import Textbooks.LinearAlgebra.Chapter04.MatrixMaps

/-!
Matrices relative to finite ordered bases.
`Basis.equivFun` is the coordinate map and `LinearMap.toMatrix b c f` has
source basis `b` and target basis `c`. Only its entry formula is used from
Mathlib; the representation, uniqueness, and isomorphism proofs are local.
-/

namespace LinearAlgebra.Chapter04

open scoped BigOperators Matrix

variable {K V W U : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup U] [Module K U] {n m p : ℕ}

/-- Proposition: a matrix column consists of the coordinates of a basis image. -/
theorem toMatrix_apply (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K W)
    (f : V →ₗ[K] W) (i : Fin m) (j : Fin n) :
    LinearMap.toMatrix b c f i j = c.repr (f (b j)) i :=
  LinearMap.toMatrix_apply b c f i j

/-- Theorem: the representing matrix carries source coordinates to target coordinates.
This proves `LinearMap.toMatrix_mulVec_repr` by expanding a finite basis sum. -/
theorem toMatrix_mulVec_repr (b : Module.Basis (Fin n) K V)
    (c : Module.Basis (Fin m) K W) (f : V →ₗ[K] W) (v : V) :
    LinearMap.toMatrix b c f *ᵥ b.repr v = c.repr (f v) := by
  have h : f v = ∑ j, b.repr v j • f (b j) := by
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    simp only [map_smul]

  funext i
  rw [h]
  simp only [Matrix.mulVec, dotProduct, toMatrix_apply, map_sum, map_smul,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, mul_comm]

/-- Theorem: the coordinate identity determines the matrix uniquely. -/
theorem exists_unique_toMatrix (b : Module.Basis (Fin n) K V)
    (c : Module.Basis (Fin m) K W) (f : V →ₗ[K] W) :
    ∃! A : Matrix (Fin m) (Fin n) K, ∀ v, A *ᵥ b.repr v = c.repr (f v) := by
  refine ⟨LinearMap.toMatrix b c f, toMatrix_mulVec_repr b c f, ?_⟩
  intro A h
  ext i j

  have hj := h (b j)
  simpa [Module.Basis.repr_self, Matrix.mulVec, dotProduct, Finsupp.single_apply,
    toMatrix_apply, eq_comm] using congrFun hj i

/-- Proposition: in standard bases, the general matrix is the coordinate-space matrix. -/
theorem toMatrix_standard (f : (Fin n → K) →ₗ[K] (Fin m → K)) :
    LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin m)) f =
      LinearMap.toMatrix' f := by
  ext i j
  rw [toMatrix_apply, toMatrix'_apply, Pi.basisFun_repr, Pi.basisFun_apply]

/-- Proposition: prescribed coefficients of basis images are the matrix entries. -/
theorem toMatrix_eq_of_basis_images (b : Module.Basis (Fin n) K V)
    (c : Module.Basis (Fin m) K W) (f : V →ₗ[K] W) (A : Matrix (Fin m) (Fin n) K)
    (h : ∀ j, f (b j) = ∑ i, A i j • c i) : LinearMap.toMatrix b c f = A := by
  ext i j
  rw [toMatrix_apply, h j]

  have hc := c.equivFun.apply_symm_apply (fun i => A i j)
  rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_apply] at hc
  exact congrFun hc i

/-- Proposition: taking matrices preserves addition. -/
theorem toMatrix_add (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K W)
    (f g : V →ₗ[K] W) :
    LinearMap.toMatrix b c (f + g) = LinearMap.toMatrix b c f + LinearMap.toMatrix b c g := by
  ext i j
  simp only [toMatrix_apply, LinearMap.add_apply, map_add, Finsupp.add_apply, Matrix.add_apply]

/-- Proposition: taking matrices preserves scalar multiplication. -/
theorem toMatrix_smul (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K W)
    (a : K) (f : V →ₗ[K] W) :
    LinearMap.toMatrix b c (a • f) = a • LinearMap.toMatrix b c f := by
  ext i j
  simp only [toMatrix_apply, LinearMap.smul_apply, map_smul, Finsupp.smul_apply,
    Matrix.smul_apply]

/-- Theorem: taking matrices is injective, since coordinates determine each image. -/
theorem toMatrix_injective (b : Module.Basis (Fin n) K V)
    (c : Module.Basis (Fin m) K W) :
    Function.Injective (fun f : V →ₗ[K] W => LinearMap.toMatrix b c f) := by
  intro f g h
  dsimp only at h

  apply LinearMap.ext
  intro v
  apply c.repr.injective
  apply DFunLike.coe_injective
  rw [← toMatrix_mulVec_repr b c f, ← toMatrix_mulVec_repr b c g, h]

/-- Definition: reconstruct a map by applying a matrix between the two coordinate maps. -/
noncomputable def mapOfMatrix (b : Module.Basis (Fin n) K V)
    (c : Module.Basis (Fin m) K W) (A : Matrix (Fin m) (Fin n) K) : V →ₗ[K] W :=
  c.equivFun.symm.toLinearMap.comp (A.mulVecLin.comp b.equivFun.toLinearMap)

/-- Proposition: reconstruction realizes the prescribed matrix. -/
theorem toMatrix_mapOfMatrix (b : Module.Basis (Fin n) K V)
    (c : Module.Basis (Fin m) K W) (A : Matrix (Fin m) (Fin n) K) :
    LinearMap.toMatrix b c (mapOfMatrix b c A) = A := by
  apply Eq.symm
  exact (exists_unique_toMatrix b c (mapOfMatrix b c A)).unique (by
    intro v
    change A *ᵥ b.repr v = c.equivFun (c.equivFun.symm (A *ᵥ b.equivFun v))
    rw [c.equivFun.apply_symm_apply, Module.Basis.equivFun_apply])
    (toMatrix_mulVec_repr b c _)

/-- Theorem: taking matrices is surjective by coordinate reconstruction. -/
theorem toMatrix_surjective (b : Module.Basis (Fin n) K V)
    (c : Module.Basis (Fin m) K W) :
    Function.Surjective (fun f : V →ₗ[K] W => LinearMap.toMatrix b c f) := by
  intro A
  exact ⟨mapOfMatrix b c A, toMatrix_mapOfMatrix b c A⟩

/-- Definition: the locally verified linear isomorphism from maps to matrices.
Its forward map is exactly Mathlib's `LinearMap.toMatrix`. -/
noncomputable def matrixEquiv (b : Module.Basis (Fin n) K V)
    (c : Module.Basis (Fin m) K W) : (V →ₗ[K] W) ≃ₗ[K] Matrix (Fin m) (Fin n) K where
  toFun := LinearMap.toMatrix b c
  invFun := mapOfMatrix b c
  left_inv _f := toMatrix_injective b c (toMatrix_mapOfMatrix b c _)
  right_inv := toMatrix_mapOfMatrix b c
  map_add' := toMatrix_add b c
  map_smul' := toMatrix_smul b c

/-- Corollary: the space of linear maps has dimension the product of the dimensions. -/
theorem finrank_linearMap (b : Module.Basis (Fin n) K V)
    (c : Module.Basis (Fin m) K W) : Module.finrank K (V →ₗ[K] W) = m * n := by
  have hd := Chapter03.finrank_eq_of_bijective (matrixEquiv b c).symm.toLinearMap
    (matrixEquiv b c).symm.bijective

  exact hd.symm.trans (Chapter02.finrank_matrixSpace m n)

/-- Corollary: the dimension formula depends only on the dimensions of the two spaces. -/
theorem finrank_linearMap_eq_mul [Module.Finite K V] [Module.Finite K W] :
    Module.finrank K (V →ₗ[K] W) = Module.finrank K W * Module.finrank K V := by
  obtain ⟨e⟩ := Chapter03.nonempty_coordinate_equiv (K := K) (V := V)
  obtain ⟨f⟩ := Chapter03.nonempty_coordinate_equiv (K := K) (V := W)

  exact finrank_linearMap ((Pi.basisFun K _).map e) ((Pi.basisFun K _).map f)

/-- Theorem: the matrix of a composite is the product in composition order. -/
theorem toMatrix_comp (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K W)
    (d : Module.Basis (Fin p) K U) (g : W →ₗ[K] U) (f : V →ₗ[K] W) :
    LinearMap.toMatrix b d (g.comp f) = LinearMap.toMatrix c d g * LinearMap.toMatrix b c f := by
  ext i j
  have h := congrFun (toMatrix_mulVec_repr c d g (f (b j))) i
  simpa only [toMatrix_apply, LinearMap.comp_apply, Matrix.mul_apply,
    Matrix.mulVec, dotProduct] using h.symm

/-- Proposition: the identity map in a single basis has identity matrix. -/
theorem toMatrix_id (b : Module.Basis (Fin n) K V) :
    LinearMap.toMatrix b b (LinearMap.id : V →ₗ[K] V) = 1 := by
  ext i j
  simp only [toMatrix_apply, LinearMap.id_apply, Module.Basis.repr_self_apply,
    Matrix.one_apply, eq_comm]

end LinearAlgebra.Chapter04
