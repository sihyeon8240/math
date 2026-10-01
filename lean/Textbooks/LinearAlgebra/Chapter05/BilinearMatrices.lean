import Textbooks.LinearAlgebra.Chapter05.ScalarProducts
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace LinearAlgebra.Chapter05

open scoped BigOperators Matrix

variable {K : Type*} [Field K] {m n : ℕ}

/-- Definition: the matrix of a bilinear map consists of its values on unit vectors. -/
def bilinearMatrix (g : (Fin m → K) →ₗ[K] (Fin n → K) →ₗ[K] K) :
    Matrix (Fin m) (Fin n) K :=
  fun i j => g (Pi.single i 1) (Pi.single j 1)

/-- Definition: the bilinear map `XᵀAY`, bundled in each argument. -/
def matrixBilinear (A : Matrix (Fin m) (Fin n) K) :
    (Fin m → K) →ₗ[K] (Fin n → K) →ₗ[K] K where
  toFun x :=
    { toFun := fun y => ∑ i, ∑ j, A i j * x i * y j
      map_add' := by
        intro y z
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c y
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        congr 1
        funext i
        congr 1
        funext j
        ring }
  map_add' := by
    intro x z
    apply LinearMap.ext
    intro y
    change (∑ i, ∑ j, A i j * (x i + z i) * y j) =
      (∑ i, ∑ j, A i j * x i * y j) + ∑ i, ∑ j, A i j * z i * y j
    simp only [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    apply LinearMap.ext
    intro y
    change (∑ i, ∑ j, A i j * (c * x i) * y j) =
      c * ∑ i, ∑ j, A i j * x i * y j
    simp only [Finset.mul_sum]
    congr 1
    funext i
    congr 1
    funext j
    ring

/-- Lemma: every coordinate vector is its unit-vector expansion. -/
theorem sum_single (x : Fin n → K) : ∑ i, x i • Pi.single i (1 : K) = x := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

/-- Theorem: unit-vector values reconstruct every bilinear map. -/
theorem matrixBilinear_bilinearMatrix
    (g : (Fin m → K) →ₗ[K] (Fin n → K) →ₗ[K] K) :
    matrixBilinear (bilinearMatrix g) = g := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change (∑ i, ∑ j, g (Pi.single i 1) (Pi.single j 1) * x i * y j) = g x y

  conv_rhs => rw [← sum_single x, ← sum_single y]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Proposition: recovering the unit-vector values recovers the matrix. -/
theorem bilinearMatrix_matrixBilinear (A : Matrix (Fin m) (Fin n) K) :
    bilinearMatrix (matrixBilinear A) = A := by
  ext i j
  simp [bilinearMatrix, matrixBilinear, Pi.single_apply]

/-- Theorem: a bilinear map is represented by exactly one matrix. -/
theorem exists_unique_bilinearMatrix
    (g : (Fin m → K) →ₗ[K] (Fin n → K) →ₗ[K] K) :
    ∃! A, matrixBilinear A = g := by
  refine ⟨bilinearMatrix g, matrixBilinear_bilinearMatrix g, ?_⟩

  intro A hA
  rw [← bilinearMatrix_matrixBilinear A, hA]

/-- Definition: the linear isomorphism between matrices and bilinear maps. -/
def matrixBilinearEquiv :
    Matrix (Fin m) (Fin n) K ≃ₗ[K] ((Fin m → K) →ₗ[K] (Fin n → K) →ₗ[K] K) where
  toFun := matrixBilinear
  invFun := bilinearMatrix
  left_inv := bilinearMatrix_matrixBilinear
  right_inv := matrixBilinear_bilinearMatrix
  map_add' := by
    intro A C
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simp [matrixBilinear, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c A
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change (∑ i, ∑ j, (c * A i j) * x i * y j) =
      c * ∑ i, ∑ j, A i j * x i * y j
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Proposition: transposition interchanges the arguments of the bilinear map. -/
theorem matrixBilinear_transpose (A : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    matrixBilinear Aᵀ x y = matrixBilinear A y x := by
  change (∑ i, ∑ j, A j i * x i * y j) = ∑ i, ∑ j, A i j * y i * x j
  rw [Finset.sum_comm]

  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Theorem: symmetric matrices are exactly symmetric bilinear forms. -/
theorem matrixBilinear_isSymm_iff (A : Matrix (Fin n) (Fin n) K) :
    (matrixBilinear A).IsSymm ↔ A.IsSymm := by
  constructor

  · intro h
    ext i j
    have hi := h.eq (Pi.single j 1) (Pi.single i 1)
    have hr := congrFun (congrFun (bilinearMatrix_matrixBilinear A) i) j
    have hs := congrFun (congrFun (bilinearMatrix_matrixBilinear A) j) i

    exact hs.symm.trans (hi.trans hr)

  · intro h
    constructor
    intro x y
    change matrixBilinear A x y = matrixBilinear A y x
    rw [← matrixBilinear_transpose, h]

/-- Theorem: every scalar product on a coordinate space has a unique symmetric matrix. -/
theorem exists_unique_symmetric_matrix (B : LinearMap.BilinForm K (Fin n → K))
    (hB : B.IsSymm) : ∃! A : Matrix (Fin n) (Fin n) K, A.IsSymm ∧ matrixBilinear A = B := by
  obtain ⟨A, hA, hunique⟩ := exists_unique_bilinearMatrix B

  have hs : A.IsSymm := by
    rw [← matrixBilinear_isSymm_iff, hA]
    exact LinearMap.BilinForm.isSymm_iff.mp hB

  exact ⟨A, ⟨hs, hA⟩, fun C hC => hunique C hC.2⟩

/-- Proposition: a diagonal matrix gives a weighted sum of squares. -/
theorem matrixBilinear_diagonal (d : Fin n → K) (x : Fin n → K) :
    matrixBilinear (Matrix.diagonal d) x x = ∑ i, d i * (x i) ^ 2 := by
  simp [matrixBilinear, Matrix.diagonal_apply, pow_two, mul_assoc]

end LinearAlgebra.Chapter05
