import Textbooks.LinearAlgebra.Chapter05.BilinearMatrices
import Textbooks.LinearAlgebra.Chapter01.DirectSums
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FinCases

namespace LinearAlgebra.Chapter05

open scoped BigOperators Matrix

variable {K : Type*} [Field K] {m n : ℕ}

/-- Proposition: the bilinear map associated with a matrix is `XᵀAY`. -/
theorem matrixBilinear_eq_dotProduct_mulVec (A : Matrix (Fin m) (Fin n) K)
    (x : Fin m → K) (y : Fin n → K) : matrixBilinear A x y = x ⬝ᵥ (A *ᵥ y) := by
  change (∑ i, ∑ j, A i j * x i * y j) = x ⬝ᵥ (A *ᵥ y)
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Definition: the standard bilinear scalar product on a coordinate space. -/
def coordinateProduct (n : ℕ) : LinearMap.BilinForm K (Fin n → K) := matrixBilinear 1

/-- Proposition: the standard scalar product agrees with the earlier dot product. -/
theorem coordinateProduct_eq_dotProduct (x y : Fin n → K) :
    coordinateProduct n x y = Chapter01.dotProduct x y := by
  rw [coordinateProduct, matrixBilinear_eq_dotProduct_mulVec, Matrix.one_mulVec]
  rfl

/-- Proposition: the coordinate scalar product is symmetric. -/
theorem coordinateProduct_isSymm : (coordinateProduct (K := K) n).IsSymm := by
  unfold coordinateProduct
  apply LinearMap.BilinForm.isSymm_iff.mpr
  apply (matrixBilinear_isSymm_iff _).mpr
  exact Matrix.isSymm_one

/-- Proposition: the coordinate scalar product is nondegenerate. -/
theorem coordinateProduct_separatingLeft : (coordinateProduct (K := K) n).SeparatingLeft := by
  intro x hx
  ext i
  have hi := hx (Pi.single i 1)
  rw [coordinateProduct_eq_dotProduct] at hi
  simpa [Chapter01.dotProduct, Pi.single_apply] using hi

/-- Proposition: the real coordinate scalar product is positive definite. -/
theorem coordinateProduct_posDef : (coordinateProduct (K := ℝ) n).toQuadraticMap.PosDef := by
  intro x hx
  change coordinateProduct n x x > 0
  rw [coordinateProduct_eq_dotProduct]
  apply Finset.sum_pos'

  · intro i _
    exact mul_self_nonneg _

  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact ⟨i, Finset.mem_univ _, mul_self_pos.mpr hi⟩

/-- Proposition: the nonzero complex vector `(1, i)` has zero bilinear square. -/
theorem complex_isotropic_vector :
    (![(1 : ℂ), Complex.I] : Fin 2 → ℂ) ≠ 0 ∧
      coordinateProduct 2 ![(1 : ℂ), Complex.I] ![(1 : ℂ), Complex.I] = 0 := by
  constructor

  · intro h
    have he := congrFun h 0
    norm_num at he

  · rw [coordinateProduct_eq_dotProduct]
    simp [Chapter01.dotProduct, Fin.sum_univ_two, Complex.I_mul_I]

/-- Definition: the isotropic line through `(1, i)` for the complex bilinear dot product. -/
def complexIsotropicLine : Submodule ℂ (Fin 2 → ℂ) :=
  Submodule.span ℂ {![(1 : ℂ), Complex.I]}

/-- Proposition: this isotropic line equals its bilinear orthogonal space. -/
theorem complexIsotropicLine_orthogonal :
    complexIsotropicLine.orthogonalBilin (coordinateProduct 2) = complexIsotropicLine := by
  ext w
  constructor

  · intro h
    have he := h ![(1 : ℂ), Complex.I] (Submodule.mem_span_singleton_self _)
    rw [coordinateProduct_eq_dotProduct] at he
    have hz : w 0 + Complex.I * w 1 = 0 := by
      simpa [Chapter01.dotProduct, Fin.sum_univ_two] using he

    have hw : w 1 = Complex.I * w 0 := by
      have hi := congrArg (fun z : ℂ => Complex.I * z) hz
      simp only [mul_add, ← mul_assoc, Complex.I_mul_I, neg_one_mul, mul_zero] at hi
      linear_combination -hi

    apply Submodule.mem_span_singleton.mpr
    refine ⟨w 0, ?_⟩
    ext i
    fin_cases i

    · simp

    · simpa [mul_comm] using hw.symm

  · intro h z hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp h
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [complex_isotropic_vector.2, mul_zero, mul_zero]

/-- Proposition: positivity is essential for a subspace to split off its orthogonal space. -/
theorem complexIsotropicLine_not_directSum :
    ¬Chapter01.IsDirectSum complexIsotropicLine
      (complexIsotropicLine.orthogonalBilin (coordinateProduct 2)) := by
  intro h
  have hz := (Chapter01.directSum_sup_inf h).2
  have hu : ![(1 : ℂ), Complex.I] ∈ complexIsotropicLine ⊓
      complexIsotropicLine.orthogonalBilin (coordinateProduct 2) := by
    rw [complexIsotropicLine_orthogonal]
    exact ⟨Submodule.mem_span_singleton_self _, Submodule.mem_span_singleton_self _⟩

  rw [hz, Submodule.mem_bot] at hu
  exact complex_isotropic_vector.1 hu

/-- Proposition: the standard Hermitian product sums conjugated first coordinates. -/
theorem euclidean_inner (x y : EuclideanSpace ℂ (Fin n)) :
    inner ℂ x y = ∑ i, star (x i) * y i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply, mul_comm]

/-- Proposition: the standard unit vectors form an orthonormal basis. -/
theorem euclidean_basis_orthonormal (𝕜 : Type*) [RCLike 𝕜] :
    Orthonormal 𝕜 (EuclideanSpace.basisFun (Fin n) 𝕜) := by
  constructor

  · intro i
    simp only [EuclideanSpace.basisFun_apply, PiLp.norm_single, norm_one]

  · intro i j hij
    simp [EuclideanSpace.basisFun_apply, PiLp.inner_apply, hij]

/-- Proposition: the vectors `(1, 2)` and `(2, 1)` are perpendicular for a form of mixed sign. -/
theorem indefinite_perpendicular :
    matrixBilinear (Matrix.diagonal ![(1 : ℝ), -1]) ![1, 2] ![2, 1] = 0 := by
  norm_num [matrixBilinear, Matrix.diagonal_apply, Fin.sum_univ_two]

end LinearAlgebra.Chapter05
