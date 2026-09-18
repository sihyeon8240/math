import Textbooks.LinearAlgebra.Chapter01.Dimension
import Textbooks.LinearAlgebra.Chapter02.MatrixSpace

namespace LinearAlgebra.Chapter02

open scoped BigOperators Matrix
open Chapter01

variable {K : Type*} [Field K]

/-- Definition: a solution of a system of linear equations. -/
def IsSolution {m n : ℕ} (A : MatrixSpace K m n) (b : Fin m → K) (x : Fin n → K) : Prop :=
  ∀ i, ∑ j, A i j * x j = b i

/-- Proposition: the scalar equations are equivalent to the matrix equation. -/
theorem solution_iff_mulVec {m n : ℕ} (A : MatrixSpace K m n) (b : Fin m → K) (x : Fin n → K) :
    IsSolution A b x ↔ A *ᵥ x = b := Iff.symm funext_iff

/-- Proposition: matrix multiplication by a vector combines the columns. -/
theorem mulVec_eq_combination {m n : ℕ} (A : MatrixSpace K m n) (x : Fin n → K) :
    A *ᵥ x = linearCombination (column A) x := by
  funext i
  simp only [Matrix.mulVec_apply_eq_sum, linearCombination, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, column, mul_comm]

/-- Proposition: the zero vector solves every homogeneous system. -/
theorem homogeneous_zero {m n : ℕ} (A : MatrixSpace K m n) : IsSolution A 0 0 := by
  intro i
  simp only [Pi.zero_apply, MulZeroClass.mul_zero, Finset.sum_const_zero]

/-- Proposition: nontrivial homogeneous solutions are exactly column dependencies. -/
theorem nontrivial_solution_iff {m n : ℕ} (A : MatrixSpace K m n) :
    (∃ x, IsSolution A 0 x ∧ x ≠ 0) ↔ ¬LinearIndependent K (column A) := by
  simp only [solution_iff_mulVec, mulVec_eq_combination]
  exact dependent_iff (column A)

/-- Theorem: more unknowns than equations imply a nontrivial homogeneous solution. -/
theorem exists_nontrivial_solution {m n : ℕ} (A : MatrixSpace K m n) (h : m < n) :
    ∃ x, IsSolution A 0 x ∧ x ≠ 0 := by
  apply (nontrivial_solution_iff A).mpr
  intro hi

  have hc := independent_le_generating hi (standard_is_basis (K := K) m).2

  simp only [Fintype.card_fin] at hc
  omega

/-- Lemma: the standard coordinate space has its expected dimension. -/
theorem finrank_coordinates (n : ℕ) : Module.finrank K (Fin n → K) = n := by
  obtain ⟨b, _⟩ := (finiteBasis_iff _).mp (standard_is_basis (K := K) n)

  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b

/-- Theorem: a square system with independent columns has exactly one solution. -/
theorem exists_unique_solution {n : ℕ} (A : MatrixSpace K n n)
    (h : LinearIndependent K (column A)) (b : Fin n → K) : ∃! x, IsSolution A b x := by
  have hb := independent_card_finrank_is_basis h (by
    rw [Fintype.card_fin, finrank_coordinates])

  simpa only [solution_iff_mulVec, mulVec_eq_combination] using exists_unique_coordinates hb b

end LinearAlgebra.Chapter02
