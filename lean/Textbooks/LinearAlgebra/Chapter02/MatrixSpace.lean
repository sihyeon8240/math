import Textbooks.LinearAlgebra.Chapter01.Dimension
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.Symmetric

namespace LinearAlgebra.Chapter02

open scoped BigOperators
open Chapter01

variable {K : Type*} [Field K]

/-- Definition: the space of matrices with `m` rows and `n` columns. -/
abbrev MatrixSpace (K : Type*) (m n : ℕ) := Matrix (Fin m) (Fin n) K

/-- Definition: a row of a matrix. -/
def row {m n : ℕ} (A : MatrixSpace K m n) (i : Fin m) : Fin n → K := A i

/-- Definition: a column of a matrix. -/
def column {m n : ℕ} (A : MatrixSpace K m n) (j : Fin n) : Fin m → K := fun i => A i j

/-- Definition: a matrix supported on a single entry. -/
def matrixUnit {m n : ℕ} (p : Fin m × Fin n) : MatrixSpace K m n :=
  Matrix.of fun i j => if p = (i, j) then 1 else 0

/-- Proposition: matrix addition and scalar multiplication act entrywise. -/
theorem matrix_operations {m n : ℕ} (A B : MatrixSpace K m n) (c : K) (i : Fin m) (j : Fin n) :
    (A + B) i j = A i j + B i j ∧ (c • A) i j = c * A i j ∧
    (0 : MatrixSpace K m n) i j = 0 ∧ (-A) i j = -A i j := ⟨rfl, rfl, rfl, rfl⟩

omit [Field K] in
/-- Proposition: transposition interchanges rows and columns. -/
theorem transpose_apply {m n : ℕ} (A : MatrixSpace K m n) (i : Fin m) (j : Fin n) :
    A.transpose j i = A i j := rfl

/-- Proposition: every diagonal matrix is symmetric. -/
theorem diagonal_is_symmetric {n : ℕ} {A : MatrixSpace K n n} (h : A.IsDiag) : A.IsSymm := by
  ext i j
  by_cases hij : i = j
  · subst j; rfl
  · exact (h (fun hji => hij hji.symm)).trans (h hij).symm

/-- Lemma: coefficients of matrix units are the entries of their sum. -/
theorem combination_matrixUnit {m n : ℕ} (a : Fin m × Fin n → K) (i : Fin m) (j : Fin n) :
    linearCombination (matrixUnit (K := K)) a i j = a (i, j) := by
  simp [linearCombination, matrixUnit, Matrix.sum_apply]

/-- Theorem: the matrix units form a basis. -/
theorem matrixUnit_is_basis (m n : ℕ) :
    IsFiniteBasis (K := K) (matrixUnit (K := K) (m := m) (n := n)) := by
  refine ⟨Fintype.linearIndependent_iff.mpr ?_, ?_⟩
  · intro a ha p
    change linearCombination (matrixUnit (K := K)) a = 0 at ha
    have he := congrArg (fun A : MatrixSpace K m n => A p.1 p.2) ha
    simpa only [combination_matrixUnit, Matrix.zero_apply] using he
  · intro A
    refine ⟨fun p => A p.1 p.2, ?_⟩
    ext i j
    exact combination_matrixUnit _ i j

/-- Theorem: the space of `m` by `n` matrices has dimension `m*n`. -/
theorem finrank_matrixSpace (m n : ℕ) : Module.finrank K (MatrixSpace K m n) = m * n := by
  obtain ⟨b, _⟩ := (finiteBasis_iff _).mp (matrixUnit_is_basis (K := K) m n)
  simpa only [Fintype.card_prod, Fintype.card_fin] using Module.finrank_eq_card_basis b

end LinearAlgebra.Chapter02
