import Textbooks.LinearAlgebra.Chapter02.MatrixSpace

namespace LinearAlgebra.Chapter02

open scoped BigOperators

variable {K : Type*} [Field K]

/-- Proposition: a product entry is the dot product of a row and a column. -/
theorem mul_apply {m n p : ℕ} (A : MatrixSpace K m n) (B : MatrixSpace K n p)
    (i : Fin m) (k : Fin p) : (A * B) i k = ∑ j, A i j * B j k := rfl

/-- Theorem: multiplication distributes over addition on the right. -/
theorem mul_add {m n p : ℕ} (A : MatrixSpace K m n) (B C : MatrixSpace K n p) :
    A * (B + C) = A * B + A * C := by
  ext i k
  simp only [mul_apply, Matrix.add_apply, _root_.mul_add, Finset.sum_add_distrib]

/-- Theorem: multiplication distributes over addition on the left. -/
theorem add_mul {m n p : ℕ} (A B : MatrixSpace K m n) (C : MatrixSpace K n p) :
    (A + B) * C = A * C + B * C := by
  ext i k
  simp only [mul_apply, Matrix.add_apply, _root_.add_mul, Finset.sum_add_distrib]

/-- Theorem: scalars commute with matrix multiplication. -/
theorem mul_smul {m n p : ℕ} (A : MatrixSpace K m n) (B : MatrixSpace K n p) (c : K) :
    A * (c • B) = c • (A * B) := by
  ext i k
  simp only [mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_left_comm _ _ _

/-- Theorem: matrix multiplication is associative. -/
theorem mul_assoc {m n p q : ℕ} (A : MatrixSpace K m n) (B : MatrixSpace K n p)
    (C : MatrixSpace K p q) : (A * B) * C = A * (B * C) := by
  ext i l
  simp only [mul_apply, Finset.sum_mul, Finset.mul_sum, _root_.mul_assoc]
  exact Finset.sum_comm

/-- Theorem: transposition reverses the order of a product. -/
theorem transpose_mul {m n p : ℕ} (A : MatrixSpace K m n) (B : MatrixSpace K n p) :
    (A * B).transpose = B.transpose * A.transpose := by
  ext i k
  simp only [Matrix.transpose_apply, mul_apply, mul_comm]

/-- Proposition: the identity matrix is a left identity. -/
theorem one_mul {m n : ℕ} (A : MatrixSpace K m n) : (1 : MatrixSpace K m m) * A = A := by
  ext i j
  simp only [mul_apply, Matrix.one_apply, ite_mul, _root_.one_mul,
    MulZeroClass.zero_mul]
  simp

/-- Proposition: the identity matrix is a right identity. -/
theorem mul_one {m n : ℕ} (A : MatrixSpace K m n) : A * (1 : MatrixSpace K n n) = A := by
  ext i j
  simp only [mul_apply, Matrix.one_apply, mul_ite, _root_.mul_one,
    MulZeroClass.mul_zero]
  simp

/-- Proposition: a product with a zero matrix is zero. -/
theorem mul_zero {m n p : ℕ} (A : MatrixSpace K m n) : A * (0 : MatrixSpace K n p) = 0 := by
  ext i j
  simp only [mul_apply, Matrix.zero_apply, MulZeroClass.mul_zero, Finset.sum_const_zero]

/-- Definition: a square matrix is nonsingular if it has a two-sided inverse. -/
def IsNonsingular {n : ℕ} (A : MatrixSpace K n n) : Prop := ∃ B, A * B = 1 ∧ B * A = 1

/-- Theorem: a left inverse and a right inverse coincide. -/
theorem inverse_unique {n : ℕ} {A B C : MatrixSpace K n n}
    (hB : B * A = 1) (hC : A * C = 1) : B = C := by
  calc
    B = B * 1 := (mul_one B).symm
    _ = B * (A * C) := by
      rw [hC]
    _ = (B * A) * C := (mul_assoc B A C).symm
    _ = C := by
      rw [hB, one_mul]

/-- Definition: the inverse of a nonsingular matrix. -/
noncomputable def inverse {n : ℕ} {A : MatrixSpace K n n} (h : IsNonsingular A) :
    MatrixSpace K n n := Classical.choose h

/-- Proposition: the chosen inverse satisfies both inverse equations. -/
theorem inverse_spec {n : ℕ} {A : MatrixSpace K n n} (h : IsNonsingular A) :
    A * inverse h = 1 ∧ inverse h * A = 1 := Classical.choose_spec h

end LinearAlgebra.Chapter02
