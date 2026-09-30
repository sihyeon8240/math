import Textbooks.LinearAlgebra.Chapter02.Multiplication
import Textbooks.LinearAlgebra.Chapter03.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
Matrix maps and their unique matrices.
Use Mathlib's `Matrix`, `mulVecLin`, and `LinearMap.toMatrix'` interfaces.
The proofs below recover matrices from standard vectors and extend by finite
linear combinations; they do not use Mathlib's matrix/map equivalence theorems.
-/

namespace LinearAlgebra.Chapter04

open scoped BigOperators Matrix
open Chapter01

variable {K : Type*} [Field K] {m n p : ℕ}

/-- Lemma: applying a matrix map to a standard vector extracts a column. -/
theorem mulVecLin_single (A : Matrix (Fin m) (Fin n) K) (j : Fin n) :
    A.mulVecLin (Pi.single j 1) = fun i => A i j := by
  ext i
  change ∑ k, A i k * (Pi.single j 1 : Fin n → K) k = A i j
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- Theorem: equal matrix maps have equal matrices. -/
theorem mulVecLin_injective :
    Function.Injective (fun A : Matrix (Fin m) (Fin n) K => A.mulVecLin) := by
  intro A B h
  ext i j

  have hc := congrArg (fun f : (Fin n → K) →ₗ[K] (Fin m → K) => f (Pi.single j 1)) h
  rw [mulVecLin_single, mulVecLin_single] at hc
  exact congrFun hc i

/-- Proposition: homogeneous solutions are exactly the kernel of the matrix map. -/
theorem solution_iff_mem_ker (A : Matrix (Fin m) (Fin n) K) (x : Fin n → K) :
    Chapter02.IsSolution A 0 x ↔ x ∈ LinearMap.ker A.mulVecLin := by
  rw [Chapter02.solution_iff_mulVec]
  rfl

/-- Proposition: the associated matrix has the images of standard vectors as columns. -/
theorem toMatrix'_apply (f : (Fin n → K) →ₗ[K] (Fin m → K)) (i : Fin m) (j : Fin n) :
    LinearMap.toMatrix' f i j = f (Pi.single j 1) i := rfl

/-- Theorem: the matrix constructed from the columns represents the given map.
This independently proves `Matrix.toLin'_toMatrix'` in finite coordinate spaces. -/
theorem mulVecLin_toMatrix' (f : (Fin n → K) →ₗ[K] (Fin m → K)) :
    (LinearMap.toMatrix' f).mulVecLin = f := by
  apply Chapter03.maps_eq_on_generators (standard_is_basis n).2
  intro j

  have hs : standardVector (K := K) j = Pi.single j 1 := by
    ext k
    simp [standardVector, Pi.single_apply, eq_comm]

  rw [hs, mulVecLin_single]
  rfl

/-- Theorem: every linear map between coordinate spaces has a unique matrix. -/
theorem exists_unique_matrix (f : (Fin n → K) →ₗ[K] (Fin m → K)) :
    ∃! A : Matrix (Fin m) (Fin n) K, A.mulVecLin = f := by
  refine ⟨LinearMap.toMatrix' f, mulVecLin_toMatrix' f, ?_⟩
  intro A h
  exact mulVecLin_injective (h.trans (mulVecLin_toMatrix' f).symm)

/-- Lemma: the identity matrix represents the identity map. -/
theorem mulVecLin_one : (1 : Matrix (Fin n) (Fin n) K).mulVecLin = LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext i
  change ∑ j, (if i = j then (1 : K) else 0) * x j = x i
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- Lemma: matrix multiplication represents composition, by exchanging finite sums. -/
theorem mulVecLin_mul (A : Matrix (Fin p) (Fin m) K) (B : Matrix (Fin m) (Fin n) K) :
    (A * B).mulVecLin = A.mulVecLin.comp B.mulVecLin := by
  apply LinearMap.ext
  intro x
  funext i
  simp only [Matrix.mulVecLin_apply, LinearMap.comp_apply, Matrix.mulVec,
    _root_.dotProduct, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- Theorem: a square matrix is invertible exactly when its columns are independent.
The inverse is constructed from the earlier unique-solution theorem, without determinants. -/
theorem isNonsingular_iff_linearIndependent (A : Matrix (Fin n) (Fin n) K) :
    Chapter02.IsNonsingular A ↔ LinearIndependent K (Chapter02.column A) := by
  constructor

  · rintro ⟨B, hAB, hBA⟩
    have hinj : Function.Injective A.mulVecLin := by
      intro x y h

      have hx := congrArg (fun f : (Fin n → K) →ₗ[K] (Fin n → K) => f x)
        (mulVecLin_mul B A)
      have hy := congrArg (fun f : (Fin n → K) →ₗ[K] (Fin n → K) => f y)
        (mulVecLin_mul B A)

      rw [hBA, mulVecLin_one] at hx hy
      exact hx.trans ((congrArg B.mulVecLin h).trans hy.symm)

    by_contra hi
    obtain ⟨x, hx, hne⟩ := (Chapter02.nontrivial_solution_iff A).mpr hi
    apply hne
    apply hinj
    exact ((Chapter02.solution_iff_mulVec A 0 x).mp hx).trans
      (A.mulVecLin.map_zero).symm

  · intro h
    have hb : Function.Bijective A.mulVecLin := by
      constructor

      · intro x y hxy
        obtain ⟨z, _, hz⟩ := Chapter02.exists_unique_solution A h (A.mulVecLin x)
        exact (hz x ((Chapter02.solution_iff_mulVec _ _ _).mpr rfl)).trans
          (hz y ((Chapter02.solution_iff_mulVec _ _ _).mpr hxy.symm)).symm

      · intro y
        obtain ⟨x, hx, _⟩ := Chapter02.exists_unique_solution A h y
        exact ⟨x, (Chapter02.solution_iff_mulVec _ _ _).mp hx⟩

    obtain ⟨g, hgf, hfg⟩ := Chapter03.exists_inverse_linear A.mulVecLin
      ((Chapter03.ker_eq_bot_iff_injective _).mpr hb.1) hb.2
    refine ⟨LinearMap.toMatrix' g, ?_, ?_⟩

    · apply mulVecLin_injective
      dsimp only
      rw [mulVecLin_mul, mulVecLin_toMatrix', mulVecLin_one]
      exact LinearMap.ext hfg

    · apply mulVecLin_injective
      dsimp only
      rw [mulVecLin_mul, mulVecLin_toMatrix', mulVecLin_one]
      exact LinearMap.ext hgf

end LinearAlgebra.Chapter04
