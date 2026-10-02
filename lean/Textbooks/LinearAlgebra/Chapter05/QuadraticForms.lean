import Textbooks.LinearAlgebra.Chapter05.BilinearMatrices
import Textbooks.LinearAlgebra.Chapter05.OrthogonalBases

namespace LinearAlgebra.Chapter05

open Module
open scoped BigOperators

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Lemma: the square of an orthogonal linear combination is a diagonal sum. -/
theorem bilin_sum_self {ι : Type*} [Fintype ι] (B : LinearMap.BilinForm K V)
    (u : ι → V) (hu : B.IsOrthoᵢ u) (a : ι → K) :
    B (∑ i, a i • u i) (∑ i, a i • u i) = ∑ i, B (u i) (u i) * (a i) ^ 2 := by
  classical
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, Finset.sum_eq_single i]

  · ring

  · intro j _ hji
    rw [hu hji, mul_zero, mul_zero]

  · intro hn
    exact (hn (Finset.mem_univ i)).elim

/-- Theorem: an orthogonal basis expresses the quadratic form as a sum of weighted squares. -/
theorem quadraticForm_eq_sum {ι : Type*} [Fintype ι] (B : LinearMap.BilinForm K V)
    (b : Basis ι K V) (hb : B.IsOrthoᵢ b) (v : V) :
    B.toQuadraticMap v = ∑ i, B (b i) (b i) * (b.repr v i) ^ 2 := by
  change B v v = _
  conv_lhs => rw [← b.sum_repr v]
  exact bilin_sum_self B b hb (fun i => b.repr v i)

/-- Theorem: in characteristic not two, the quadratic form determines the scalar product. -/
theorem toQuadraticMap_injective (h2 : (2 : K) ≠ 0)
    (B C : LinearMap.BilinForm K V) (hB : B.IsSymm) (hC : C.IsSymm)
    (h : B.toQuadraticMap = C.toQuadraticMap) : B = C := by
  have he (v : V) : B v v = C v v := congrArg (fun Q => Q v) h

  ext v w
  rw [polarization B hB h2, polarization C hC h2, he, he, he]

end LinearAlgebra.Chapter05
