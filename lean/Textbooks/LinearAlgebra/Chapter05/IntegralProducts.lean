import Textbooks.LinearAlgebra.Chapter05.HermitianProducts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.ContinuousMap.Ordered

namespace LinearAlgebra.Chapter05

open MeasureTheory

/-- Definition: integrate the pointwise product of continuous real functions. -/
noncomputable def realIntegralProduct (a b : ℝ) : LinearMap.BilinForm ℝ C(ℝ, ℝ) where
  toFun f :=
    { toFun := fun g => ∫ x in a..b, f x * g x
      map_add' := by
        intro g h
        simp only [ContinuousMap.add_apply, mul_add]
        exact intervalIntegral.integral_add
          ((f.continuous.mul g.continuous).intervalIntegrable a b)
          ((f.continuous.mul h.continuous).intervalIntegrable a b)
      map_smul' := by
        intro c g
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        have he (x : ℝ) : f x * (c * g x) = c * (f x * g x) := by
          ring
        simp_rw [he]
        exact intervalIntegral.integral_const_mul _ _ }
  map_add' := by
    intro f h
    apply LinearMap.ext
    intro g
    change (∫ x in a..b, (f x + h x) * g x) =
      (∫ x in a..b, f x * g x) + ∫ x in a..b, h x * g x
    simp_rw [add_mul]
    exact intervalIntegral.integral_add
      ((f.continuous.mul g.continuous).intervalIntegrable a b)
      ((h.continuous.mul g.continuous).intervalIntegrable a b)
  map_smul' := by
    intro c f
    apply LinearMap.ext
    intro g
    change (∫ x in a..b, (c * f x) * g x) = c * ∫ x in a..b, f x * g x
    simp_rw [mul_assoc]
    exact intervalIntegral.integral_const_mul _ _

/-- Proposition: the real integral product is symmetric. -/
theorem realIntegralProduct_isSymm (a b : ℝ) : (realIntegralProduct a b).IsSymm := by
  constructor
  intro f g
  change (∫ x in a..b, f x * g x) = ∫ x in a..b, g x * f x
  simp only [mul_comm]

/-- Lemma: a nonzero continuous function has positive squared integral on a nontrivial interval.
Integral positivity is an accepted prerequisite for this example. -/
theorem integral_square_pos {a b : ℝ} (hab : a < b) (f : C(ℝ, ℝ))
    (hf : ∃ x ∈ Set.Icc a b, f x ≠ 0) : 0 < ∫ x in a..b, f x * f x := by
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hab continuousOn_const (f.continuous.mul f.continuous).continuousOn
    (fun x _ => mul_self_nonneg (f x)) ?_

  · simpa only [intervalIntegral.integral_zero, Pi.mul_apply] using h

  · obtain ⟨x, hx, hfx⟩ := hf
    exact ⟨x, hx, mul_self_pos.mpr hfx⟩

/-- Definition: extend a function on a closed interval by its endpoint values. -/
noncomputable def intervalExtension {a b : ℝ} (hab : a ≤ b) : C(Set.Icc a b, ℝ) →ₗ[ℝ] C(ℝ, ℝ) where
  toFun := ContinuousMap.IccExtend hab
  map_add' := by
    intro f g
    rfl
  map_smul' := by
    intro c f
    rfl

/-- Definition: the scalar product on continuous functions on a closed interval. -/
noncomputable def intervalProduct {a b : ℝ} (hab : a ≤ b) :
    LinearMap.BilinForm ℝ C(Set.Icc a b, ℝ) :=
  (realIntegralProduct a b).compl₁₂ (intervalExtension hab) (intervalExtension hab)

/-- Proposition: the continuous-function product on a nontrivial interval is positive definite. -/
theorem intervalProduct_posDef {a b : ℝ} (hab : a < b) :
    (intervalProduct hab.le).toQuadraticMap.PosDef := by
  intro f hf
  apply integral_square_pos hab (ContinuousMap.IccExtend hab.le f)

  have hn : ∃ x, f x ≠ 0 := by
    by_contra hn
    apply hf
    ext x
    change f x = 0
    exact not_not.mp (not_exists.mp hn x)

  obtain ⟨x, hx⟩ := hn
  refine ⟨x, x.property, ?_⟩
  simpa only [ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem hab.le f x.property] using hx

/-- Proposition: the integral scalar product on continuous functions on `[0,1]` is nondegenerate. -/
theorem unitIntervalProduct_separatingLeft :
    (intervalProduct (a := 0) (b := 1) (by norm_num)).SeparatingLeft :=
  separatingLeft_of_posDef _ (intervalProduct_posDef (by norm_num))

end LinearAlgebra.Chapter05
