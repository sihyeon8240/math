import Textbooks.MathematicalAnalysis.Chapter03.ContinuousFunctions
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace MathematicalAnalysis.Chapter04

open Set Metric Filter
open scoped Topology
open MathematicalAnalysis.Chapter02 MathematicalAnalysis.Chapter03

/-- Definition: a real derivative is the punctured limit of difference quotients. -/
theorem hasDerivAt_iff_limit (f : ℝ → ℝ) (d a : ℝ) :
    HasDerivAt f d a ↔
      Tendsto (fun x => (f x - f a) / (x - a)) (𝓝[≠] a) (𝓝 d) := by
  have hs : slope f a = fun x => (f x - f a) / (x - a) :=
    funext (slope_def_field f a)
  rw [hasDerivAt_iff_tendsto_slope, hs]

/-- Definition: differentiability means existence of a finite real derivative. -/
theorem differentiableAt_iff_limit (f : ℝ → ℝ) (a : ℝ) :
    DifferentiableAt ℝ f a ↔ ∃ d : ℝ,
      Tendsto (fun x => (f x - f a) / (x - a)) (𝓝[≠] a) (𝓝 d) := by
  constructor
  · intro h
    exact ⟨deriv f a, (hasDerivAt_iff_limit f _ a).mp h.hasDerivAt⟩
  · rintro ⟨d, hd⟩
    exact ((hasDerivAt_iff_limit f d a).mpr hd).differentiableAt

/-- Lemma: the derivative limit has the epsilon-delta difference-quotient form. -/
theorem hasDerivAt_iff_epsilon (f : ℝ → ℝ) (d a : ℝ) :
    HasDerivAt f d a ↔ ∀ ε > 0, ∃ δ > 0, ∀ x,
      0 < |x - a| → |x - a| < δ → |(f x - f a) / (x - a) - d| < ε := by
  rw [hasDerivAt_iff_limit, punctured_limit_iff]
  simp only [Real.dist_eq]

/-- Definition: the difference quotient extended at its base point by the derivative value. -/
noncomputable def derivativeSlope (f : ℝ → ℝ) (d a x : ℝ) : ℝ :=
  if x = a then d else (f x - f a) / (x - a)

/-- Lemma: the extended difference quotient is continuous at its base point. -/
theorem derivativeSlope_continuousAt (f : ℝ → ℝ) (d a : ℝ) (hf : HasDerivAt f d a) :
    ContinuousAt (derivativeSlope f d a) a := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := (hasDerivAt_iff_epsilon f d a).mp hf ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  by_cases hxa : x = a
  · subst x
    simpa only [dist_self] using hε
  · simpa only [derivativeSlope, hxa, ↓reduceIte, Real.dist_eq] using
      hd x (abs_pos.mpr (sub_ne_zero.mpr hxa)) hx

/-- Theorem: a differentiable real function is continuous at the same point. -/
theorem continuousAt_of_hasDerivAt (f : ℝ → ℝ) (d a : ℝ) (hf : HasDerivAt f d a) :
    ContinuousAt f a := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨r, hr, hq⟩ := (hasDerivAt_iff_epsilon f d a).mp hf 1 zero_lt_one
  have hp : 0 < |d| + 1 := by positivity
  refine ⟨min r (ε / (|d| + 1)), lt_min hr (div_pos hε hp), ?_⟩
  intro x hx
  by_cases hxa : x = a
  · subst x
    simpa only [dist_self] using hε
  · have hn : x - a ≠ 0 := sub_ne_zero.mpr hxa
    have hnear : |x - a| < r := hx.trans_le (min_le_left _ _)
    have hsmall : |x - a| * (|d| + 1) < ε :=
      (lt_div_iff₀ hp).mp (hx.trans_le (min_le_right _ _))
    have hquot := hq x (abs_pos.mpr hn) hnear
    have hbound : |(f x - f a) / (x - a)| ≤ |d| + 1 := by
      have ht := abs_add_le ((f x - f a) / (x - a) - d) d
      rw [sub_add_cancel] at ht
      linarith

    have heq : f x - f a = ((f x - f a) / (x - a)) * (x - a) := by
      rw [div_mul_cancel₀ _ hn]
    rw [Real.dist_eq, heq, abs_mul]
    exact (mul_le_mul_of_nonneg_right hbound (abs_nonneg _)).trans_lt
      (by simpa only [mul_comm] using hsmall)

/-- Corollary: differentiability implies continuity. -/
theorem differentiableAt_continuousAt (f : ℝ → ℝ) (a : ℝ)
    (hf : DifferentiableAt ℝ f a) : ContinuousAt f a :=
  continuousAt_of_hasDerivAt f (deriv f a) a hf.hasDerivAt

/-- Lemma: linear combinations have the corresponding linear combination of derivatives. -/
theorem hasDerivAt_linear_combination (f g : ℝ → ℝ) (df dg A B a : ℝ)
    (hf : HasDerivAt f df a) (hg : HasDerivAt g dg a) :
    HasDerivAt (fun x => A * f x + B * g x) (A * df + B * dg) a := by
  apply (hasDerivAt_iff_limit _ _ a).mpr
  apply (punctured_limit_iff_sequences _ a _).mpr
  intro u hu hlim
  have hfl := (punctured_limit_iff_sequences _ a df).mp
    ((hasDerivAt_iff_limit f df a).mp hf) u hu hlim
  have hgl := (punctured_limit_iff_sequences _ a dg).mp
    ((hasDerivAt_iff_limit g dg a).mp hg) u hu hlim
  have hsum := real_tendsto_add _ _ _ _
    (real_tendsto_const_mul _ df A hfl) (real_tendsto_const_mul _ dg B hgl)
  convert hsum using 1
  funext n
  dsimp [Function.comp_def]
  ring

/-- Lemma: the identity function has derivative one. -/
theorem hasDerivAt_identity (a : ℝ) : HasDerivAt (fun x : ℝ => x) 1 a := by
  apply (hasDerivAt_iff_epsilon _ 1 a).mpr
  intro ε hε
  refine ⟨1, zero_lt_one, ?_⟩
  intro x hx _
  rw [div_self (abs_pos.mp hx), sub_self, abs_zero]
  exact hε

/-- Theorem: the chain rule, including sequences along which the inner function
equals its value at the base point. -/
theorem hasDerivAt_comp (f g : ℝ → ℝ) (df dg a : ℝ)
    (hf : HasDerivAt f df a) (hg : HasDerivAt g dg (f a)) :
    HasDerivAt (g ∘ f) (dg * df) a := by
  apply (hasDerivAt_iff_limit _ _ a).mpr
  apply (punctured_limit_iff_sequences _ a _).mpr
  intro u hu hlim
  have hfu := (continuousAt_iff_sequences f a).mp
    (continuousAt_of_hasDerivAt f df a hf) u hlim
  have hinner := (continuousAt_iff_sequences (derivativeSlope f df a) a).mp
    (derivativeSlope_continuousAt f df a hf) u hlim
  have houter := (continuousAt_iff_sequences (derivativeSlope g dg (f a)) (f a)).mp
    (derivativeSlope_continuousAt g dg (f a) hg) (f ∘ u) hfu
  simp only [derivativeSlope, ↓reduceIte] at hinner houter

  have hprod := real_tendsto_mul _ _ dg df houter hinner
  convert hprod using 1
  funext n
  dsimp [Function.comp_def, derivativeSlope]
  rw [ite_eq_right (hu n)]
  by_cases heq : f (u n) = f a
  · simp only [heq, ↓reduceIte, sub_self, zero_div, mul_zero]
  · rw [ite_eq_right heq]
    field_simp [sub_ne_zero.mpr heq]

end MathematicalAnalysis.Chapter04
