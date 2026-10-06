import Textbooks.MathematicalAnalysis.Chapter04.MeanValue

namespace MathematicalAnalysis.Chapter04

open Set Metric Filter
open scoped Topology
open MathematicalAnalysis.Chapter01 MathematicalAnalysis.Chapter03

/-- Lemma: Euclidean limits are exactly the limits of all coordinate functions. -/
theorem euclidean_tendsto_iff {A : Type*} (l : Filter A) (m : ℕ)
    (f : A → EuclideanSpace ℝ (Fin m)) (v : EuclideanSpace ℝ (Fin m)) :
    Tendsto f l (𝓝 v) ↔ ∀ j, Tendsto (fun x => f x j) l (𝓝 (v j)) := by
  constructor
  · intro h j
    have hid : Continuous (fun x : EuclideanSpace ℝ (Fin m) => x) := by
      apply Metric.continuous_iff.mpr
      intro _ ε hε
      exact ⟨ε, hε, fun _ hx => hx⟩
    have hcoord := (continuous_euclidean_iff m _).mp hid j
    exact hcoord.continuousAt.tendsto.comp h
  · intro h
    have hp : Tendsto (fun x => (fun j => f x j : Fin m → ℝ)) l
        (𝓝 (fun j => v j)) := tendsto_pi_nhds.mpr h
    exact (continuous_to_euclidean m).continuousAt.tendsto.comp hp

/-- Theorem: the derivative of a Euclidean-valued function is the vector of its
coordinate derivatives. -/
theorem hasDerivAt_euclidean_iff (m : ℕ) (f : ℝ → EuclideanSpace ℝ (Fin m))
    (v : EuclideanSpace ℝ (Fin m)) (a : ℝ) :
    HasDerivAt f v a ↔ ∀ j, HasDerivAt (fun x => f x j) (v j) a := by
  rw [hasDerivAt_iff_tendsto_slope, euclidean_tendsto_iff]
  apply forall_congr'
  intro j
  rw [hasDerivAt_iff_limit]
  have heq : (fun x => slope f a x j) = fun x => (f x j - f a j) / (x - a) := by
    funext x
    rw [slope_def_module]
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq]

private theorem continuous_inner (m : ℕ) (v : EuclideanSpace ℝ (Fin m)) :
    Continuous (fun x : EuclideanSpace ℝ (Fin m) => inner ℝ v x) := by
  apply Metric.continuous_iff.mpr
  intro a ε hε
  have hp : 0 < ‖v‖ + 1 := by positivity
  refine ⟨ε / (‖v‖ + 1), div_pos hε hp, ?_⟩
  intro x hx
  rw [Real.dist_eq, ← inner_sub_right]
  have hsmall := (lt_div_iff₀ hp).mp hx
  have hbound := abs_real_inner_le_norm v (x - a)
  rw [← dist_eq_norm] at hbound
  nlinarith [dist_nonneg (x := x) (y := a)]

private theorem hasDerivAt_inner (m : ℕ) (v : EuclideanSpace ℝ (Fin m))
    (f : ℝ → EuclideanSpace ℝ (Fin m)) (df : EuclideanSpace ℝ (Fin m)) (a : ℝ)
    (hf : HasDerivAt f df a) :
    HasDerivAt (fun x => inner ℝ v (f x)) (inner ℝ v df) a := by
  have hlim := (continuous_inner m v).continuousAt.tendsto.comp
    (hasDerivAt_iff_tendsto_slope.mp hf)
  apply (hasDerivAt_iff_limit _ _ a).mpr
  convert hlim using 1
  funext x
  dsimp only [Function.comp_def]
  rw [slope_def_module, inner_smul_right, inner_sub_right]
  simp only [div_eq_mul_inv, mul_comm]

/-- Theorem: a Euclidean-valued function satisfies the mean value inequality
at some interior point; an equality of derivative vectors is not required. -/
theorem vector_mean_value_inequality (m : ℕ)
    (f df : ℝ → EuclideanSpace ℝ (Fin m)) (a b : ℝ) (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (df x) x) :
    ∃ c ∈ Ioo a b, ‖f b - f a‖ ≤ ‖df c‖ * (b - a) := by
  let v := f b - f a
  have hscalar : ContinuousOn (fun x => inner ℝ v (f x)) (Icc a b) := by
    apply (continuousOn_iff_restrict _ _).mpr
    exact continuous_comp (fun x : Icc a b => f x) (fun x => inner ℝ v x)
      ((continuousOn_iff_restrict _ _).mp hf) (continuous_inner m v)
  obtain ⟨c, hc, heq⟩ := mean_value (fun x => inner ℝ v (f x))
    (fun x => inner ℝ v (df x)) a b hab hscalar
    (fun x hx => hasDerivAt_inner m v f (df x) x (hd x hx))
  have heq' := (eq_div_iff (sub_ne_zero.mpr (ne_of_gt hab))).mp heq
  rw [← inner_sub_right, real_inner_self_eq_norm_sq] at heq'
  have hbound := real_inner_le_norm v (df c)
  have hprod := mul_le_mul_of_nonneg_right hbound (sub_pos.mpr hab).le
  refine ⟨c, hc, ?_⟩
  by_cases hv : ‖v‖ = 0
  · change ‖v‖ ≤ ‖df c‖ * (b - a)
    rw [hv]
    exact mul_nonneg (norm_nonneg _) (sub_pos.mpr hab).le
  · have hp : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    change ‖v‖ ≤ ‖df c‖ * (b - a)
    nlinarith

end MathematicalAnalysis.Chapter04
