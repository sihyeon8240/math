import Textbooks.MathematicalAnalysis.Chapter02.RootRatioTests

namespace MathematicalAnalysis.Chapter02

open Filter
open scoped Topology

private theorem roots_limsup_le_of_ratio_bound (u : ℕ → ℝ) (q : ℝ) (hq : 0 < q)
    (hstep : ∀ᶠ n in atTop, |u (n + 1)| ≤ q * |u n|) :
    limsup (fun n => (rootTerms u n : EReal)) atTop ≤ (q : EReal) := by
  obtain ⟨C, hC, hbound⟩ := ratio_upper_majorant u q hq hstep
  let w : ℕ → ℝ := fun n => (C + 1) ^ ((n + 1 : ℝ)⁻¹) * q
  have hlim : Tendsto w atTop (𝓝 q) := by
    simpa only [one_mul] using real_tendsto_mul _ _ _ _
      (nth_root_tendsto_one (C + 1) (by linarith)) (real_tendsto_const q)
  have hrootbound : ∀ᶠ n in atTop, rootTerms u n ≤ w n := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
    apply eventually_atTop.mpr
    refine ⟨N, ?_⟩
    intro n hn
    have hpow : 0 ≤ q ^ (n + 1) := pow_nonneg hq.le _
    have hmajor : |u (n + 1)| ≤ (C + 1) * q ^ (n + 1) := by
      have hb := hN (n + 1) (by omega)
      nlinarith
    have hroot := Real.rpow_le_rpow (abs_nonneg _) hmajor
      (by positivity : 0 ≤ (n + 1 : ℝ)⁻¹)
    rw [Real.mul_rpow (by linarith : 0 ≤ C + 1) hpow] at hroot
    have heq : (q ^ (n + 1)) ^ ((n + 1 : ℝ)⁻¹) = q := by
      simpa only [Nat.cast_succ] using
        Real.pow_rpow_inv_natCast hq.le (Nat.succ_ne_zero n)
    rw [heq] at hroot
    exact hroot

  have hcomp := (liminf_limsup_mono _ w hrootbound).2
  rw [(liminf_limsup_of_tendsto w q hlim).2] at hcomp
  exact hcomp

private theorem roots_liminf_ge_of_ratio_bound (u : ℕ → ℝ) (q : ℝ) (hq : 0 < q)
    (hu0 : ∀ᶠ n in atTop, u n ≠ 0)
    (hstep : ∀ᶠ n in atTop, q * |u n| ≤ |u (n + 1)|) :
    (q : EReal) ≤ liminf (fun n => (rootTerms u n : EReal)) atTop := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hu0.and hstep)
  let C := |u N| / q ^ N
  have hC : 0 < C := div_pos (abs_pos.mpr (hN N le_rfl).1) (pow_pos hq N)
  have hbound : ∀ n ≥ N, C * q ^ n ≤ |u n| := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact (div_mul_cancel₀ (|u N|) (pow_pos hq N).ne').le
    | succ n hn ih =>
      have hmul := mul_le_mul_of_nonneg_left ih hq.le
      rw [pow_succ]
      nlinarith [(hN n hn).2]

  let w : ℕ → ℝ := fun n => C ^ ((n + 1 : ℝ)⁻¹) * q
  have hlim : Tendsto w atTop (𝓝 q) := by
    simpa only [one_mul] using real_tendsto_mul _ _ _ _
      (nth_root_tendsto_one C hC) (real_tendsto_const q)
  have hrootbound : ∀ᶠ n in atTop, w n ≤ rootTerms u n := by
    apply eventually_atTop.mpr
    refine ⟨N, ?_⟩
    intro n hn
    have hroot := Real.rpow_le_rpow (mul_nonneg hC.le (pow_nonneg hq.le _))
      (hbound (n + 1) (by omega)) (by positivity : 0 ≤ (n + 1 : ℝ)⁻¹)
    rw [Real.mul_rpow hC.le (pow_nonneg hq.le _)] at hroot
    have heq : (q ^ (n + 1)) ^ ((n + 1 : ℝ)⁻¹) = q := by
      simpa only [Nat.cast_succ] using
        Real.pow_rpow_inv_natCast hq.le (Nat.succ_ne_zero n)
    rw [heq] at hroot
    exact hroot

  have hcomp := (liminf_limsup_mono w _ hrootbound).1
  rw [(liminf_limsup_of_tendsto w q hlim).1] at hcomp
  exact hcomp

/-- Theorem: consecutive ratios bound the lower and upper limits of root terms. -/
theorem root_ratio_comparison (u : ℕ → ℝ) (hu0 : ∀ᶠ n in atTop, u n ≠ 0) :
    liminf (fun n => (ratioTerms u n : EReal)) atTop ≤
      liminf (fun n => (rootTerms u n : EReal)) atTop ∧
    liminf (fun n => (rootTerms u n : EReal)) atTop ≤
      limsup (fun n => (rootTerms u n : EReal)) atTop ∧
    limsup (fun n => (rootTerms u n : EReal)) atTop ≤
      limsup (fun n => (ratioTerms u n : EReal)) atTop := by
  have hrootnonneg := (nonneg_liminf_limsup (rootTerms u)
    (fun n => Real.rpow_nonneg (abs_nonneg _) _)).1
  have hrationonneg := (nonneg_liminf_limsup (ratioTerms u) (fun n => abs_nonneg _)).2
  refine ⟨?_, liminf_le_limsup (rootTerms u), ?_⟩

  · by_contra h
    obtain ⟨b, hrootb, hbratio⟩ := exists_between (lt_of_not_ge h)
    induction b using EReal.rec with
    | bot => exact (not_lt_of_ge bot_le hrootb).elim
    | top => exact (not_lt_of_ge le_top hbratio).elim
    | coe q =>
      have hq : 0 < q := EReal.coe_lt_coe_iff.mp (hrootnonneg.trans_lt hrootb)
      have hstep : ∀ᶠ n in atTop, q * |u n| ≤ |u (n + 1)| := by
        filter_upwards [hu0, eventually_gt_of_lt_liminf (ratioTerms u) q hbratio] with n hn hr
        dsimp [ratioTerms] at hr
        rw [abs_div, lt_div_iff₀ (abs_pos.mpr hn)] at hr
        exact hr.le
      exact (not_lt_of_ge (roots_liminf_ge_of_ratio_bound u q hq hu0 hstep)) hrootb

  · by_contra h
    obtain ⟨b, hratiob, hbroot⟩ := exists_between (lt_of_not_ge h)
    induction b using EReal.rec with
    | bot => exact (not_lt_of_ge bot_le hratiob).elim
    | top => exact (not_lt_of_ge le_top hbroot).elim
    | coe q =>
      have hq : 0 < q := EReal.coe_lt_coe_iff.mp (hrationonneg.trans_lt hratiob)
      have hstep : ∀ᶠ n in atTop, |u (n + 1)| ≤ q * |u n| := by
        filter_upwards [hu0, eventually_lt_of_limsup_lt (ratioTerms u) q hratiob] with n hn hr
        dsimp [ratioTerms] at hr
        rw [abs_div, div_lt_iff₀ (abs_pos.mpr hn)] at hr
        exact hr.le
      exact (not_lt_of_ge (roots_limsup_le_of_ratio_bound u q hq hstep)) hbroot

end MathematicalAnalysis.Chapter02
