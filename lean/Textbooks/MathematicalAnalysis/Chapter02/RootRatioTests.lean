import Textbooks.MathematicalAnalysis.Chapter02.Series
import Textbooks.MathematicalAnalysis.Chapter02.SpecialSequences
import Mathlib.Algebra.Field.GeomSum

namespace MathematicalAnalysis.Chapter02

open Filter Finset
open scoped Topology

/-- Definition: root terms use positive indices, excluding the irrelevant zeroth root. -/
noncomputable def rootTerms (u : ℕ → ℝ) (n : ℕ) : ℝ := |u (n + 1)| ^ ((n + 1 : ℝ)⁻¹)

/-- Definition: ratio terms are absolute consecutive quotients;
ratio theorems require the denominators to be eventually nonzero. -/
noncomputable def ratioTerms (u : ℕ → ℝ) (n : ℕ) : ℝ := |u (n + 1) / u n|

/-- Lemma: nonnegative geometric series with ratio below one converge. -/
theorem geometric_series_converges (C q : ℝ) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    SeriesConverges (fun n : ℕ => C * q ^ n) := by
  apply (nonneg_seriesConverges_iff _ (fun n => mul_nonneg hC (pow_nonneg hq0 n))).mpr
  refine ⟨C / (1 - q), ?_⟩
  rintro x ⟨n, rfl⟩
  change (∑ k ∈ range n, C * q ^ k) ≤ C / (1 - q)
  rw [← mul_sum, geom_sum_eq hq1.ne]
  rw [le_div_iff₀ (sub_pos.mpr hq1)]
  have heq : C * ((q ^ n - 1) / (q - 1)) * (1 - q) = C * (1 - q ^ n) := by
    field_simp [sub_ne_zero.mpr hq1.ne]
    ring
  rw [heq]
  nlinarith [pow_nonneg hq0 n]

/-- Lemma: eventual domination by a decaying geometric progression implies absolute convergence. -/
theorem geometric_majorant (u : ℕ → ℝ) (C q : ℝ) (hC : 0 ≤ C)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hu : ∀ᶠ n in atTop, |u n| ≤ C * q ^ n) :
    AbsolutelyConverges u := by
  apply series_comparison (fun n => |u n|) (fun n => C * q ^ n) _
    (geometric_series_converges C q hC hq0 hq1)
  simpa only [abs_abs] using hu

private theorem exists_real_bound_below_one (a : EReal) (ha : a < 1) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ a < (q : EReal) := by
  obtain ⟨b, hab, hb⟩ := exists_between ha
  induction b using EReal.rec with
  | bot => exact (not_lt_of_ge bot_le hab).elim
  | top => exact (not_lt_of_ge le_top hb).elim
  | coe b =>
    have hb1 : b < 1 := EReal.coe_lt_coe_iff.mp hb
    let q := (max b 0 + 1) / 2
    have hm : max b 0 < 1 := max_lt hb1 zero_lt_one
    have hq0 : 0 < q := by
      dsimp [q]
      linarith [le_max_right b 0]
    have hq1 : q < 1 := by
      dsimp [q]
      linarith
    have hbq : b < q := by
      dsimp [q]
      linarith [le_max_left b 0]
    exact ⟨q, hq0, hq1, hab.trans (EReal.coe_lt_coe_iff.mpr hbq)⟩

/-- Lemma: an upper-limit bound supplies an eventual strict real upper bound. -/
theorem eventually_lt_of_limsup_lt (u : ℕ → ℝ) (q : ℝ)
    (h : limsup (fun n => (u n : EReal)) atTop < (q : EReal)) :
    ∀ᶠ n in atTop, u n < q := by
  obtain ⟨N, hN⟩ := ((limsup_eq_iff_thresholds _ _).mp rfl).1 q h
  exact eventually_atTop.mpr ⟨N, fun n hn => EReal.coe_lt_coe_iff.mp (hN n hn)⟩

/-- Theorem: an upper limit of root terms below one implies absolute convergence. -/
theorem root_test_convergence (u : ℕ → ℝ)
    (hroot : limsup (fun n => (rootTerms u n : EReal)) atTop < 1) :
    AbsolutelyConverges u := by
  obtain ⟨q, hq0, hq1, hq⟩ := exists_real_bound_below_one _ hroot
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt _ q hq)
  apply geometric_majorant u 1 q zero_le_one hq0.le hq1
  apply eventually_atTop.mpr
  refine ⟨N + 1, ?_⟩
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hnN : N ≤ n - 1 := by omega
  have hrootn : |u n| ^ ((n : ℝ)⁻¹) < q := by
    have h := hN (n - 1) hnN
    dsimp [rootTerms] at h
    rw [← Nat.cast_succ] at h
    simpa only [Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega : 1 ≤ n)] using h
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (abs_nonneg _) _) hrootn.le n
  rw [Real.rpow_inv_natCast_pow (abs_nonneg _) hn0] at hpow
  simpa only [one_mul] using hpow

/-- Theorem: an upper limit of root terms above one implies divergence. -/
theorem root_test_divergence (u : ℕ → ℝ)
    (hroot : 1 < limsup (fun n => (rootTerms u n : EReal)) atTop) :
    ¬ SeriesConverges u := by
  intro hu
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (seriesConverges_tendsto_zero u hu) 1 zero_lt_one
  obtain ⟨n, hn, hrootn⟩ := ((limsup_eq_iff_thresholds _ _).mp rfl).2 1 hroot N
  have hnear : |u (n + 1)| < 1 := by
    simpa only [Real.dist_eq, sub_zero] using hN (n + 1) (by omega)
  have hrootn' : 1 < rootTerms u n := EReal.coe_lt_coe_iff.mp hrootn
  have hpow := pow_lt_pow_left₀ hrootn' zero_le_one (Nat.succ_ne_zero n)
  dsimp [rootTerms] at hpow
  rw [← Nat.cast_succ, Real.rpow_inv_natCast_pow (abs_nonneg _) (Nat.succ_ne_zero n),
    one_pow] at hpow
  linarith

/-- Lemma: an eventual upper ratio bound gives a geometric majorant. -/
theorem ratio_upper_majorant (u : ℕ → ℝ) (q : ℝ) (hq : 0 < q)
    (hstep : ∀ᶠ n in atTop, |u (n + 1)| ≤ q * |u n|) :
    ∃ C ≥ 0, ∀ᶠ n in atTop, |u n| ≤ C * q ^ n := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hstep
  let C := |u N| / q ^ N
  have hC : 0 ≤ C := div_nonneg (abs_nonneg _) (pow_nonneg hq.le _)
  refine ⟨C, hC, eventually_atTop.mpr ⟨N, ?_⟩⟩
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    exact (div_mul_cancel₀ (|u N|) (pow_pos hq N).ne').ge
  | succ n hn ih =>
    have hmul := mul_le_mul_of_nonneg_left ih hq.le
    rw [pow_succ]
    nlinarith [hN n hn]

/-- Theorem: an upper limit of ratios below one implies absolute convergence. -/
theorem ratio_test_convergence (u : ℕ → ℝ) (hu0 : ∀ᶠ n in atTop, u n ≠ 0)
    (hratio : limsup (fun n => (ratioTerms u n : EReal)) atTop < 1) :
    AbsolutelyConverges u := by
  obtain ⟨q, hq0, hq1, hq⟩ := exists_real_bound_below_one _ hratio
  have hstep : ∀ᶠ n in atTop, |u (n + 1)| ≤ q * |u n| := by
    filter_upwards [hu0, eventually_lt_of_limsup_lt _ q hq] with n hn hr
    dsimp [ratioTerms] at hr
    rw [abs_div, div_lt_iff₀ (abs_pos.mpr hn)] at hr
    exact hr.le
  obtain ⟨C, hC, hbound⟩ := ratio_upper_majorant u q hq0 hstep
  exact geometric_majorant u C q hC hq0.le hq1 hbound

/-- Theorem: eventually nonzero terms and ratios at least one force divergence. -/
theorem ratio_test_divergence (u : ℕ → ℝ)
    (hu0 : ∀ᶠ n in atTop, u n ≠ 0)
    (hratio : ∀ᶠ n in atTop, 1 ≤ ratioTerms u n) : ¬ SeriesConverges u := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hu0.and hratio)
  have hpos : 0 < |u N| := abs_pos.mpr (hN N le_rfl).1
  have hbound : ∀ n ≥ N, |u N| ≤ |u n| := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih =>
      have hr := (hN n hn).2
      dsimp [ratioTerms] at hr
      rw [abs_div, le_div_iff₀ (abs_pos.mpr (hN n hn).1), one_mul] at hr
      exact ih.trans hr

  intro hu
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp (seriesConverges_tendsto_zero u hu) (|u N|) hpos
  have hnear : |u (max N M)| < |u N| := by
    simpa only [Real.dist_eq, sub_zero] using hM (max N M) (le_max_right _ _)
  exact (not_lt_of_ge (hbound (max N M) (le_max_left _ _))) hnear

end MathematicalAnalysis.Chapter02
