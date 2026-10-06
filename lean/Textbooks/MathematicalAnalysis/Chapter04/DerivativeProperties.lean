import Textbooks.MathematicalAnalysis.Chapter04.MeanValue

namespace MathematicalAnalysis.Chapter04

open Set Metric
open scoped Topology
open MathematicalAnalysis.Chapter01 MathematicalAnalysis.Chapter03

/-- Theorem: a nonnegative derivative makes a function nondecreasing on an open interval.
No continuity at its endpoints is assumed. -/
theorem monotoneOn_of_derivative_nonneg (f df : ℝ → ℝ) (a b : ℝ)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (df x) x)
    (hpos : ∀ x ∈ Ioo a b, 0 ≤ df x) : MonotoneOn f (Ioo a b) := by
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with rfl | hxy
  · exact le_rfl
  · have hsub : Icc x y ⊆ Ioo a b := fun z hz =>
      ⟨hx.1.trans_le hz.1, hz.2.trans_lt hy.2⟩
    have hc : ContinuousOn f (Icc x y) := by
      intro z hz
      exact (continuousAt_of_hasDerivAt f (df z) z (hd z (hsub hz))).continuousWithinAt

    obtain ⟨c, hcI, heq⟩ := mean_value f df x y hxy hc
      (fun z hz => hd z (hsub ⟨hz.1.le, hz.2.le⟩))
    have hnonneg := hpos c (hsub ⟨hcI.1.le, hcI.2.le⟩)
    have hmul := (eq_div_iff (sub_ne_zero.mpr (ne_of_gt hxy))).mp heq

    nlinarith

/-- Theorem: a nonpositive derivative makes a function nonincreasing on an open interval. -/
theorem antitoneOn_of_derivative_nonpos (f df : ℝ → ℝ) (a b : ℝ)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (df x) x)
    (hneg : ∀ x ∈ Ioo a b, df x ≤ 0) : AntitoneOn f (Ioo a b) := by
  have hdn : ∀ x ∈ Ioo a b, HasDerivAt (fun x => -f x) (-df x) x := by
    intro x hx
    simpa only [neg_one_mul, zero_mul, add_zero] using
      hasDerivAt_linear_combination f f (df x) (df x) (-1) 0 x (hd x hx) (hd x hx)

  have hm := monotoneOn_of_derivative_nonneg (fun x => -f x) (fun x => -df x) a b
    hdn (fun x hx => neg_nonneg.mpr (hneg x hx))
  intro x hx y hy hxy
  exact neg_le_neg_iff.mp (hm hx hy hxy)

/-- Theorem: a zero derivative makes a function constant throughout an open interval. -/
theorem constant_of_derivative_zero (f df : ℝ → ℝ) (a b : ℝ)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (df x) x)
    (hz : ∀ x ∈ Ioo a b, df x = 0) :
    ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, f x = f y := by
  have hm := monotoneOn_of_derivative_nonneg f df a b hd (fun x hx => (hz x hx).ge)
  have ha := antitoneOn_of_derivative_nonpos f df a b hd (fun x hx => (hz x hx).le)
  intro x hx y hy
  rcases le_total x y with hxy | hyx
  · exact le_antisymm (hm hx hy hxy) (ha hx hy hxy)
  · exact le_antisymm (ha hy hx hyx) (hm hy hx hyx)

private theorem exists_right_lt (f : ℝ → ℝ) (d a b : ℝ) (hab : a < b)
    (hd : HasDerivAt f d a) (hneg : d < 0) : ∃ x ∈ Ioo a b, f x < f a := by
  obtain ⟨δ, hδ, hq⟩ := (hasDerivAt_iff_epsilon f d a).mp hd (-d) (neg_pos.mpr hneg)
  let t := min δ (b - a) / 2
  have ht : 0 < t := half_pos (lt_min hδ (sub_pos.mpr hab))
  have htδ : t < δ := (half_lt_self (lt_min hδ (sub_pos.mpr hab))).trans_le
    (min_le_left _ _)
  have htb : t < b - a := (half_lt_self (lt_min hδ (sub_pos.mpr hab))).trans_le
    (min_le_right _ _)
  have hdist : |a + t - a| = t := by simp only [add_sub_cancel_left, abs_of_pos ht]
  have hquot := (abs_lt.mp (hq (a + t) (by rwa [hdist]) (by rwa [hdist]))).2
  have hlt : (f (a + t) - f a) / (a + t - a) < 0 := by linarith
  have hnum := (div_lt_iff₀ (by linarith : 0 < a + t - a)).mp hlt

  exact ⟨a + t, ⟨by linarith, by linarith⟩, by linarith⟩

private theorem exists_left_lt (f : ℝ → ℝ) (d a b : ℝ) (hab : a < b)
    (hd : HasDerivAt f d b) (hpos : 0 < d) : ∃ x ∈ Ioo a b, f x < f b := by
  obtain ⟨δ, hδ, hq⟩ := (hasDerivAt_iff_epsilon f d b).mp hd d hpos
  let t := min δ (b - a) / 2
  have ht : 0 < t := half_pos (lt_min hδ (sub_pos.mpr hab))
  have htδ : t < δ := (half_lt_self (lt_min hδ (sub_pos.mpr hab))).trans_le
    (min_le_left _ _)
  have htb : t < b - a := (half_lt_self (lt_min hδ (sub_pos.mpr hab))).trans_le
    (min_le_right _ _)
  have hdist : |b - t - b| = t := by
    rw [show b - t - b = -t by ring, abs_neg, abs_of_pos ht]

  have hquot := (abs_lt.mp (hq (b - t) (by rwa [hdist]) (by rwa [hdist]))).1
  have hlt : 0 < (f (b - t) - f b) / (b - t - b) := by linarith
  have hnum := (div_pos_iff).mp hlt

  rcases hnum with h | h
  · linarith [h.2]
  · exact ⟨b - t, ⟨by linarith, by linarith⟩, sub_neg.mp h.1⟩

/-- Theorem: derivatives have the intermediate value property. Endpoint
derivatives are explicitly assumed, since the statement compares their values. -/
theorem derivative_intermediate_value (f df : ℝ → ℝ) (a b v : ℝ) (hab : a < b)
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (df x) x)
    (ha : df a < v) (hb : v < df b) : ∃ c ∈ Ioo a b, df c = v := by
  let F := fun x => f x - v * x
  have hF : ∀ x ∈ Icc a b, HasDerivAt F (df x - v) x := by
    intro x hx
    simpa only [F, one_mul, mul_one, neg_mul, sub_eq_add_neg] using
      hasDerivAt_linear_combination f (fun x => x) (df x) 1 1 (-v) x
        (hd x hx) (hasDerivAt_identity x)

  have hc : ContinuousOn F (Icc a b) := by
    intro x hx
    exact (continuousAt_of_hasDerivAt F (df x - v) x (hF x hx)).continuousWithinAt

  have hbound := compact_bounded _ (compact_image_on _ (interval_compact a b hab.le) F hc)

  obtain ⟨_, ⟨c, hcI, hFc⟩⟩ := extreme_value_interval a b hab.le F hc
  have hmin : ∀ x ∈ Icc a b, F c ≤ F x := by
    intro x hx
    rw [hFc]
    exact csInf_le hbound.bddBelow ⟨x, hx, rfl⟩

  obtain ⟨x, hx, hxa⟩ := exists_right_lt F (df a - v) a b hab
    (hF a ⟨le_rfl, hab.le⟩) (sub_neg.mpr ha)
  obtain ⟨y, hy, hyb⟩ := exists_left_lt F (df b - v) a b hab
    (hF b ⟨hab.le, le_rfl⟩) (sub_pos.mpr hb)
  have hci : c ∈ Ioo a b := by
    constructor
    · apply lt_of_le_of_ne hcI.1
      intro heq
      have hm := hmin x ⟨hx.1.le, hx.2.le⟩
      rw [← heq] at hm
      linarith

    · apply lt_of_le_of_ne hcI.2
      intro heq
      have hm := hmin y ⟨hy.1.le, hy.2.le⟩
      rw [heq] at hm
      linarith

  have hlocal : IsLocalMin F c := by
    have hm := localMax_of_interval (fun x => -F x) a b c hci
      (fun x hx => neg_le_neg (hmin x hx))

    obtain ⟨δ, hδ, hb⟩ := (isLocalMax_iff _ c).mp hm
    exact (isLocalMin_iff F c).mpr ⟨δ, hδ, fun x hx => neg_le_neg_iff.mp (hb x hx)⟩

  have hz := derivative_zero_of_localMin F (df c - v) c (hF c hcI) hlocal

  exact ⟨c, hci, sub_eq_zero.mp hz⟩

end MathematicalAnalysis.Chapter04
