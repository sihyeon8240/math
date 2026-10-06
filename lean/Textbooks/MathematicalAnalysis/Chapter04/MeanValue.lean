import Textbooks.MathematicalAnalysis.Chapter04.DerivativeLimits
import Textbooks.MathematicalAnalysis.Chapter03.CompactContinuity
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.Order.Bornology

namespace MathematicalAnalysis.Chapter04

open Set Metric Filter
open scoped Topology
open MathematicalAnalysis.Chapter01 MathematicalAnalysis.Chapter03

/-- Definition: a local maximum bounds the function from above throughout some ball. -/
theorem isLocalMax_iff (f : ℝ → ℝ) (a : ℝ) :
    IsLocalMax f a ↔ ∃ δ > 0, ∀ x, |x - a| < δ → f x ≤ f a := by
  exact Metric.eventually_nhds_iff

/-- Definition: a local minimum bounds the function from below throughout some ball. -/
theorem isLocalMin_iff (f : ℝ → ℝ) (a : ℝ) :
    IsLocalMin f a ↔ ∃ δ > 0, ∀ x, |x - a| < δ → f a ≤ f x := by
  exact Metric.eventually_nhds_iff

/-- Theorem: the derivative at a differentiable local maximum is zero. -/
theorem derivative_zero_of_localMax (f : ℝ → ℝ) (d a : ℝ)
    (hf : HasDerivAt f d a) (hmax : IsLocalMax f a) : d = 0 := by
  obtain ⟨r, hr, hbound⟩ := (isLocalMax_iff f a).mp hmax
  apply le_antisymm

  · by_contra hn
    have hd : 0 < d := lt_of_not_ge hn

    obtain ⟨δ, hδ, hq⟩ := (hasDerivAt_iff_epsilon f d a).mp hf d hd
    let t := min r δ / 2
    have ht : 0 < t := half_pos (lt_min hr hδ)
    have htr : t < r := (half_lt_self (lt_min hr hδ)).trans_le (min_le_left _ _)
    have htδ : t < δ := (half_lt_self (lt_min hr hδ)).trans_le (min_le_right _ _)
    have hdist : |a + t - a| = t := by simp only [add_sub_cancel_left, abs_of_pos ht]
    have hle := hbound (a + t) (by rwa [hdist])
    have hquot := hq (a + t) (by rwa [hdist]) (by rwa [hdist])
    have hsign : (f (a + t) - f a) / (a + t - a) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hle) (by linarith)
    have hlow := (abs_lt.mp hquot).1

    linarith

  · by_contra hn
    have hd : d < 0 := lt_of_not_ge hn

    obtain ⟨δ, hδ, hq⟩ := (hasDerivAt_iff_epsilon f d a).mp hf (-d) (neg_pos.mpr hd)
    let t := min r δ / 2
    have ht : 0 < t := half_pos (lt_min hr hδ)
    have htr : t < r := (half_lt_self (lt_min hr hδ)).trans_le (min_le_left _ _)
    have htδ : t < δ := (half_lt_self (lt_min hr hδ)).trans_le (min_le_right _ _)
    have hdist : |a - t - a| = t := by
      rw [show a - t - a = -t by ring, abs_neg, abs_of_pos ht]

    have hle := hbound (a - t) (by rwa [hdist])
    have hquot := hq (a - t) (by rwa [hdist]) (by rwa [hdist])
    have hsign : 0 ≤ (f (a - t) - f a) / (a - t - a) :=
      div_nonneg_of_nonpos (sub_nonpos.mpr hle) (by linarith)
    have hupp := (abs_lt.mp hquot).2

    linarith

/-- Corollary: the derivative at a differentiable local minimum is zero. -/
theorem derivative_zero_of_localMin (f : ℝ → ℝ) (d a : ℝ)
    (hf : HasDerivAt f d a) (hmin : IsLocalMin f a) : d = 0 := by
  have hn : HasDerivAt (fun x => -f x) (-d) a := by
    simpa only [neg_one_mul, zero_mul, add_zero] using
      hasDerivAt_linear_combination f f d d (-1) 0 a hf hf

  have hm : IsLocalMax (fun x => -f x) a := by
    obtain ⟨r, hr, hb⟩ := (isLocalMin_iff f a).mp hmin
    exact (isLocalMax_iff _ a).mpr ⟨r, hr, fun x hx => neg_le_neg (hb x hx)⟩

  have hz := derivative_zero_of_localMax _ (-d) a hn hm

  linarith

/-- Lemma: an extremum on an interval is a local extremum at each interior point. -/
theorem localMax_of_interval (f : ℝ → ℝ) (a b c : ℝ) (hc : c ∈ Ioo a b)
    (hmax : ∀ x ∈ Icc a b, f x ≤ f c) : IsLocalMax f c := by
  refine (isLocalMax_iff f c).mpr ⟨min (c - a) (b - c),
    lt_min (sub_pos.mpr hc.1) (sub_pos.mpr hc.2), ?_⟩
  intro x hx
  have hl := hx.trans_le (min_le_left _ _)
  have hr := hx.trans_le (min_le_right _ _)
  rw [abs_lt] at hl hr
  exact hmax x ⟨by linarith, by linarith⟩

/-- Theorem: Rolle's theorem, obtained from interval extrema and the local extremum criterion. -/
theorem rolle (f : ℝ → ℝ) (df : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hc : ContinuousOn f (Icc a b)) (hd : ∀ x ∈ Ioo a b, HasDerivAt f (df x) x)
    (heq : f a = f b) : ∃ c ∈ Ioo a b, df c = 0 := by
  have hbdd := compact_bounded _ (compact_image_on _ (interval_compact a b hab.le) f hc)

  obtain ⟨⟨u, hu, hfu⟩, ⟨v, hv, hfv⟩⟩ := extreme_value_interval a b hab.le f hc
  have hmax : ∀ x ∈ Icc a b, f x ≤ f u := by
    intro x hx
    rw [hfu]
    exact le_csSup hbdd.bddAbove ⟨x, hx, rfl⟩

  have hmin : ∀ x ∈ Icc a b, f v ≤ f x := by
    intro x hx
    rw [hfv]
    exact csInf_le hbdd.bddBelow ⟨x, hx, rfl⟩

  by_cases hgt : f a < f u

  · have hui : u ∈ Ioo a b := by
      constructor
      · exact lt_of_le_of_ne hu.1 (fun h => (ne_of_lt hgt) (congrArg f h))
      · exact lt_of_le_of_ne hu.2 (fun h => (ne_of_lt hgt).symm ((congrArg f h).trans heq.symm))
    exact ⟨u, hui, derivative_zero_of_localMax f (df u) u (hd u hui)
      (localMax_of_interval f a b u hui hmax)⟩

  · by_cases hlt : f v < f a
    · have hvi : v ∈ Ioo a b := by
        constructor
        · exact lt_of_le_of_ne hv.1 (fun h => (ne_of_lt hlt).symm (congrArg f h))
        · exact lt_of_le_of_ne hv.2 (fun h => (ne_of_lt hlt) ((congrArg f h).trans heq.symm))
      have hm : IsLocalMin f v := by
        have hn := localMax_of_interval (fun x => -f x) a b v hvi
          (fun x hx => neg_le_neg (hmin x hx))

        obtain ⟨r, hr, hb⟩ := (isLocalMax_iff _ v).mp hn
        exact (isLocalMin_iff f v).mpr ⟨r, hr, fun x hx => neg_le_neg_iff.mp (hb x hx)⟩

      exact ⟨v, hvi, derivative_zero_of_localMin f (df v) v (hd v hvi) hm⟩

    · let c := (a + b) / 2
      have hci : c ∈ Ioo a b := ⟨by dsimp [c]; linarith, by dsimp [c]; linarith⟩
      have hconst : ∀ x ∈ Icc a b, f x = f a := by
        intro x hx
        exact le_antisymm ((hmax x hx).trans (le_of_not_gt hgt))
          ((le_of_not_gt hlt).trans (hmin x hx))

      have hm := localMax_of_interval f a b c hci (fun x hx => by
        rw [hconst x hx, hconst c ⟨hci.1.le, hci.2.le⟩])

      exact ⟨c, hci, derivative_zero_of_localMax f (df c) c (hd c hci) hm⟩

/-- Theorem: the Cauchy mean value theorem requires no nonzero derivative assumption. -/
theorem cauchy_mean_value (f g df dg : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hdf : ∀ x ∈ Ioo a b, HasDerivAt f (df x) x)
    (hdg : ∀ x ∈ Ioo a b, HasDerivAt g (dg x) x) :
    ∃ c ∈ Ioo a b, (f b - f a) * dg c = (g b - g a) * df c := by
  let F := fun x => (g b - g a) * f x - (f b - f a) * g x
  have hF : ContinuousOn F (Icc a b) := by
    apply (continuousOn_iff_restrict _ _).mpr
    exact continuous_sub _ _
      (continuous_mul _ _ (continuous_const _) ((continuousOn_iff_restrict _ _).mp hf))
      (continuous_mul _ _ (continuous_const _) ((continuousOn_iff_restrict _ _).mp hg))

  have hFD : ∀ x ∈ Ioo a b,
      HasDerivAt F ((g b - g a) * df x - (f b - f a) * dg x) x := by
    intro x hx
    simpa only [F, neg_mul, sub_eq_add_neg] using
      hasDerivAt_linear_combination f g (df x) (dg x)
        (g b - g a) (-(f b - f a)) x (hdf x hx) (hdg x hx)

  obtain ⟨c, hc, hzero⟩ := rolle F _ a b hab hF hFD (by dsimp [F]; ring)

  exact ⟨c, hc, by linarith⟩

/-- Theorem: the scalar mean value theorem. -/
theorem mean_value (f df : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hd : ∀ x ∈ Ioo a b, HasDerivAt f (df x) x) :
    ∃ c ∈ Ioo a b, df c = (f b - f a) / (b - a) := by
  have hid : ContinuousOn (fun x : ℝ => x) (Icc a b) := by
    intro x _
    apply Metric.continuousWithinAt_iff.mpr
    intro ε hε
    exact ⟨ε, hε, fun _ _ hx => hx⟩

  obtain ⟨c, hc, heq⟩ := cauchy_mean_value f (fun x => x) df (fun _ => 1)
    a b hab hf hid hd (fun x _ => hasDerivAt_identity x)
  refine ⟨c, hc, (eq_div_iff (sub_ne_zero.mpr (ne_of_gt hab))).mpr ?_⟩
  nlinarith

end MathematicalAnalysis.Chapter04
