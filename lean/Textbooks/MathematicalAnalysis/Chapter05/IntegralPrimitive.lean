import Textbooks.MathematicalAnalysis.Chapter05.Subintervals
import Textbooks.MathematicalAnalysis.Chapter05.ContinuousIntegrability
import Textbooks.MathematicalAnalysis.Chapter04.DerivativeLimits

namespace MathematicalAnalysis.Chapter05

open Set Metric BoxIntegral

noncomputable section

/-- Definition: the integral over a nondecreasing pair of endpoints, with
value zero on a degenerate interval. -/
def segmentIntegral (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  if hab : a < b then riemannIntegral (intervalBox a b hab) f else 0

/-- Definition: the indefinite integral with a fixed lower endpoint. -/
def integralPrimitive (a : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun x => segmentIntegral a x f

/-- Lemma: a degenerate interval has integral zero. -/
theorem segmentIntegral_self (a : ℝ) (f : ℝ → ℝ) : segmentIntegral a a f = 0 := by
  simp only [segmentIntegral, lt_self_iff_false, ↓reduceDIte]

/-- Lemma: closed subintervals give smaller reversed boxes. -/
theorem intervalBox_le (a b x y : ℝ) (hab : a < b) (hxy : x < y)
    (hax : a ≤ x) (hyb : y ≤ b) : intervalBox x y hxy ≤ intervalBox a b hab := by
  apply Box.le_iff_bounds.mpr
  exact ⟨fun _ => neg_le_neg hyb, fun _ => neg_le_neg hax⟩

/-- Lemma: interval additivity includes degenerate subintervals. -/
theorem segmentIntegral_add (a b x y z : ℝ) (hab : a < b)
    (hax : a ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hzb : z ≤ b)
    (f : ℝ → ℝ) (hf : RiemannIntegrable (intervalBox a b hab) f) :
    segmentIntegral x z f = segmentIntegral x y f + segmentIntegral y z f := by
  rcases hxy.eq_or_lt with h | hxy
  · subst y
    rw [segmentIntegral_self, zero_add]
  rcases hyz.eq_or_lt with h | hyz
  · subst z
    rw [segmentIntegral_self, add_zero]
  simp only [segmentIntegral, hxy, hyz, hxy.trans hyz, ↓reduceDIte]
  exact riemannIntegral_split x y z hxy hyz f
    (riemannIntegrable_subinterval f (intervalBox_le a b x z hab (hxy.trans hyz) hax hzb) hf)

/-- Lemma: an absolute bound controls integrals over every closed subinterval. -/
theorem segmentIntegral_abs_le (a b x y : ℝ) (hab : a < b)
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y)
    (f : ℝ → ℝ) (hf : RiemannIntegrable (intervalBox a b hab) f)
    (C : ℝ) (_hC : 0 ≤ C) (hbound : ∀ t ∈ Icc a b, |f t| ≤ C) :
    |segmentIntegral x y f| ≤ C * (y - x) := by
  rcases hxy.eq_or_lt with h | hxy
  · subst y
    simp only [segmentIntegral_self, abs_zero, sub_self, mul_zero, le_refl]
  simp only [segmentIntegral, hxy, ↓reduceDIte]
  have hs := riemannIntegrable_subinterval f (intervalBox_le a b x y hab hxy hx.1 hy.2) hf
  have hb : ∀ t ∈ Icc (-(intervalBox x y hxy).upper ()) (-(intervalBox x y hxy).lower ()),
      |f t| ≤ C := by
    intro t ht
    simp only [intervalBox, neg_neg] at ht
    exact hbound t ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩
  simpa only [cellLength, intervalBox, neg_sub_neg] using
    riemannIntegral_abs_le (intervalBox x y hxy) f hs C hb

/-- Theorem: a bounded integrable function has a Lipschitz indefinite integral. -/
theorem integralPrimitive_difference_bound (a b : ℝ) (hab : a < b)
    (f : ℝ → ℝ) (hf : RiemannIntegrable (intervalBox a b hab) f)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ t ∈ Icc a b, |f t| ≤ C)
    (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |integralPrimitive a f x - integralPrimitive a f y| ≤ C * |x - y| := by
  rcases le_total x y with hxy | hyx
  · have he := segmentIntegral_add a b a x y hab le_rfl hx.1 hxy hy.2 f hf
    have hb := segmentIntegral_abs_le a b x y hab hx hy hxy f hf C hC hbound
    dsimp only [integralPrimitive]
    rw [he, show segmentIntegral a x f - (segmentIntegral a x f + segmentIntegral x y f) =
      -segmentIntegral x y f by ring, abs_neg, abs_of_nonpos (sub_nonpos.mpr hxy)]
    convert hb using 1
    ring
  · have he := segmentIntegral_add a b a y x hab le_rfl hy.1 hyx hx.2 f hf
    have hb := segmentIntegral_abs_le a b y x hab hy hx hyx f hf C hC hbound
    dsimp only [integralPrimitive]
    rw [he, add_sub_cancel_left, abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact hb

/-- Theorem: the indefinite integral of an integrable function is continuous. -/
theorem integralPrimitive_continuousOn (a b : ℝ) (hab : a < b)
    (f : ℝ → ℝ) (hf : RiemannIntegrable (intervalBox a b hab) f) :
    ContinuousOn (integralPrimitive a f) (Icc a b) := by
  obtain ⟨C, hC, hb⟩ := absolute_bound (intervalBox a b hab) f hf.1
  simp only [intervalBox, neg_neg] at hb
  intro x hx
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  refine ⟨ε / (C + 1), div_pos hε (by linarith), ?_⟩
  intro y hy hdist
  have he := integralPrimitive_difference_bound a b hab f hf C hC.le hb y x hy hx
  change |y - x| < ε / (C + 1) at hdist
  change |integralPrimitive a f y - integralPrimitive a f x| < ε
  have hh := (lt_div_iff₀ (show 0 < C + 1 by linarith)).mp hdist
  nlinarith [abs_nonneg (y - x)]

/-- Lemma: integrating a constant multiplies it by the interval length. -/
theorem riemannIntegral_constant (I : Box Unit) (c : ℝ) :
    riemannIntegral I (fun _ => c) = c * cellLength I := by
  have hc : ContinuousOn (fun _ : ℝ => c) (Icc (-I.upper ()) (-I.lower ())) :=
    (Chapter03.continuous_const c).continuousOn
  apply riemannIntegral_eq_of_taggedSum I _ (continuous_riemannIntegrable I _ hc)
  intro P
  refine ⟨fun J => -J.upper (), fun J _ => ⟨le_rfl, neg_lt_neg (J.lower_lt_upper ())⟩, ?_⟩
  simp only [taggedSum, ← Finset.mul_sum, sum_cellLengths]

/-- Lemma: an integrand uniformly close to a constant has an integral close
to that constant times the interval length. -/
theorem integral_constant_error (I : Box Unit) (f : ℝ → ℝ)
    (hf : RiemannIntegrable I f) (c ε : ℝ)
    (he : ∀ t ∈ Icc (-I.upper ()) (-I.lower ()), |f t - c| ≤ ε) :
    |riemannIntegral I f - c * cellLength I| ≤ ε * cellLength I := by
  have hc := continuous_riemannIntegrable I (fun _ : ℝ => c)
    (Chapter03.continuous_const c).continuousOn
  have hh := riemannIntegrable_add I f (fun _ => -1 * c) hf
    (riemannIntegrable_const_mul I _ (-1) hc)
  have hv := riemannIntegral_linear I f (fun _ => c) 1 (-1) hf hc
  simp only [one_mul, neg_one_mul, riemannIntegral_constant] at hv hh
  have hb := riemannIntegral_abs_le I (fun t => f t + -c) hh ε (by
    intro t ht
    simpa only [sub_eq_add_neg] using he t ht)
  rw [hv] at hb
  simpa only [sub_eq_add_neg] using hb

/-- Theorem: at an interior continuity point of the integrand, the derivative
of its indefinite integral equals its value. -/
theorem integralPrimitive_hasDerivAt (a b : ℝ) (hab : a < b)
    (f : ℝ → ℝ) (hf : RiemannIntegrable (intervalBox a b hab) f)
    (x : ℝ) (hx : x ∈ Ioo a b) (hc : ContinuousAt f x) :
    HasDerivAt (integralPrimitive a f) (f x) x := by
  apply (Chapter04.hasDerivAt_iff_epsilon _ _ _).mpr
  intro ε hε
  obtain ⟨r, hr, hc⟩ := Metric.continuousAt_iff.mp hc (ε / 2) (half_pos hε)
  refine ⟨min r (min (x - a) (b - x)), lt_min hr (lt_min
    (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)), ?_⟩
  intro y hne hy
  have hyr : |y - x| < r := lt_of_lt_of_le hy (min_le_left _ _)
  have hya : |y - x| < x - a := lt_of_lt_of_le hy
    ((min_le_right _ _).trans (min_le_left _ _))
  have hyb : |y - x| < b - x := lt_of_lt_of_le hy
    ((min_le_right _ _).trans (min_le_right _ _))
  have hyI : y ∈ Icc a b := ⟨by linarith [(abs_lt.mp hya).1],
    by linarith [(abs_lt.mp hyb).2]⟩
  have he : ∀ t ∈ Icc (min x y) (max x y), |f t - f x| ≤ ε / 2 := by
    intro t ht
    have htnear : |t - x| < r := by
      rcases le_total x y with h | h
      · rw [min_eq_left h, max_eq_right h] at ht
        rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
        linarith [ht.2, (abs_lt.mp hyr).2]
      · rw [min_eq_right h, max_eq_left h] at ht
        rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]
        linarith [ht.1, (abs_lt.mp hyr).1]
    exact (hc (by simpa only [Real.dist_eq] using htnear)).le
  rcases lt_or_gt_of_ne (sub_ne_zero.mp (abs_pos.mp hne)) with hxy | hyx
  · have hs := riemannIntegrable_subinterval f (intervalBox_le a b y x hab hxy hyI.1 hx.2.le) hf
    have hb := integral_constant_error (intervalBox y x hxy) f hs (f x) (ε / 2) (by
      simpa only [intervalBox, neg_neg, min_eq_right hxy.le, max_eq_left hxy.le] using he)
    have hv := segmentIntegral_add a b a y x hab le_rfl hyI.1 hxy.le hx.2.le f hf
    simp only [segmentIntegral, hxy, ↓reduceDIte] at hv
    have hid : (integralPrimitive a f y - integralPrimitive a f x) / (y - x) - f x =
        (riemannIntegral (intervalBox y x hxy) f - f x * (x - y)) / (x - y) := by
      dsimp only [integralPrimitive, segmentIntegral]
      rw [hv]
      field_simp [sub_ne_zero.mpr hxy.ne, sub_ne_zero.mpr hxy.ne']
      ring
    rw [hid, abs_div, abs_of_pos (sub_pos.mpr hxy)]
    apply lt_of_le_of_lt ((div_le_iff₀ (sub_pos.mpr hxy)).mpr ?_) (half_lt_self hε)
    simpa only [cellLength, intervalBox, neg_sub_neg] using hb
  · have hs := riemannIntegrable_subinterval f (intervalBox_le a b x y hab hyx hx.1.le hyI.2) hf
    have hb := integral_constant_error (intervalBox x y hyx) f hs (f x) (ε / 2) (by
      simpa only [intervalBox, neg_neg, min_eq_left hyx.le, max_eq_right hyx.le] using he)
    have hv := segmentIntegral_add a b a x y hab le_rfl hx.1.le hyx.le hyI.2 f hf
    simp only [segmentIntegral, hyx, ↓reduceDIte] at hv
    have hid : (integralPrimitive a f y - integralPrimitive a f x) / (y - x) - f x =
        (riemannIntegral (intervalBox x y hyx) f - f x * (y - x)) / (y - x) := by
      dsimp only [integralPrimitive, segmentIntegral]
      rw [hv]
      field_simp [sub_ne_zero.mpr hyx.ne, sub_ne_zero.mpr hyx.ne']
      ring
    rw [hid, abs_div, abs_of_pos (sub_pos.mpr hyx)]
    apply lt_of_le_of_lt ((div_le_iff₀ (sub_pos.mpr hyx)).mpr ?_) (half_lt_self hε)
    simpa only [cellLength, intervalBox, neg_sub_neg] using hb

end

end MathematicalAnalysis.Chapter05
