import Textbooks.MathematicalAnalysis.Chapter04.MeanValue
import Mathlib.Topology.Order.LeftRightNhds

namespace MathematicalAnalysis.Chapter04

open Set Metric Filter
open scoped Topology
open MathematicalAnalysis.Chapter03

private theorem limit_combination {l : Filter ℝ} (u v : ℝ → ℝ) (a b A B : ℝ)
    (hu : Tendsto u l (𝓝 a)) (hv : Tendsto v l (𝓝 b)) :
    Tendsto (fun x => A * u x + B * v x) l (𝓝 (A * a + B * b)) := by
  have hp : Continuous (fun p : ℝ × ℝ => p.1) := by
    apply Metric.continuous_iff.mpr
    intro _ ε hε
    exact ⟨ε, hε, fun _ hx => (le_max_left _ _).trans_lt hx⟩
  have hq : Continuous (fun p : ℝ × ℝ => p.2) := by
    apply Metric.continuous_iff.mpr
    intro _ ε hε
    exact ⟨ε, hε, fun _ hx => (le_max_right _ _).trans_lt hx⟩
  have hc := continuous_add (fun p : ℝ × ℝ => A * p.1) (fun p => B * p.2)
    (continuous_mul _ _ (continuous_const A) hp)
    (continuous_mul _ _ (continuous_const B) hq)
  exact hc.continuousAt.tendsto.comp (hu.prodMk_nhds hv)

private theorem limit_abs {l : Filter ℝ} (u : ℝ → ℝ) (a : ℝ)
    (hu : Tendsto u l (𝓝 a)) : Tendsto (fun x => |u x|) l (𝓝 |a|) := by
  have hc : Continuous (fun x : ℝ => |x|) := by
    apply Metric.continuous_iff.mpr
    intro a ε hε
    refine ⟨ε, hε, ?_⟩
    intro x hx
    exact (abs_abs_sub_abs_le_abs_sub x a).trans_lt hx
  exact hc.continuousAt.tendsto.comp hu

private theorem limit_le {l : Filter ℝ} [NeBot l] (u v : ℝ → ℝ) (a b : ℝ)
    (hu : Tendsto u l (𝓝 a)) (hv : Tendsto v l (𝓝 b))
    (hle : ∀ᶠ x in l, u x ≤ v x) : a ≤ b := by
  by_contra hn
  have hab : b < a := lt_of_not_ge hn
  have hε : 0 < (a - b) / 3 := by positivity
  have h₁ := Metric.tendsto_nhds.mp hu ((a - b) / 3) hε
  have h₂ := Metric.tendsto_nhds.mp hv ((a - b) / 3) hε
  obtain ⟨x, hx, hy, hxy⟩ := (h₁.and (h₂.and hle)).exists
  rw [Real.dist_eq, abs_lt] at hx hy
  linarith

private theorem increment_bound (S : Set ℝ)
    (hS : ∀ x ∈ S, ∀ y ∈ S, Icc x y ⊆ S)
    (f g df dg : ℝ → ℝ) (hd : ∀ x ∈ S, HasDerivAt f (df x) x)
    (he : ∀ x ∈ S, HasDerivAt g (dg x) x) (h0 : ∀ x ∈ S, dg x ≠ 0)
    (L η t : ℝ) (hη : 0 < η)
    (hnear : ∀ x ∈ S, x < t → |df x / dg x - L| < η)
    (x y : ℝ) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hyt : y < t) :
    |(f y - f x) - L * (g y - g x)| ≤ η * |g y - g x| := by
  have hf : ContinuousOn f (Icc x y) := fun z hz =>
    (continuousAt_of_hasDerivAt f (df z) z (hd z (hS x hx y hy hz))).continuousWithinAt
  have hg : ContinuousOn g (Icc x y) := fun z hz =>
    (continuousAt_of_hasDerivAt g (dg z) z (he z (hS x hx y hy hz))).continuousWithinAt
  have hdiff : g y - g x ≠ 0 := by
    intro hn
    obtain ⟨c, hc, hzero⟩ := rolle g dg x y hxy hg
      (fun z hz => he z (hS x hx y hy ⟨hz.1.le, hz.2.le⟩)) (sub_eq_zero.mp hn).symm
    exact h0 c (hS x hx y hy ⟨hc.1.le, hc.2.le⟩) hzero
  obtain ⟨c, hc, hmean⟩ := cauchy_mean_value f g df dg x y hxy hf hg
    (fun z hz => hd z (hS x hx y hy ⟨hz.1.le, hz.2.le⟩))
    (fun z hz => he z (hS x hx y hy ⟨hz.1.le, hz.2.le⟩))
  have hcs := hS x hx y hy ⟨hc.1.le, hc.2.le⟩
  have hratio : (f y - f x) / (g y - g x) = df c / dg c := by
    apply (div_eq_div_iff hdiff (h0 c hcs)).mpr
    simpa only [mul_comm] using hmean
  have hsmall := hnear c hcs (hc.2.trans hyt)
  rw [← hratio] at hsmall
  have hid : (f y - f x) - L * (g y - g x) =
      ((f y - f x) / (g y - g x) - L) * (g y - g x) := by
    field_simp
  rw [hid, abs_mul]
  exact mul_le_mul hsmall.le le_rfl (abs_nonneg _) hη.le

private theorem eventually_denominator_ne {l : Filter ℝ} [NeBot l] (S : Set ℝ)
    (hbasis : ∀ p : ℝ → Prop, (∀ᶠ x in l, p x) ↔
      ∃ t ∈ S, ∀ x ∈ S, x < t → p x)
    (hS : ∀ x ∈ S, ∀ y ∈ S, Icc x y ⊆ S) (g dg : ℝ → ℝ)
    (hd : ∀ x ∈ S, HasDerivAt g (dg x) x) (h0 : ∀ x ∈ S, dg x ≠ 0) :
    ∀ᶠ x in l, g x ≠ 0 := by
  by_cases hz : ∃ z ∈ S, g z = 0
  · obtain ⟨z, hzS, hgz⟩ := hz
    apply (hbasis _).mpr
    refine ⟨z, hzS, ?_⟩
    intro x hx hxz hgx
    have hc : ContinuousOn g (Icc x z) := fun y hy =>
      (continuousAt_of_hasDerivAt g (dg y) y (hd y (hS x hx z hzS hy))).continuousWithinAt
    obtain ⟨c, hcI, hdc⟩ := rolle g dg x z hxz hc
      (fun y hy => hd y (hS x hx z hzS ⟨hy.1.le, hy.2.le⟩)) (hgx.trans hgz.symm)
    exact h0 c (hS x hx z hzS ⟨hcI.1.le, hcI.2.le⟩) hdc
  · obtain ⟨t, ht, _⟩ := (hbasis (fun _ => True)).mp (Eventually.of_forall (fun _ => trivial))
    exact (hbasis _).mpr ⟨t, ht, fun x hx _ hgx => hz ⟨x, hx, hgx⟩⟩

private theorem lhopital_zero {l : Filter ℝ} [NeBot l] (S : Set ℝ)
    (hbasis : ∀ p : ℝ → Prop, (∀ᶠ x in l, p x) ↔
      ∃ t ∈ S, ∀ x ∈ S, x < t → p x)
    (hS : ∀ x ∈ S, ∀ y ∈ S, Icc x y ⊆ S) (f g df dg : ℝ → ℝ) (L : ℝ)
    (hd : ∀ x ∈ S, HasDerivAt f (df x) x)
    (he : ∀ x ∈ S, HasDerivAt g (dg x) x) (h0 : ∀ x ∈ S, dg x ≠ 0)
    (hr : Tendsto (fun x => df x / dg x) l (𝓝 L))
    (hf : Tendsto f l (𝓝 0)) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x => f x / g x) l (𝓝 L) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨t, ht, hnear⟩ := (hbasis _).mp
    (Metric.tendsto_nhds.mp hr (ε / 2) (half_pos hε))
  have hn := eventually_denominator_ne S hbasis hS g dg he h0
  have hregion : ∀ᶠ x in l, x ∈ S ∧ x < t :=
    (hbasis _).mpr ⟨t, ht, fun x hx hxt => ⟨hx, hxt⟩⟩
  filter_upwards [hregion, hn] with x hx hnx
  have hsmall : |f x - L * g x| ≤ (ε / 2) * |g x| := by
    have hy : ∀ᶠ y in l, y ∈ S ∧ y < x :=
      (hbasis _).mpr ⟨x, hx.1, fun y hy hyx => ⟨hy, hyx⟩⟩
    have hbound : ∀ᶠ y in l,
        |(f x - f y) - L * (g x - g y)| ≤ (ε / 2) * |g x - g y| := by
      filter_upwards [hy] with y hy
      exact increment_bound S hS f g df dg hd he h0 L (ε / 2) t
        (half_pos hε) hnear y x hy.1 hx.1 hy.2 hx.2
    have hfx : Tendsto (fun y => f x - f y) l (𝓝 (f x)) := by
      simpa only [one_mul, neg_one_mul, neg_zero, add_zero, sub_eq_add_neg] using
        limit_combination (fun _ => f x) f (f x) 0 1 (-1) tendsto_const_nhds hf
    have hgx : Tendsto (fun y => g x - g y) l (𝓝 (g x)) := by
      simpa only [one_mul, neg_one_mul, neg_zero, add_zero, sub_eq_add_neg] using
        limit_combination (fun _ => g x) g (g x) 0 1 (-1) tendsto_const_nhds hg
    have hleft := limit_abs _ _ (limit_combination _ _ _ _ 1 (-L) hfx hgx)
    have hright := limit_combination (fun y => |g x - g y|) (fun _ => (0 : ℝ))
      |g x| 0 (ε / 2) 0 (limit_abs _ _ hgx) tendsto_const_nhds
    simp only [one_mul, neg_mul, ← sub_eq_add_neg] at hleft
    simp only [zero_mul, add_zero] at hright
    exact limit_le _ _ _ _ hleft hright hbound
  rw [Real.dist_eq, show f x / g x - L = (f x - L * g x) / g x by field_simp,
    abs_div, div_lt_iff₀ (abs_pos.mpr hnx)]
  exact hsmall.trans_lt (mul_lt_mul_of_pos_right (half_lt_self hε) (abs_pos.mpr hnx))

private theorem lhopital_infinity {l : Filter ℝ} [NeBot l] (S : Set ℝ)
    (hbasis : ∀ p : ℝ → Prop, (∀ᶠ x in l, p x) ↔
      ∃ t ∈ S, ∀ x ∈ S, x < t → p x)
    (hS : ∀ x ∈ S, ∀ y ∈ S, Icc x y ⊆ S) (f g df dg : ℝ → ℝ) (L : ℝ)
    (hd : ∀ x ∈ S, HasDerivAt f (df x) x)
    (he : ∀ x ∈ S, HasDerivAt g (dg x) x) (h0 : ∀ x ∈ S, dg x ≠ 0)
    (hr : Tendsto (fun x => df x / dg x) l (𝓝 L)) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x / g x) l (𝓝 L) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨t, ht, hnear⟩ := (hbasis _).mp
    (Metric.tendsto_nhds.mp hr (ε / 4) (by positivity))
  have hy : ∀ᶠ y in l, y ∈ S ∧ y < t :=
    (hbasis _).mpr ⟨t, ht, fun y hy hyt => ⟨hy, hyt⟩⟩
  obtain ⟨y, hyS, hyt⟩ := hy.exists
  let B := ε / 4 * |g y| + |f y - L * g y|
  have hregion : ∀ᶠ x in l, x ∈ S ∧ x < y :=
    (hbasis _).mpr ⟨y, hyS, fun x hx hxy => ⟨hx, hxy⟩⟩
  have hlarge : ∀ᶠ x in l, max 1 (4 * B / ε) + 1 ≤ g x :=
    (tendsto_atTop.mp hg) (max 1 (4 * B / ε) + 1)
  filter_upwards [hregion, hlarge] with x hx hgx
  have hgpos : 0 < g x := by linarith [le_max_left (1 : ℝ) (4 * B / ε)]
  have hB : B < ε / 4 * g x := by
    have hlt : 4 * B / ε < g x := by linarith [le_max_right (1 : ℝ) (4 * B / ε)]
    have hmul := (div_lt_iff₀ hε).mp hlt
    nlinarith
  have hinc := increment_bound S hS f g df dg hd he h0 L (ε / 4) t
    (by positivity) hnear x y hx.1 hyS hx.2 hyt
  have hnum : |f x - L * g x| < ε * g x := by
    have ht := abs_add_le ((f x - L * g x) - (f y - L * g y)) (f y - L * g y)
    rw [sub_add_cancel] at ht
    have hid : (f y - f x) - L * (g y - g x) =
        -((f x - L * g x) - (f y - L * g y)) := by ring
    rw [hid, abs_neg] at hinc
    have hgabs := abs_add_le (g y) (-g x)
    rw [abs_neg, ← sub_eq_add_neg] at hgabs
    rw [abs_of_pos hgpos] at hgabs
    have hmul := mul_le_mul_of_nonneg_left hgabs (by positivity : 0 ≤ ε / 4)
    dsimp only [B] at hB
    nlinarith
  rw [Real.dist_eq, show f x / g x - L = (f x - L * g x) / g x by field_simp,
    abs_div, abs_of_pos hgpos, div_lt_iff₀ hgpos]
  exact hnum

private theorem right_basis (a b : ℝ) (hab : a < b) (p : ℝ → Prop) :
    (∀ᶠ x in 𝓝[>] a, p x) ↔ ∃ t ∈ Ioo a b, ∀ x ∈ Ioo a b, x < t → p x := by
  rw [(nhdsGT_basis a).eventually_iff]
  constructor
  · rintro ⟨r, hr, hp⟩
    let t := (a + min r b) / 2
    have hat : a < t := by dsimp [t]; linarith [lt_min hr hab]
    have htr : t < r := by dsimp [t]; linarith [lt_min hr hab, min_le_left r b]
    have htb : t < b := by dsimp [t]; linarith [lt_min hr hab, min_le_right r b]
    exact ⟨t, ⟨hat, htb⟩, fun x hx hxt => hp ⟨hx.1, hxt.trans htr⟩⟩
  · rintro ⟨t, ht, hp⟩
    exact ⟨t, ht.1, fun x hx => hp x ⟨hx.1, hx.2.trans ht.2⟩ hx.2⟩

private theorem atBot_basis (b : ℝ) (p : ℝ → Prop) :
    (∀ᶠ x in atBot, p x) ↔ ∃ t ∈ Iio b, ∀ x ∈ Iio b, x < t → p x := by
  rw [eventually_atBot]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨min r b - 1, (show min r b - 1 < b by linarith [min_le_right r b]), ?_⟩
    intro x _ hxt
    exact hr x (by linarith [min_le_left r b])
  · rintro ⟨t, ht, hp⟩
    change t < b at ht
    refine ⟨t - 1, ?_⟩
    intro x hx
    exact hp x (show x < b by linarith) (by linarith)

/-- Theorem: L'Hôpital's rule for a finite left endpoint, approached from the right,
in the zero-over-zero case. -/
theorem lhopital_zero_right (f g df dg : ℝ → ℝ) (a b L : ℝ) (hab : a < b)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (df x) x)
    (he : ∀ x ∈ Ioo a b, HasDerivAt g (dg x) x) (h0 : ∀ x ∈ Ioo a b, dg x ≠ 0)
    (hr : Tendsto (fun x => df x / dg x) (𝓝[>] a) (𝓝 L))
    (hf : Tendsto f (𝓝[>] a) (𝓝 0)) (hg : Tendsto g (𝓝[>] a) (𝓝 0)) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) (𝓝 L) :=
  lhopital_zero (Ioo a b) (right_basis a b hab)
    (fun _x hx _y hy _z hz => ⟨hx.1.trans_le hz.1, hz.2.trans_lt hy.2⟩)
    f g df dg L hd he h0 hr hf hg

/-- Theorem: L'Hôpital's rule at a finite left endpoint when the denominator
tends to positive infinity; no limit of the numerator is required. -/
theorem lhopital_infinity_right (f g df dg : ℝ → ℝ) (a b L : ℝ) (hab : a < b)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (df x) x)
    (he : ∀ x ∈ Ioo a b, HasDerivAt g (dg x) x) (h0 : ∀ x ∈ Ioo a b, dg x ≠ 0)
    (hr : Tendsto (fun x => df x / dg x) (𝓝[>] a) (𝓝 L))
    (hg : Tendsto g (𝓝[>] a) atTop) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) (𝓝 L) :=
  lhopital_infinity (Ioo a b) (right_basis a b hab)
    (fun _x hx _y hy _z hz => ⟨hx.1.trans_le hz.1, hz.2.trans_lt hy.2⟩)
    f g df dg L hd he h0 hr hg

/-- Theorem: L'Hôpital's zero-over-zero rule when the left endpoint is negative infinity. -/
theorem lhopital_zero_atBot (f g df dg : ℝ → ℝ) (b L : ℝ)
    (hd : ∀ x ∈ Iio b, HasDerivAt f (df x) x)
    (he : ∀ x ∈ Iio b, HasDerivAt g (dg x) x) (h0 : ∀ x ∈ Iio b, dg x ≠ 0)
    (hr : Tendsto (fun x => df x / dg x) atBot (𝓝 L))
    (hf : Tendsto f atBot (𝓝 0)) (hg : Tendsto g atBot (𝓝 0)) :
    Tendsto (fun x => f x / g x) atBot (𝓝 L) :=
  lhopital_zero (Iio b) (atBot_basis b)
    (fun _x _ _y hy _z hz => hz.2.trans_lt hy) f g df dg L hd he h0 hr hf hg

/-- Theorem: L'Hôpital's rule at negative infinity when the denominator tends
to positive infinity. -/
theorem lhopital_infinity_atBot (f g df dg : ℝ → ℝ) (b L : ℝ)
    (hd : ∀ x ∈ Iio b, HasDerivAt f (df x) x)
    (he : ∀ x ∈ Iio b, HasDerivAt g (dg x) x) (h0 : ∀ x ∈ Iio b, dg x ≠ 0)
    (hr : Tendsto (fun x => df x / dg x) atBot (𝓝 L)) (hg : Tendsto g atBot atTop) :
    Tendsto (fun x => f x / g x) atBot (𝓝 L) :=
  lhopital_infinity (Iio b) (atBot_basis b)
    (fun _x _ _y hy _z hz => hz.2.trans_lt hy) f g df dg L hd he h0 hr hg

/-- Corollary: the zero-over-zero rule also applies when the upper endpoint is unbounded. -/
theorem lhopital_zero_right_unbounded (f g df dg : ℝ → ℝ) (a L : ℝ)
    (hd : ∀ x ∈ Ioi a, HasDerivAt f (df x) x)
    (he : ∀ x ∈ Ioi a, HasDerivAt g (dg x) x) (h0 : ∀ x ∈ Ioi a, dg x ≠ 0)
    (hr : Tendsto (fun x => df x / dg x) (𝓝[>] a) (𝓝 L))
    (hf : Tendsto f (𝓝[>] a) (𝓝 0)) (hg : Tendsto g (𝓝[>] a) (𝓝 0)) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) (𝓝 L) :=
  lhopital_zero_right f g df dg a (a + 1) L (by linarith)
    (fun x hx => hd x hx.1) (fun x hx => he x hx.1) (fun x hx => h0 x hx.1) hr hf hg

/-- Corollary: the infinite-denominator rule also applies with an unbounded upper endpoint. -/
theorem lhopital_infinity_right_unbounded (f g df dg : ℝ → ℝ) (a L : ℝ)
    (hd : ∀ x ∈ Ioi a, HasDerivAt f (df x) x)
    (he : ∀ x ∈ Ioi a, HasDerivAt g (dg x) x) (h0 : ∀ x ∈ Ioi a, dg x ≠ 0)
    (hr : Tendsto (fun x => df x / dg x) (𝓝[>] a) (𝓝 L))
    (hg : Tendsto g (𝓝[>] a) atTop) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) (𝓝 L) :=
  lhopital_infinity_right f g df dg a (a + 1) L (by linarith)
    (fun x hx => hd x hx.1) (fun x hx => he x hx.1) (fun x hx => h0 x hx.1) hr hg

/-- Corollary: L'Hôpital's zero-over-zero rule on the entire real line at negative infinity. -/
theorem lhopital_zero_atBot_unbounded (f g df dg : ℝ → ℝ) (L : ℝ)
    (hd : ∀ x, HasDerivAt f (df x) x)
    (he : ∀ x, HasDerivAt g (dg x) x) (h0 : ∀ x, dg x ≠ 0)
    (hr : Tendsto (fun x => df x / dg x) atBot (𝓝 L))
    (hf : Tendsto f atBot (𝓝 0)) (hg : Tendsto g atBot (𝓝 0)) :
    Tendsto (fun x => f x / g x) atBot (𝓝 L) :=
  lhopital_zero_atBot f g df dg 0 L (fun x _ => hd x) (fun x _ => he x)
    (fun x _ => h0 x) hr hf hg

/-- Corollary: the infinite-denominator rule on the entire real line at negative infinity. -/
theorem lhopital_infinity_atBot_unbounded (f g df dg : ℝ → ℝ) (L : ℝ)
    (hd : ∀ x, HasDerivAt f (df x) x)
    (he : ∀ x, HasDerivAt g (dg x) x) (h0 : ∀ x, dg x ≠ 0)
    (hr : Tendsto (fun x => df x / dg x) atBot (𝓝 L)) (hg : Tendsto g atBot atTop) :
    Tendsto (fun x => f x / g x) atBot (𝓝 L) :=
  lhopital_infinity_atBot f g df dg 0 L (fun x _ => hd x) (fun x _ => he x)
    (fun x _ => h0 x) hr hg

end MathematicalAnalysis.Chapter04
