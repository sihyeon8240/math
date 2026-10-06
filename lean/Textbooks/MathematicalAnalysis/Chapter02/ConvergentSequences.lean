import Textbooks.MathematicalAnalysis.Chapter01.MetricSpaces
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity

namespace MathematicalAnalysis.Chapter02

open Set Metric
open MathematicalAnalysis.Chapter01

variable {X : Type*} [MetricSpace X]

/-- Lemma: a finite initial segment and a bounded tail have a common bound. -/
theorem convergent_bounded (u : ℕ → X) (p : X) (h : Filter.Tendsto u Filter.atTop (nhds p)) :
    Bornology.IsBounded (range u) := by
  rw [Metric.tendsto_atTop] at h
  apply (isBounded_iff (range u)).mpr
  intro _

  obtain ⟨N, hN⟩ := h 1 zero_lt_one

  let R := 1 + ∑ n ∈ Finset.range N, dist (u n) p

  have hsum : 0 ≤ ∑ n ∈ Finset.range N, dist (u n) p :=
    Finset.sum_nonneg (fun n _ => dist_nonneg)

  refine ⟨p, R, by
    dsimp [R]
    linarith, ?_⟩
  rintro x ⟨n, rfl⟩
  change dist (u n) p < R
  by_cases hn : n < N

  · have hle := Finset.single_le_sum (f := fun n => dist (u n) p)
      (fun n _ => dist_nonneg) (Finset.mem_range.mpr hn)
    dsimp [R]
    linarith

  · have htail := hN n (Nat.le_of_not_gt hn)
    dsimp [R]
    linarith

/-- Lemma: two distinct limits contradict the triangle inequality. -/
theorem limit_unique (u : ℕ → X) (p q : X)
    (hp : Filter.Tendsto u Filter.atTop (nhds p))
    (hq : Filter.Tendsto u Filter.atTop (nhds q)) : p = q := by
  rw [Metric.tendsto_atTop] at hp hq
  by_contra hne

  have hd : 0 < dist p q := dist_pos.mpr hne

  obtain ⟨N, hN⟩ := hp (dist p q / 2) (half_pos hd)
  obtain ⟨M, hM⟩ := hq (dist p q / 2) (half_pos hd)

  have hn := hN (max N M) (le_max_left _ _)

  have hm := hM (max N M) (le_max_right _ _)

  have ht := dist_triangle p (u (max N M)) q

  rw [dist_comm p (u (max N M))] at ht
  linarith

/-- Proposition: a convergent sequence is bounded and has a unique limit. -/
theorem convergent_properties (u : ℕ → X) (p : X) (hp : Filter.Tendsto u Filter.atTop (nhds p)) :
    Bornology.IsBounded (range u) ∧ ∀ q : X, Filter.Tendsto u Filter.atTop (nhds q) → p = q := by
  exact ⟨convergent_bounded u p hp, fun q hq => limit_unique u p q hp hq⟩

open Filter
open scoped Topology

/-- Lemma: real convergence has the epsilon characterization with a strict index bound. -/
theorem real_tendsto_iff (u : ℕ → ℝ) (a : ℝ) :
    Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n > N, |u n - a| < ε := by
  simpa only [Real.dist_eq] using (Metric.tendsto_atTop' (u := u) (a := a))

/-- Lemma: a real sequence is bounded exactly when all its terms have a strict absolute bound. -/
theorem real_bounded_iff (u : ℕ → ℝ) :
    Bornology.IsBounded (range u) ↔ ∃ C > 0, ∀ n, |u n| < C := by
  constructor

  · intro h
    obtain ⟨p, r, hr, hs⟩ := (isBounded_iff (range u)).mp h ⟨0⟩
    refine ⟨r + |p|, by linarith [abs_nonneg p], ?_⟩
    intro n
    have hn : |u n - p| < r := hs (mem_range_self n)
    have ht : |u n| ≤ |u n - p| + |p| := by
      simpa only [sub_add_cancel] using abs_add_le (u n - p) p
    linarith

  · rintro ⟨C, hC, hu⟩
    apply (isBounded_iff (range u)).mpr
    intro _
    refine ⟨0, C, hC, ?_⟩
    rintro x ⟨n, rfl⟩
    simpa only [mem_ball, Real.dist_eq, sub_zero] using hu n

/-- Lemma: a constant real sequence converges to its value. -/
theorem real_tendsto_const (a : ℝ) : Tendsto (fun _ : ℕ => a) atTop (𝓝 a) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  exact ⟨0, fun _ _ => by simpa only [dist_self] using hε⟩

/-- Theorem: limits commute with addition of real sequences. -/
theorem real_tendsto_add (u v : ℕ → ℝ) (a b : ℝ)
    (hu : Tendsto u atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 b)) :
    Tendsto (fun n => u n + v n) atTop (𝓝 (a + b)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hu (ε / 2) (half_pos hε)
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hv (ε / 2) (half_pos hε)
  refine ⟨max N M, ?_⟩
  intro n hn
  have hx := hN n ((le_max_left _ _).trans hn)
  have hy := hM n ((le_max_right _ _).trans hn)
  rw [Real.dist_eq] at hx hy ⊢
  have hbound : |u n + v n - (a + b)| ≤ |u n - a| + |v n - b| := by
    rw [show u n + v n - (a + b) = (u n - a) + (v n - b) by ring]
    exact abs_add_le _ _
  linarith

/-- Theorem: limits commute with multiplication of real sequences. -/
theorem real_tendsto_mul (u v : ℕ → ℝ) (a b : ℝ)
    (hu : Tendsto u atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 b)) :
    Tendsto (fun n => u n * v n) atTop (𝓝 (a * b)) := by
  obtain ⟨C, hC, hbound⟩ := (real_bounded_iff u).mp (convergent_bounded u a hu)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ := ε / (2 * (|b| + C + 1))
  have hden : 0 < 2 * (|b| + C + 1) := by linarith [abs_nonneg b]
  have hδ : 0 < δ := div_pos hε hden
  have hδε : δ * (2 * (|b| + C + 1)) = ε := div_mul_cancel₀ ε hden.ne'

  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hu δ hδ
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hv δ hδ
  refine ⟨max N M, ?_⟩
  intro n hn
  have hx := hN n ((le_max_left _ _).trans hn)
  have hy := hM n ((le_max_right _ _).trans hn)
  rw [Real.dist_eq] at hx hy ⊢
  have hcalc : u n * v n - a * b = (u n - a) * b + u n * (v n - b) := by ring
  have hsum := abs_add_le ((u n - a) * b) (u n * (v n - b))
  rw [← hcalc, abs_mul, abs_mul] at hsum
  have hleft := mul_le_mul_of_nonneg_right hx.le (abs_nonneg b)
  have hright := mul_le_mul (hbound n).le hy.le (abs_nonneg _) hC.le
  nlinarith

/-- Theorem: a constant factor may be passed through a real limit. -/
theorem real_tendsto_const_mul (u : ℕ → ℝ) (a c : ℝ)
    (hu : Tendsto u atTop (𝓝 a)) :
    Tendsto (fun n => c * u n) atTop (𝓝 (c * a)) :=
  real_tendsto_mul (fun _ => c) u c a (real_tendsto_const c) hu

/-- Theorem: reciprocals converge when all denominators and the limit are nonzero. -/
theorem real_tendsto_inv (u : ℕ → ℝ) (a : ℝ)
    (hu : Tendsto u atTop (𝓝 a)) (hu0 : ∀ n, u n ≠ 0) (ha : a ≠ 0) :
    Tendsto (fun n => 1 / u n) atTop (𝓝 (1 / a)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have ha' : 0 < |a| := abs_pos.mpr ha
  let δ := min (|a| / 2) (ε * |a| ^ 2 / 2)
  have hδ : 0 < δ := lt_min (half_pos ha') (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hu δ hδ
  refine ⟨N, ?_⟩
  intro n hn
  have hd : |u n - a| < δ := hN n hn
  have hsmall := hd.trans_le (min_le_left _ _)
  have herror := hd.trans_le (min_le_right _ _)
  have htriangle : |a| ≤ |a - u n| + |u n| := by
    simpa only [sub_add_cancel] using abs_add_le (a - u n) (u n)
  rw [abs_sub_comm a (u n)] at htriangle
  have hlower : |a| / 2 < |u n| := by linarith
  have hprod : 0 < |u n| * |a| := mul_pos (abs_pos.mpr (hu0 n)) ha'

  rw [Real.dist_eq, one_div, one_div, inv_sub_inv (hu0 n) ha,
    abs_div, abs_mul, abs_sub_comm a (u n), div_lt_iff₀ hprod]
  have hmul := mul_lt_mul_of_pos_right hlower ha'
  nlinarith

/-- Theorem: a sequence between two sequences with the same limit has that limit. -/
theorem real_tendsto_squeeze (u v w : ℕ → ℝ) (a : ℝ)
    (huv : ∀ n, u n ≤ v n) (hvw : ∀ n, v n ≤ w n)
    (hu : Tendsto u atTop (𝓝 a)) (hw : Tendsto w atTop (𝓝 a)) :
    Tendsto v atTop (𝓝 a) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hu ε hε
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hw ε hε
  refine ⟨max N M, ?_⟩
  intro n hn
  have hx : |u n - a| < ε := hN n ((le_max_left _ _).trans hn)
  have hz : |w n - a| < ε := hM n ((le_max_right _ _).trans hn)
  rw [Real.dist_eq, abs_lt]
  obtain ⟨hx', _⟩ := abs_lt.mp hx
  obtain ⟨_, hz'⟩ := abs_lt.mp hz
  constructor <;> linarith [huv n, hvw n]

end MathematicalAnalysis.Chapter02
