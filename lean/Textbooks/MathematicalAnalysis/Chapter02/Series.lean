import Textbooks.MathematicalAnalysis.Chapter02.CauchySequences
import Textbooks.MathematicalAnalysis.Chapter02.MonotoneSequences
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals

namespace MathematicalAnalysis.Chapter02

open Set Metric Filter Finset
open scoped Topology

/-- Definition: partial sums use the standard zero-based indexing convention. -/
def partialSums (u : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ range n, u k

/-- Definition: a series has sum `a` when its ordered partial sums converge to `a`.
This includes conditional convergence, unlike unordered `HasSum` on real families. -/
def HasSeriesSum (u : ℕ → ℝ) (a : ℝ) : Prop := Tendsto (partialSums u) atTop (𝓝 a)

/-- Definition: a series converges when its partial sums have a real limit. -/
def SeriesConverges (u : ℕ → ℝ) : Prop := ∃ a, HasSeriesSum u a

/-- Definition: absolute convergence is convergence of the series of absolute values. -/
def AbsolutelyConverges (u : ℕ → ℝ) : Prop := SeriesConverges (fun n => |u n|)

/-- Lemma: the increment of a partial sum is the next summand. -/
theorem partialSums_succ (u : ℕ → ℝ) (n : ℕ) :
    partialSums u (n + 1) = partialSums u n + u n := sum_range_succ u n

/-- Lemma: an interval sum is a difference of partial sums. -/
theorem sum_Ico_eq_partialSums_sub (u : ℕ → ℝ) (n m : ℕ) (hnm : n ≤ m) :
    ∑ k ∈ Ico n m, u k = partialSums u m - partialSums u n := by
  exact sum_Ico_eq_sub _ hnm

/-- Theorem: the Cauchy tail condition characterizes convergence of a real series. -/
theorem seriesConverges_iff_cauchy_tails (u : ℕ → ℝ) :
    SeriesConverges u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ n,
      |∑ k ∈ Ico n (m + 1), u k| < ε := by
  change (∃ a, Tendsto (partialSums u) atTop (𝓝 a)) ↔ _
  rw [real_converges_iff_cauchy, Metric.cauchySeq_iff]
  constructor

  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, ?_⟩
    intro n hn m hmn
    rw [sum_Ico_eq_partialSums_sub u n (m + 1) (by omega)]
    exact hN (m + 1) (by omega) n hn

  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, ?_⟩
    intro m hm n hn
    rcases lt_trichotomy n m with hnm | hnm | hmn

    · have ht := hN n hn (m - 1) (by omega)
      rw [Nat.sub_add_cancel (by omega), sum_Ico_eq_partialSums_sub u n m hnm.le] at ht
      exact ht

    · subst m
      simpa only [dist_self] using hε

    · have ht := hN m hm (n - 1) (by omega)
      rw [Nat.sub_add_cancel (by omega), sum_Ico_eq_partialSums_sub u m n hmn.le] at ht
      simpa only [Real.dist_eq, abs_sub_comm] using ht

/-- Theorem: the terms of a convergent series tend to zero. -/
theorem seriesConverges_tendsto_zero (u : ℕ → ℝ) (hu : SeriesConverges u) :
    Tendsto u atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := (seriesConverges_iff_cauchy_tails u).mp hu ε hε
  refine ⟨N, ?_⟩
  intro n hn
  have ht := hN n hn n le_rfl
  simpa only [Nat.Ico_succ_singleton, Finset.sum_singleton,
    Real.dist_eq, sub_zero] using ht

/-- Lemma: nonnegative terms give nondecreasing partial sums. -/
theorem partialSums_monotone (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) :
    Monotone (partialSums u) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [partialSums_succ]
  exact le_add_of_nonneg_right (hu n)

/-- Lemma: a nonnegative series converges exactly when its partial sums are bounded above. -/
theorem nonneg_seriesConverges_iff (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) :
    SeriesConverges u ↔ BddAbove (Set.range (partialSums u)) := by
  constructor

  · rintro ⟨a, ha⟩
    obtain ⟨C, _, hC⟩ := (real_bounded_iff _).mp (convergent_bounded _ a ha)
    refine ⟨C, ?_⟩
    rintro x ⟨n, rfl⟩
    exact (le_abs_self _).trans (hC n).le

  · intro hb
    exact ⟨sSup (Set.range (partialSums u)),
      monotone_tendsto_sSup _ (partialSums_monotone u hu) hb⟩

/-- Theorem: eventual absolute domination by a convergent series implies convergence. -/
theorem series_comparison (u v : ℕ → ℝ) (hdom : ∀ᶠ n in atTop, |u n| ≤ v n)
    (hv : SeriesConverges v) : SeriesConverges u := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp hdom
  apply (seriesConverges_iff_cauchy_tails u).mpr
  intro ε hε
  obtain ⟨N, hN⟩ := (seriesConverges_iff_cauchy_tails v).mp hv ε hε
  refine ⟨max N M, ?_⟩
  intro n hn m hmn
  have hsum : |∑ k ∈ Ico n (m + 1), u k| ≤ ∑ k ∈ Ico n (m + 1), v k := by
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro k hk
    exact hM k ((le_max_right N M).trans (hn.trans (mem_Ico.mp hk).1))

  have ht := hN n ((le_max_left _ _).trans hn) m hmn
  exact (hsum.trans (le_abs_self _)).trans_lt ht

/-- Theorem: absolute convergence implies convergence. -/
theorem absolute_convergence (u : ℕ → ℝ) (hu : AbsolutelyConverges u) :
    SeriesConverges u :=
  series_comparison u (fun n => |u n|) (Eventually.of_forall (fun _ => le_rfl)) hu

/-- Theorem: eventual domination of a divergent nonnegative series implies divergence. -/
theorem series_comparison_divergence (u v : ℕ → ℝ)
    (hdom : ∀ᶠ n in atTop, 0 ≤ v n ∧ v n ≤ u n)
    (hv : ¬ SeriesConverges v) : ¬ SeriesConverges u := by
  intro hu
  apply hv
  apply series_comparison v u _ hu
  exact hdom.mono (fun _ h => by
    rw [abs_of_nonneg h.1]
    exact h.2)

/-- Lemma: changing finitely many terms does not change convergence of an ordered series. -/
theorem seriesConverges_congr_eventually (u v : ℕ → ℝ) (huv : u =ᶠ[atTop] v) :
    SeriesConverges u ↔ SeriesConverges v := by
  have transfer (f g : ℕ → ℝ) (hfg : f =ᶠ[atTop] g) (hf : SeriesConverges f) :
      SeriesConverges g := by
    obtain ⟨M, hM⟩ := eventually_atTop.mp hfg
    apply (seriesConverges_iff_cauchy_tails g).mpr
    intro ε hε
    obtain ⟨N, hN⟩ := (seriesConverges_iff_cauchy_tails f).mp hf ε hε
    refine ⟨max N M, ?_⟩
    intro n hn m hnm
    have heq : (∑ k ∈ Ico n (m + 1), g k) = ∑ k ∈ Ico n (m + 1), f k := by
      apply sum_congr rfl
      intro k hk
      exact (hM k ((le_max_right N M).trans (hn.trans (mem_Ico.mp hk).1))).symm
    rw [heq]
    exact hN n ((le_max_left _ _).trans hn) m hnm

  exact ⟨transfer u v huv, transfer v u huv.symm⟩

end MathematicalAnalysis.Chapter02
