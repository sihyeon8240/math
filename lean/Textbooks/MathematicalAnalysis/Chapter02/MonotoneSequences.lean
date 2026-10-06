import Textbooks.MathematicalAnalysis.Chapter02.ConvergentSequences

namespace MathematicalAnalysis.Chapter02

open Set Metric Filter
open scoped Topology

/-- Lemma: nondecreasingness is equivalent to the consecutive-term inequalities. -/
theorem monotone_iff_le_succ (u : ℕ → ℝ) :
    Monotone u ↔ ∀ n, u n ≤ u (n + 1) :=
  ⟨fun h n => h (Nat.le_succ n), monotone_nat_of_le_succ⟩

/-- Lemma: nonincreasingness is equivalent to the consecutive-term inequalities. -/
theorem antitone_iff_succ_le (u : ℕ → ℝ) :
    Antitone u ↔ ∀ n, u (n + 1) ≤ u n :=
  ⟨fun h n => h (Nat.le_succ n), antitone_nat_of_succ_le⟩

/-- Theorem: a bounded-above nondecreasing sequence converges to its supremum. -/
theorem monotone_tendsto_sSup (u : ℕ → ℝ) (hu : Monotone u)
    (hb : BddAbove (range u)) : Tendsto u atTop (𝓝 (sSup (range u))) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨x, ⟨N, rfl⟩, hx⟩ := exists_lt_of_lt_csSup (range_nonempty u)
    (sub_lt_self (sSup (range u)) hε)
  refine ⟨N, ?_⟩
  intro n hn
  have hupper := le_csSup hb (mem_range_self n)
  have hlower := hu hn
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hupper)]
  linarith

/-- Theorem: a bounded-below nonincreasing sequence converges to its infimum. -/
theorem antitone_tendsto_sInf (u : ℕ → ℝ) (hu : Antitone u)
    (hb : BddBelow (range u)) : Tendsto u atTop (𝓝 (sInf (range u))) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨x, ⟨N, rfl⟩, hx⟩ := exists_lt_of_csInf_lt (range_nonempty u)
    (lt_add_of_pos_right (sInf (range u)) hε)
  refine ⟨N, ?_⟩
  intro n hn
  have hlower := csInf_le hb (mem_range_self n)
  have hupper := hu hn
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlower)]
  linarith

/-- Theorem: every bounded monotone real sequence converges. -/
theorem bounded_monotone_converges (u : ℕ → ℝ)
    (hb : Bornology.IsBounded (range u)) (hm : Monotone u ∨ Antitone u) :
    ∃ a : ℝ, Tendsto u atTop (𝓝 a) := by
  obtain ⟨C, _, hC⟩ := (real_bounded_iff u).mp hb
  rcases hm with hm | hm

  · refine ⟨sSup (range u), monotone_tendsto_sSup u hm ⟨C, ?_⟩⟩
    rintro x ⟨n, rfl⟩
    exact (le_abs_self _).trans (hC n).le

  · refine ⟨sInf (range u), antitone_tendsto_sInf u hm ⟨-C, ?_⟩⟩
    rintro x ⟨n, rfl⟩
    exact (abs_lt.mp (hC n)).1.le

end MathematicalAnalysis.Chapter02
