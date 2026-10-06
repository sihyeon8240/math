import Textbooks.MathematicalAnalysis.Chapter02.ConvergentSequences
import Textbooks.MathematicalAnalysis.Chapter01.SequentialCompactness

namespace MathematicalAnalysis.Chapter02

open Set Metric Filter
open scoped Topology

variable {X : Type*} [MetricSpace X]

/-- Definition: a subsequential limit is the limit along a strictly increasing index map. -/
def subsequentialLimits (u : ℕ → X) : Set X :=
  {p | ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 p)}

/-- Theorem: every subsequence of a convergent sequence converges to the same limit. -/
theorem tendsto_subsequence (u : ℕ → X) (p : X) (hu : Tendsto u atTop (𝓝 p))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) : Tendsto (u ∘ φ) atTop (𝓝 p) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hu ε hε
  exact ⟨N, fun n hn => hN (φ n) (hn.trans (hφ.id_le n))⟩

/-- Theorem: convergence is equivalent to convergence of all subsequences to the same limit. -/
theorem tendsto_iff_all_subsequences (u : ℕ → X) (p : X) :
    Tendsto u atTop (𝓝 p) ↔
      ∀ φ : ℕ → ℕ, StrictMono φ → Tendsto (u ∘ φ) atTop (𝓝 p) := by
  constructor
  · exact tendsto_subsequence u p
  · intro h
    exact h id strictMono_id

/-- Theorem: a subsequential limit is approached at infinitely many indices in every ball. -/
theorem mem_subsequentialLimits_iff (u : ℕ → X) (p : X) :
    p ∈ subsequentialLimits u ↔
      ∀ ε > 0, {n : ℕ | dist (u n) p < ε}.Infinite := by
  constructor

  · rintro ⟨φ, hφ, hlim⟩ ε hε hf
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim ε hε
    obtain ⟨M, hM⟩ := hf.bddAbove
    let n := max N (M + 1)
    have hnear := hN n (le_max_left _ _)
    have hle : φ n ≤ M := hM (show φ n ∈ {n : ℕ | dist (u n) p < ε} from hnear)
    exact (Nat.not_succ_le_self M)
      ((le_max_right N (M + 1)).trans ((hφ.id_le n).trans hle))

  · intro h
    apply MathematicalAnalysis.Chapter01.subsequence_of_frequent_approximation u p
    intro n m
    obtain ⟨k, hk, hkm⟩ := (h (1 / (n + 1 : ℝ)) (by positivity)).exists_gt m
    exact ⟨k, hkm.le, hk⟩

/-- Theorem: every bounded real sequence has a convergent subsequence. -/
theorem bolzano_weierstrass (u : ℕ → ℝ) (hu : Bornology.IsBounded (range u)) :
    (subsequentialLimits u).Nonempty := by
  obtain ⟨C, hC, hbound⟩ := (real_bounded_iff u).mp hu
  have hinterval := MathematicalAnalysis.Chapter01.interval_compact (-C) C (by linarith)
  have huI : ∀ n, u n ∈ Icc (-C) C := by
    intro n
    exact ⟨(abs_lt.mp (hbound n)).1.le, (abs_lt.mp (hbound n)).2.le⟩
  obtain ⟨p, _, φ, hφ, hlim⟩ := MathematicalAnalysis.Chapter01.compact_seqCompact _
    hinterval huI
  exact ⟨p, φ, hφ, hlim⟩

/-- Theorem: a sequence converges exactly when every subsequence converges. -/
theorem converges_iff_all_subsequences (u : ℕ → X) :
    (∃ p, Tendsto u atTop (𝓝 p)) ↔
      ∀ φ : ℕ → ℕ, StrictMono φ → ∃ p, Tendsto (u ∘ φ) atTop (𝓝 p) := by
  constructor
  · rintro ⟨p, hp⟩ φ hφ
    exact ⟨p, tendsto_subsequence u p hp φ hφ⟩
  · intro h
    exact h id strictMono_id

/-- Lemma: deleting the first term does not change a sequence limit. -/
theorem tendsto_iff_succ (u : ℕ → X) (p : X) :
    Tendsto u atTop (𝓝 p) ↔ Tendsto (fun n => u (n + 1)) atTop (𝓝 p) := by
  constructor
  · intro h
    apply tendsto_subsequence u p h (fun n => n + 1)
    intro m n hmn
    change m + 1 < n + 1
    omega
  · intro h
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h ε hε
    refine ⟨N + 1, ?_⟩
    intro n hn
    have ht := hN (n - 1) (by omega)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using ht

end MathematicalAnalysis.Chapter02
