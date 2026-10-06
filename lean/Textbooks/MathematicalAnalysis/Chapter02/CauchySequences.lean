import Textbooks.MathematicalAnalysis.Chapter02.Subsequences
import Mathlib.Topology.MetricSpace.Cauchy

namespace MathematicalAnalysis.Chapter02

open Set Metric Filter
open MathematicalAnalysis.Chapter01
open scoped Topology

variable {X : Type*} [MetricSpace X]

/-- Lemma: the metric epsilon condition is the standard Cauchy sequence predicate. -/
theorem cauchySeq_iff (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ m > N, ∀ n > N, dist (u m) (u n) < ε := by
  rw [Metric.cauchySeq_iff]
  constructor

  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, fun m hm n hn => hN m hm.le n hn.le⟩

  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N + 1, fun m hm n hn => hN m (Nat.lt_of_lt_of_le (Nat.lt_succ_self N) hm)
      n (Nat.lt_of_lt_of_le (Nat.lt_succ_self N) hn)⟩

/-- Theorem: a convergent metric sequence is Cauchy. -/
theorem convergent_cauchy (u : ℕ → X) (p : X) (hu : Tendsto u atTop (𝓝 p)) :
    CauchySeq u := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hu (ε / 2) (half_pos hε)
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hx := hN m hm
  have hy := hN n hn
  have ht := dist_triangle (u m) p (u n)
  rw [dist_comm p (u n)] at ht
  linarith

/-- Theorem: every metric Cauchy sequence is bounded. -/
theorem cauchy_bounded (u : ℕ → X) (hu : CauchySeq u) :
    Bornology.IsBounded (range u) := by
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu 1 zero_lt_one
  let R := 1 + ∑ n ∈ Finset.range N, dist (u n) (u N)
  have hsum : 0 ≤ ∑ n ∈ Finset.range N, dist (u n) (u N) :=
    Finset.sum_nonneg (fun _ _ => dist_nonneg)

  apply (isBounded_iff (range u)).mpr
  intro _
  refine ⟨u N, R, by
    dsimp [R]
    linarith, ?_⟩
  rintro x ⟨n, rfl⟩
  change dist (u n) (u N) < R
  by_cases hn : n < N

  · have hle := Finset.single_le_sum (f := fun n => dist (u n) (u N))
      (fun _ _ => dist_nonneg) (Finset.mem_range.mpr hn)
    dsimp [R]
    linarith

  · have htail := hN n (Nat.le_of_not_gt hn) N le_rfl
    dsimp [R]
    linarith

/-- Theorem: a Cauchy sequence with a convergent subsequence converges to the same point. -/
theorem cauchy_tendsto_of_subsequence (u : ℕ → X) (p : X) (hu : CauchySeq u)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (hlim : Tendsto (u ∘ φ) atTop (𝓝 p)) :
    Tendsto u atTop (𝓝 p) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu (ε / 2) (half_pos hε)
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hlim (ε / 2) (half_pos hε)
  let k := max N M

  refine ⟨N, ?_⟩
  intro n hn
  have hclose := hN n hn (φ k) ((le_max_left N M).trans (hφ.id_le k))
  have hnear := hM k (le_max_right _ _)
  have ht := dist_triangle (u n) (u (φ k)) p
  change dist (u (φ k)) p < ε / 2 at hnear

  linarith

/-- Theorem: every real Cauchy sequence converges, using boundedness and interval compactness. -/
theorem real_cauchy_converges (u : ℕ → ℝ) (hu : CauchySeq u) :
    ∃ a : ℝ, Tendsto u atTop (𝓝 a) := by
  obtain ⟨p, φ, hφ, hlim⟩ := bolzano_weierstrass u (cauchy_bounded u hu)
  exact ⟨p, cauchy_tendsto_of_subsequence u p hu φ hφ hlim⟩

/-- Theorem: a real sequence converges exactly when it is Cauchy. -/
theorem real_converges_iff_cauchy (u : ℕ → ℝ) :
    (∃ a : ℝ, Tendsto u atTop (𝓝 a)) ↔ CauchySeq u := by
  constructor
  · rintro ⟨a, ha⟩
    exact convergent_cauchy u a ha
  · exact real_cauchy_converges u

/-- Lemma: metric completeness is expressed by convergence of every Cauchy sequence.
The equivalence converts Mathlib's uniform-filter representation to its sequential interface. -/
theorem completeSpace_iff_cauchy_converges :
    CompleteSpace X ↔ ∀ u : ℕ → X, CauchySeq u → ∃ p, Tendsto u atTop (𝓝 p) := by
  constructor
  · intro h u hu
    exact h.complete hu
  · exact Metric.complete_of_cauchySeq_tendsto

/-- Theorem: the real least-upper-bound property yields metric completeness. -/
theorem real_complete : CompleteSpace ℝ :=
  Metric.complete_of_cauchySeq_tendsto real_cauchy_converges

end MathematicalAnalysis.Chapter02
