import Textbooks.MathematicalAnalysis.Chapter01.CompactSets
import Mathlib.Topology.Defs.Sequences

namespace MathematicalAnalysis.Chapter01

open Set Metric Filter
open scoped Topology

variable {X : Type*} [MetricSpace X]

/-- Lemma: reciprocal approximation with increasing indices yields convergence. -/
theorem subsequence_of_frequent_approximation (u : ℕ → X) (p : X)
    (h : ∀ n m : ℕ, ∃ k ≥ m, dist (u k) p < 1 / (n + 1 : ℝ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 p) := by
  classical

  choose k hk hd using h
  let φ : ℕ → ℕ := fun n => Nat.rec (k 0 0) (fun n prev => k (n + 1) (prev + 1)) n

  have hmono : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (φ n)) (hk (n + 1) (φ n + 1))

  have hdist : ∀ n, dist (u (φ n)) p < 1 / (n + 1 : ℝ) := by
    intro n
    cases n with
    | zero => exact hd 0 0
    | succ n => exact hd (n + 1) (φ n + 1)

  refine ⟨φ, hmono, Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨N, ?_⟩
  intro n hn

  have hden : (N + 1 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.succ_le_succ hn
  have hrecip : 1 / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) :=
    one_div_le_one_div_of_le (by positivity) hden

  exact (hdist n).trans_le hrecip |>.trans hN

/-- Theorem: the closures of the tails have a common point by the finite intersection property. -/
theorem compact_seqCompact (E : Set X) (hE : IsCompact E) : IsSeqCompact E := by
  classical

  intro u hu
  let T : ℕ → Set X := fun n => {x | ∃ m ≥ n, u m = x}
  let K : ℕ → Set X := fun n => closure (T n)

  have hKE : ∀ n, K n ⊆ E := by
    intro n
    apply (closure_properties (T n)).2.2 E (compact_closed E hE)
    rintro x ⟨m, _, rfl⟩
    exact hu m

  have hK : ∀ n, IsCompact (K n) := fun n =>
    closed_subset_compact E (K n) hE (closure_closed (T n)) (hKE n)

  have hfinite : ∀ s : Finset ℕ, (⋂ n ∈ s, K n).Nonempty := by
    intro s
    let m := ∑ n ∈ s, n
    refine ⟨u m, mem_iInter.mpr ?_⟩
    intro n
    apply mem_iInter.mpr
    intro hn
    apply subset_closure (T n)
    exact ⟨m, Finset.single_le_sum (f := fun n : ℕ => n) (fun _ _ => Nat.zero_le _) hn, rfl⟩

  obtain ⟨p, hp⟩ := compact_finite_intersection K hK hfinite
  have hpE : p ∈ E := hKE 0 (mem_iInter.mp hp 0)

  have happrox : ∀ n m : ℕ, ∃ k ≥ m, dist (u k) p < 1 / (n + 1 : ℝ) := by
    intro n m
    obtain ⟨q, ⟨k, hkm, rfl⟩, hq⟩ := Metric.mem_closure_iff.mp
      (mem_iInter.mp hp m) (1 / (n + 1 : ℝ)) (by positivity)
    exact ⟨k, hkm, by rwa [dist_comm]⟩

  obtain ⟨φ, hφ, hlim⟩ := subsequence_of_frequent_approximation u p happrox

  exact ⟨p, hpE, φ, hφ, hlim⟩

/-- Lemma: a sequentially compact set contains its limit points. -/
theorem seqCompact_closed (E : Set X) (hE : IsSeqCompact E) : IsClosed E := by
  classical

  apply (closed_iff_derivedSet E).mpr
  intro p hp
  have hex : ∀ n : ℕ, ∃ q ∈ E, dist q p < 1 / (n + 1 : ℝ) := by
    intro n
    obtain ⟨q, hq, _, hd⟩ := (mem_derivedSet_iff E p).mp hp
      (1 / (n + 1 : ℝ)) (by positivity)
    exact ⟨q, hq, hd⟩

  choose u hu hd using hex
  obtain ⟨q, hq, φ, hφ, hlim⟩ := hE hu
  by_contra hpE

  have hpq : p ≠ q := fun heq => hpE (heq.symm ▸ hq)
  have hε : 0 < dist p q / 2 := half_pos (dist_pos.mpr hpq)

  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (dist p q / 2) hε
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt hε
  let n := max N M

  have hnearq := hN n (le_max_left _ _)
  have hden : (M + 1 : ℝ) ≤ φ n + 1 := by
    exact_mod_cast Nat.succ_le_succ ((le_max_right N M).trans (hφ.id_le n))

  have hnearp := (hd (φ n)).trans_le
    (one_div_le_one_div_of_le (by positivity) hden) |>.trans hM
  have htriangle := dist_triangle p (u (φ n)) q
  rw [dist_comm p (u (φ n))] at htriangle
  change dist (u (φ n)) q < dist p q / 2 at hnearq
  linarith

/-- Lemma: an unbounded sequence cannot have a convergent subsequence. -/
theorem seqCompact_bounded (E : Set X) (hE : IsSeqCompact E) : Bornology.IsBounded E := by
  classical

  apply (isBounded_iff E).mpr
  intro hX
  obtain ⟨p⟩ := hX
  by_contra hb

  have hex : ∀ n : ℕ, ∃ x ∈ E, (n : ℝ) ≤ dist x p := by
    intro n
    have hn : ¬ E ⊆ ball p (n + 1 : ℝ) := by
      intro hs
      exact hb ⟨p, n + 1, by positivity, hs⟩

    obtain ⟨x, hx, hdist⟩ := Set.not_subset.mp hn
    exact ⟨x, hx, by
      change ¬ dist x p < (n + 1 : ℝ) at hdist
      linarith⟩

  choose u hu hd using hex
  obtain ⟨q, _, φ, hφ, hlim⟩ := hE hu
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim 1 zero_lt_one
  obtain ⟨M, hM⟩ := exists_nat_gt (dist q p + 1)
  let n := max N M

  have hnear := hN n (le_max_left _ _)
  have hindex : (M : ℝ) ≤ φ n := by
    exact_mod_cast (le_max_right N M).trans (hφ.id_le n)

  have hfar := hd (φ n)
  have htriangle := dist_triangle (u (φ n)) q p
  change dist (u (φ n)) q < 1 at hnear

  linarith

/-- Theorem: compactness, closed boundedness, and subsequence convergence are equivalent
in a positive-dimensional Euclidean space. -/
theorem euclidean_compact_iff (n : ℕ+) (E : Set (EuclideanSpace ℝ (Fin n))) :
    (IsCompact E ↔ IsClosed E ∧ Bornology.IsBounded E) ∧
    (IsCompact E ↔ IsSeqCompact E) := by
  refine ⟨heine_borel n E, ?_⟩
  constructor

  · exact compact_seqCompact E
  · intro h
    exact (heine_borel n E).mpr ⟨seqCompact_closed E h, seqCompact_bounded E h⟩

end MathematicalAnalysis.Chapter01
