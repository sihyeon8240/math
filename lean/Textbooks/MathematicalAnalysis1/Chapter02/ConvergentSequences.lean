import Textbooks.MathematicalAnalysis1.Chapter01.MetricSpaces
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity

/-! Core sequence results from the epsilon definition, with indices in ℕ
starting at zero. -/

set_option autoImplicit false

namespace MathematicalAnalysis1.Chapter02

open Set Metric
open MathematicalAnalysis1.Chapter01

variable {X : Type*} [MetricSpace X]

/-- Definition: The epsilon definition for a sequence indexed from zero. -/
def convergesTo (u : ℕ → X) (p : X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, dist (u n) p < ε

/-- Definition: a sequence has a limit in its ambient metric space. -/
abbrev convergent (u : ℕ → X) : Prop := ∃ p : X, convergesTo u p

/-- Definition: a sequence has no limit in its ambient metric space. -/
abbrev divergent (u : ℕ → X) : Prop := ¬ convergent u

/-- Definition: the range of the sequence is bounded. -/
abbrev boundedSequence (u : ℕ → X) : Prop := bounded (range u)

/-- Lemma: Representation bridge to the standard Mathlib limit. -/
theorem convergesTo_iff_tendsto (u : ℕ → X) (p : X) :
    convergesTo u p ↔ Filter.Tendsto u Filter.atTop (nhds p) := by
  exact Metric.tendsto_atTop.symm

/-- Lemma: a finite initial segment and a bounded tail have a common bound. -/
theorem convergent_bounded (u : ℕ → X) (p : X) (h : convergesTo u p) :
    bounded (range u) := by
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
    (hp : convergesTo u p) (hq : convergesTo u q) : p = q := by
  by_contra hne

  have hd : 0 < dist p q := dist_pos.mpr hne

  obtain ⟨N, hN⟩ := hp (dist p q / 2) (half_pos hd)
  obtain ⟨M, hM⟩ := hq (dist p q / 2) (half_pos hd)

  have hn := hN (max N M) (le_max_left _ _)

  have hm := hM (max N M) (le_max_right _ _)

  have ht := dist_triangle p (u (max N M)) q

  rw [dist_comm p (u (max N M))] at ht
  linarith

/-- Proposition: boundedness and uniqueness, paired with the printed theorem. -/
theorem convergent_properties (u : ℕ → X) (p : X) (hp : convergesTo u p) :
    bounded (range u) ∧ ∀ q : X, convergesTo u q → p = q := by
  exact ⟨convergent_bounded u p hp, fun q hq => limit_unique u p q hp hq⟩

/-- Lemma: finite exceptional indices, rather than finitely many values. -/
theorem convergesTo_iff_finite_exceptions (u : ℕ → X) (p : X) :
    convergesTo u p ↔ ∀ ε : ℝ, 0 < ε → {n : ℕ | ε ≤ dist (u n) p}.Finite := by
  constructor

  · intro h ε hε

    obtain ⟨N, hN⟩ := h ε hε

    apply (Finset.range N).finite_toSet.subset
    intro n hn
    apply Finset.mem_range.mpr
    by_contra hnot
    exact (not_lt_of_ge hn) (hN n (Nat.le_of_not_gt hnot))

  · intro h ε hε

    obtain ⟨N, hN⟩ := (h ε hε).bddAbove

    refine ⟨N + 1, ?_⟩
    intro n hn
    by_contra hdist

    have hle := hN (show n ∈ {n : ℕ | ε ≤ dist (u n) p} from le_of_not_gt hdist)

    omega

/-- Lemma: Accepted Archimedean arithmetic supplies an index with reciprocal below ε. -/
theorem reciprocal_small (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, 1 / ((n : ℝ) + 1) < ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)

  refine ⟨N, ?_⟩
  intro n hn

  have hcast : (N : ℝ) ≤ n := Nat.cast_le.mpr hn

  have hprod : 1 < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN

  apply (div_lt_iff₀ (show 0 < (n : ℝ) + 1 by positivity)).mpr
  nlinarith

/-- Lemma: choose a distinct point within radius 1/(n+1). -/
theorem sequence_at_limit_point (E : Set X) (p : X) (hp : p ∈ limitPoints E) :
    ∃ u : ℕ → X, (∀ n, u n ∈ E ∧ u n ≠ p) ∧ convergesTo u p := by
  have hex : ∀ n : ℕ, ∃ q ∈ E, q ≠ p ∧ dist q p < 1 / ((n : ℝ) + 1) :=
    fun n => hp _ (by positivity)

  choose u hu hne hd using hex

  refine ⟨u, fun n => ⟨hu n, hne n⟩, ?_⟩
  intro ε hε

  obtain ⟨N, hN⟩ := reciprocal_small ε hε

  exact ⟨N, fun n hn => (hd n).trans (hN n hn)⟩

/-- Theorem: Both parts of the neighborhood characterization in the textbook. -/
theorem neighborhood_characterization (u : ℕ → X) (p : X) :
    (convergesTo u p ↔ ∀ ε : ℝ, 0 < ε → {n : ℕ | ε ≤ dist (u n) p}.Finite) ∧
    (∀ E : Set X, p ∈ limitPoints E →
      ∃ v : ℕ → X, (∀ n, v n ∈ E ∧ v n ≠ p) ∧ convergesTo v p) := by
  exact ⟨convergesTo_iff_finite_exceptions u p, fun E hp => sequence_at_limit_point E p hp⟩

end MathematicalAnalysis1.Chapter02
