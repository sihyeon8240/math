import Textbooks.MathematicalAnalysis1.Chapter01.MetricSpaces
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Tauto

/-! Euclidean metric and boundary results. Euclidean norm identities are accepted
finite-dimensional prerequisites; general metric topology lives in `MetricSpaces`. -/

set_option autoImplicit false

namespace MathematicalAnalysis1.Chapter01

open Set Metric

/-- Proposition: the Euclidean norm gives a metric. -/
theorem euclidean_metric (n : ℕ) :
    (∀ x y : EuclideanSpace ℝ (Fin n), 0 ≤ ‖x - y‖) ∧
    (∀ x y : EuclideanSpace ℝ (Fin n), ‖x - y‖ = 0 ↔ x = y) ∧
    (∀ x y : EuclideanSpace ℝ (Fin n), ‖x - y‖ = ‖y - x‖) ∧
    (∀ x y z : EuclideanSpace ℝ (Fin n),
      ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖) := by
  refine ⟨fun x y => norm_nonneg _, ?_, ?_, ?_⟩

  · intro x y
    rw [norm_eq_zero, sub_eq_zero]

  · intro x y
    exact norm_sub_rev x y

  · intro x y z
    calc
      ‖x - z‖ = ‖(x - y) + (y - z)‖ := by
        rw [sub_add_sub_cancel]
      _ ≤ ‖x - y‖ + ‖y - z‖ := norm_add_le _ _

/-- Lemma: a positive-dimensional Euclidean space has no isolated points. -/
theorem euclidean_punctured_ball (n : ℕ+)
    (p : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) :
    ∃ q : EuclideanSpace ℝ (Fin n), q ≠ p ∧ dist q p < r := by
  let v : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, n.pos⟩ (r / 2)

  have hv : ‖v‖ = r / 2 := by
    rw [PiLp.norm_single, Real.norm_eq_abs, abs_of_pos (half_pos hr)]

  refine ⟨p + v, ?_, ?_⟩

  · intro heq

    have hz : v = 0 := add_left_cancel (heq.trans (add_zero p).symm)

    rw [hz, norm_zero] at hv
    linarith

  · rw [dist_eq_norm, add_sub_cancel_left, hv]
    linarith

/-- Proposition: decompose the boundary according to the two limit-point sets. -/
theorem euclidean_boundary (n : ℕ+)
    (E : Set (EuclideanSpace ℝ (Fin n))) :
    frontier E = isolatedPoints E ∪ isolatedPoints Eᶜ ∪
      (derivedSet E ∩ derivedSet Eᶜ) := by
  have hE := isolated_limit_compl E (euclidean_punctured_ball n)

  have hEc := isolated_limit_compl Eᶜ (euclidean_punctured_ball n)

  rw [compl_compl] at hEc
  rw [isolated_eq_diff] at hE hEc
  rw [frontier, sdiff_eq_compl_inter,
    compl_interior_eq_closure_compl, closure_eq_union_derivedSet,
    closure_eq_union_derivedSet, isolated_eq_diff, isolated_eq_diff]
  ext p

  have h1 := @hE p

  have h2 := @hEc p

  simp only [mem_inter_iff, mem_union, mem_sdiff, mem_compl_iff] at *
  tauto

/-- Lemma: the zero-dimensional case: there is only one vector and no deleted ball. -/
theorem zero_dimensional (p q : EuclideanSpace ℝ (Fin 0)) (r : ℝ) :
    p = q ∧ ball p r \ {p} = ∅ := by
  have heq : ∀ x y : EuclideanSpace ℝ (Fin 0), x = y := by
    intro x y
    ext j
    exact Fin.elim0 j

  refine ⟨heq p q, ?_⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hx.2 (heq x p)

end MathematicalAnalysis1.Chapter01
