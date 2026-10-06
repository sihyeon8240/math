import Textbooks.MathematicalAnalysis.Chapter05.DarbouxSums

namespace MathematicalAnalysis.Chapter05

open Set BoxIntegral

noncomputable section

private def trivialPartition (I : Box Unit) : Partition I := ⟨⊤, Prepartition.isPartitionTop I⟩

/-- Lemma: upper sums form a nonempty set bounded below, and lower sums form
a nonempty set bounded above. -/
theorem sum_ranges_bounded (I : Box Unit) (f α : ℝ → ℝ)
    (hf : Bornology.IsBounded (f '' Icc (-I.upper ()) (-I.lower ())))
    (hα : MonotoneOn α (Icc (-I.upper ()) (-I.lower ()))) :
    (range (upperSum (I := I) f α)).Nonempty ∧
      BddBelow (range (upperSum (I := I) f α)) ∧
      (range (lowerSum (I := I) f α)).Nonempty ∧
      BddAbove (range (lowerSum (I := I) f α)) := by
  let P := trivialPartition I
  refine ⟨⟨upperSum f α P, P, rfl⟩, ⟨lowerSum f α P, ?_⟩,
    ⟨lowerSum f α P, P, rfl⟩, ⟨upperSum f α P, ?_⟩⟩
  · rintro x ⟨Q, rfl⟩
    exact lowerSum_le_upperSum_other f α P Q hf hα
  · rintro x ⟨Q, rfl⟩
    exact lowerSum_le_upperSum_other f α Q P hf hα

/-- Corollary: the lower integral is no larger than the upper integral. -/
theorem lowerIntegral_le_upperIntegral (I : Box Unit) (f α : ℝ → ℝ)
    (hf : Bornology.IsBounded (f '' Icc (-I.upper ()) (-I.lower ())))
    (hα : MonotoneOn α (Icc (-I.upper ()) (-I.lower ()))) :
    lowerIntegral I f α ≤ upperIntegral I f α := by
  obtain ⟨hU, _, hL, _⟩ := sum_ranges_bounded I f α hf hα
  apply le_csInf hU
  rintro x ⟨P, rfl⟩
  apply csSup_le hL
  rintro y ⟨Q, rfl⟩
  exact lowerSum_le_upperSum_other f α Q P hf hα

/-- Lemma: every partition brackets both Darboux integrals. -/
theorem integral_bounds (I : Box Unit) (f α : ℝ → ℝ) (P : Partition I)
    (hf : Bornology.IsBounded (f '' Icc (-I.upper ()) (-I.lower ())))
    (hα : MonotoneOn α (Icc (-I.upper ()) (-I.lower ()))) :
    lowerSum f α P ≤ lowerIntegral I f α ∧
      lowerIntegral I f α ≤ upperIntegral I f α ∧
      upperIntegral I f α ≤ upperSum f α P := by
  obtain ⟨_, hUb, _, hLb⟩ := sum_ranges_bounded I f α hf hα
  exact ⟨le_csSup hLb ⟨P, rfl⟩, lowerIntegral_le_upperIntegral I f α hf hα,
    csInf_le hUb ⟨P, rfl⟩⟩

/-- Theorem: a bounded function is integrable precisely when a partition makes
the difference of upper and lower sums arbitrarily small. -/
theorem stieltjesIntegrable_iff_gap (I : Box Unit) (f α : ℝ → ℝ)
    (hf : Bornology.IsBounded (f '' Icc (-I.upper ()) (-I.lower ())))
    (hα : MonotoneOn α (Icc (-I.upper ()) (-I.lower ()))) :
    StieltjesIntegrable I f α ↔
      ∀ ε > 0, ∃ P : Partition I, upperSum f α P - lowerSum f α P < ε := by
  obtain ⟨hU, _, hL, _⟩ := sum_ranges_bounded I f α hf hα
  constructor
  · rintro ⟨_, heq⟩ ε hε
    obtain ⟨u, ⟨P, rfl⟩, hu⟩ := exists_lt_of_csInf_lt hU
      (lt_add_of_pos_right (upperIntegral I f α) (half_pos hε))
    obtain ⟨v, ⟨Q, rfl⟩, hv⟩ := exists_lt_of_lt_csSup hL
      (sub_lt_self (lowerIntegral I f α) (half_pos hε))
    let R := commonRefinement P Q
    have hup := (refinement_sums f α P R inf_le_left hf hα).2
    have hlo := (refinement_sums f α Q R inf_le_right hf hα).1
    exact ⟨R, by linarith⟩
  · intro hgap
    refine ⟨hf, le_antisymm (lowerIntegral_le_upperIntegral I f α hf hα) ?_⟩
    by_contra hn
    have hp : 0 < upperIntegral I f α - lowerIntegral I f α :=
      sub_pos.mpr (lt_of_not_ge hn)
    obtain ⟨P, hP⟩ := hgap _ hp
    obtain ⟨hl, _, hu⟩ := integral_bounds I f α P hf hα
    linarith

/-- Corollary: the Darboux gap criterion for Riemann integrability. -/
theorem riemannIntegrable_iff_gap (I : Box Unit) (f : ℝ → ℝ)
    (hf : Bornology.IsBounded (f '' Icc (-I.upper ()) (-I.lower ()))) :
    RiemannIntegrable I f ↔
      ∀ ε > 0, ∃ P : Partition I, upperSum f id P - lowerSum f id P < ε :=
  stieltjesIntegrable_iff_gap I f id hf (fun _ _ _ _ h => h)

end

end MathematicalAnalysis.Chapter05
