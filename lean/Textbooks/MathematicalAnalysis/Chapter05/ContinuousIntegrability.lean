import Textbooks.MathematicalAnalysis.Chapter05.DarbouxCriterion
import Textbooks.MathematicalAnalysis.Chapter03.CompactContinuity

namespace MathematicalAnalysis.Chapter05

open Set Metric BoxIntegral
open MathematicalAnalysis.Chapter01 MathematicalAnalysis.Chapter03

noncomputable section

private theorem cell_iff_neg_mem (I : Box Unit) (x : ℝ) :
    x ∈ cell I ↔ (fun _ : Unit => -x) ∈ I := by
  constructor
  · intro hx i
    cases i
    exact ⟨by
      dsimp [cell] at hx
      linarith [hx.2], by
      dsimp [cell] at hx
      linarith [hx.1]⟩
  · intro hx
    have h := hx ()
    exact ⟨by linarith [h.2], by linarith [h.1]⟩

/-- Lemma: finitely many prescribed positive radii give a partition whose cells
are each contained in one of the corresponding closed neighborhoods. -/
theorem partition_subordinate (I : Box Unit)
    (r : Icc (-I.upper ()) (-I.lower ()) → ℝ) (hr : ∀ q, 0 < r q) :
    ∃ P : Partition I, ∀ J ∈ P.val.boxes, ∃ q : Icc (-I.upper ()) (-I.lower ()),
      ∀ x ∈ Icc (-J.upper ()) (-J.lower ()), |x - q.val| ≤ r q := by
  classical
  let A := Icc (-I.upper ()) (-I.lower ())
  have hI : IsCompact A := interval_compact _ _ (neg_le_neg (I.lower_le_upper ()))
  have hc : A ⊆ ⋃ q : A, ball q.val (r q / 2) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (half_pos (hr ⟨x, hx⟩))⟩
  obtain ⟨s, hs⟩ := hI.elim_finite_subcover _ (fun q => ball_open _ _) hc
  let B : A → Box Unit := fun q => intervalBox (q.val - r q) (q.val + r q)
    (by linarith [hr q])
  let cuts : Finset (Unit × ℝ) := s.biUnion (fun q => {((), (B q).lower ()),
    ((), (B q).upper ())})
  let P : Partition I := ⟨Prepartition.splitMany I cuts, Prepartition.isPartition_splitMany _ _⟩
  refine ⟨P, ?_⟩
  intro J hJ
  have hJI : J ≤ I := P.val.le_of_mem hJ
  have htag : -J.upper () ∈ A := cell_subset_closed hJI
    ⟨le_rfl, neg_lt_neg (J.lower_lt_upper ())⟩
  obtain ⟨q, hq⟩ := mem_iUnion.mp (hs htag)
  obtain ⟨hqs, hnear⟩ := mem_iUnion.mp hq
  have htagB : -J.upper () ∈ cell (B q) := by
    rw [cell_intervalBox]
    change |-J.upper () - q.val| < r q / 2 at hnear
    have h := abs_lt.mp hnear
    exact ⟨by linarith [hr q], by linarith [hr q]⟩
  have hJB : J ≤ B q := Prepartition.not_disjoint_imp_le_of_subset_of_mem_splitMany
    (fun i => by
      cases i
      intro p hp
      exact Finset.mem_biUnion.mpr ⟨q, hqs, by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hp⟩) hJ (by
      rw [Box.disjoint_coe]
      apply Set.not_disjoint_iff.mpr
      refine ⟨fun _ : Unit => J.upper (), ?_, J.upper_mem⟩
      simpa only [Box.coe_coe, Box.mem_coe, neg_neg] using
        (cell_iff_neg_mem (B q) (-J.upper ())).mp htagB)
  refine ⟨q, ?_⟩
  intro x hx
  have h := Box.le_iff_bounds.mp hJB
  have hl := h.1 ()
  have hu := h.2 ()
  dsimp only [B, intervalBox] at hl hu
  exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- Theorem: continuous real functions on a closed interval are Riemann integrable. -/
theorem continuous_riemannIntegrable (I : Box Unit) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (-I.upper ()) (-I.lower ()))) : RiemannIntegrable I f := by
  let A := Icc (-I.upper ()) (-I.lower ())
  have hI : IsCompact A := interval_compact _ _ (neg_le_neg (I.lower_le_upper ()))
  have hb := compact_bounded _ (compact_image_on A hI f hf)
  apply (riemannIntegrable_iff_gap I f hb).mpr
  intro ε hε
  let η := ε / (4 * (cellLength I + 1))
  have hL := cellLength_pos I
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hex : ∀ q : A, ∃ δ > 0, ∀ x ∈ A, dist x q.val < δ → |f x - f q| < η := by
    intro q
    exact Metric.continuousWithinAt_iff.mp (hf q q.property) η hη
  choose δ hδ hd using hex
  obtain ⟨P, hP⟩ := partition_subordinate I (fun q => δ q / 2)
    (fun q => half_pos (hδ q))
  have hosc : ∀ J ∈ P.val.boxes, cellSup f J - cellInf f J ≤ 2 * η := by
    intro J hJ
    obtain ⟨q, hq⟩ := hP J hJ
    have hjb := cell_image_bounded f (P.val.le_of_mem hJ) hb
    have hnear : ∀ x ∈ cell J, |f x - f q| < η := by
      intro x hx
      exact hd q x (cell_subset_closed (P.val.le_of_mem hJ) hx)
        ((hq x ⟨hx.1, hx.2.le⟩).trans_lt (half_lt_self (hδ q)))
    have hu : cellSup f J ≤ f q + η := by
      apply csSup_le (cell_image_nonempty f J)
      rintro y ⟨x, hx, rfl⟩
      have h := (abs_lt.mp (hnear x hx)).2
      linarith
    have hl : f q - η ≤ cellInf f J := by
      apply le_csInf (cell_image_nonempty f J)
      rintro y ⟨x, hx, rfl⟩
      have h := (abs_lt.mp (hnear x hx)).1
      linarith
    linarith
  refine ⟨P, ?_⟩
  have hbound : upperSum f id P - lowerSum f id P ≤ 2 * η * cellLength I := by
    dsimp only [upperSum, lowerSum]
    rw [← Finset.sum_sub_distrib, ← sum_cellLengths P, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro J hJ
    have hi : increment id J = cellLength J := by
      simp only [increment, id_eq, cellLength]
      ring
    rw [hi, ← sub_mul]
    exact mul_le_mul_of_nonneg_right (hosc J hJ) (cellLength_pos J).le
  have heq : η * (4 * (cellLength I + 1)) = ε :=
    div_mul_cancel₀ ε (by positivity)
  exact hbound.trans_lt (by nlinarith)

end

end MathematicalAnalysis.Chapter05
