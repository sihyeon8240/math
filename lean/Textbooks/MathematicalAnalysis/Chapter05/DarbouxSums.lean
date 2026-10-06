import Textbooks.MathematicalAnalysis.Chapter05.Partitions

namespace MathematicalAnalysis.Chapter05

open Set BoxIntegral

noncomputable section

/-- Definition: the supremum of a function over a partition cell. -/
def cellSup (f : ℝ → ℝ) (I : Box Unit) : ℝ := sSup (f '' cell I)

/-- Definition: the infimum of a function over a partition cell. -/
def cellInf (f : ℝ → ℝ) (I : Box Unit) : ℝ := sInf (f '' cell I)

/-- Definition: the upper Darboux-Stieltjes sum. The identity integrator gives
the upper Riemann sum. -/
def upperSum {I : Box Unit} (f α : ℝ → ℝ) (P : Partition I) : ℝ :=
  ∑ J ∈ P.val.boxes, cellSup f J * increment α J

/-- Definition: the lower Darboux-Stieltjes sum. -/
def lowerSum {I : Box Unit} (f α : ℝ → ℝ) (P : Partition I) : ℝ :=
  ∑ J ∈ P.val.boxes, cellInf f J * increment α J

/-- Definition: the upper Darboux-Stieltjes integral is the infimum of upper sums. -/
def upperIntegral (I : Box Unit) (f α : ℝ → ℝ) : ℝ :=
  sInf (range (upperSum (I := I) f α))

/-- Definition: the lower Darboux-Stieltjes integral is the supremum of lower sums. -/
def lowerIntegral (I : Box Unit) (f α : ℝ → ℝ) : ℝ :=
  sSup (range (lowerSum (I := I) f α))

/-- Definition: integrability requires boundedness and equality of the upper
and lower Darboux-Stieltjes integrals. -/
def StieltjesIntegrable (I : Box Unit) (f α : ℝ → ℝ) : Prop :=
  Bornology.IsBounded (f '' Icc (-I.upper ()) (-I.lower ())) ∧
    lowerIntegral I f α = upperIntegral I f α

/-- Definition: Riemann integrability is Stieltjes integrability for the identity integrator. -/
def RiemannIntegrable (I : Box Unit) (f : ℝ → ℝ) : Prop :=
  StieltjesIntegrable I f id

/-- Lemma: cell images are nonempty. -/
theorem cell_image_nonempty (f : ℝ → ℝ) (I : Box Unit) : (f '' cell I).Nonempty :=
  ⟨f (-I.upper ()), -I.upper (), ⟨le_rfl, neg_lt_neg (I.lower_lt_upper ())⟩, rfl⟩

/-- Lemma: a subcell lies in the ambient closed interval. -/
theorem cell_subset_closed {I J : Box Unit} (hJI : J ≤ I) :
    cell J ⊆ Icc (-I.upper ()) (-I.lower ()) :=
  (cell_mono hJI).trans Ico_subset_Icc_self

/-- Lemma: boundedness on the ambient interval bounds all cell images. -/
theorem cell_image_bounded {I J : Box Unit} (f : ℝ → ℝ) (hJI : J ≤ I)
    (hf : Bornology.IsBounded (f '' Icc (-I.upper ()) (-I.lower ()))) :
    Bornology.IsBounded (f '' cell J) := hf.subset (image_mono (cell_subset_closed hJI))

/-- Lemma: increasing integrators give nonnegative subcell increments. -/
theorem increment_nonneg {I J : Box Unit} (α : ℝ → ℝ) (hJI : J ≤ I)
    (hα : MonotoneOn α (Icc (-I.upper ()) (-I.lower ()))) : 0 ≤ increment α J := by
  have hl := (Box.le_iff_bounds.mp hJI).1 ()
  have hu := (Box.le_iff_bounds.mp hJI).2 ()
  have hlo : -J.upper () ∈ Icc (-I.upper ()) (-I.lower ()) := by
    constructor <;> linarith [J.lower_lt_upper ()]
  have hhi : -J.lower () ∈ Icc (-I.upper ()) (-I.lower ()) := by
    constructor <;> linarith [J.lower_lt_upper ()]
  exact sub_nonneg.mpr (hα hlo hhi (neg_le_neg (J.lower_le_upper ())))

/-- Lemma: the infimum on a cell is no larger than its supremum. -/
theorem cellInf_le_cellSup {I J : Box Unit} (f : ℝ → ℝ) (hJI : J ≤ I)
    (hf : Bornology.IsBounded (f '' Icc (-I.upper ()) (-I.lower ()))) :
    cellInf f J ≤ cellSup f J := by
  have hb := cell_image_bounded f hJI hf
  obtain ⟨x, hx⟩ := cell_image_nonempty f J
  exact (csInf_le hb.bddBelow hx).trans (le_csSup hb.bddAbove hx)

/-- Lemma: shrinking a cell decreases its supremum and increases its infimum. -/
theorem cell_extrema_mono {I J K : Box Unit} (f : ℝ → ℝ) (hJI : J ≤ I) (hKJ : K ≤ J)
    (hf : Bornology.IsBounded (f '' Icc (-I.upper ()) (-I.lower ()))) :
    cellSup f K ≤ cellSup f J ∧ cellInf f J ≤ cellInf f K := by
  have hb := cell_image_bounded f hJI hf
  have hbk := cell_image_bounded f (hKJ.trans hJI) hf
  have hsub := image_mono (f := f) (cell_mono hKJ)
  constructor
  · exact csSup_le (cell_image_nonempty f K) (fun x hx => le_csSup hb.bddAbove (hsub hx))
  · exact le_csInf (cell_image_nonempty f K) (fun x hx => csInf_le hb.bddBelow (hsub hx))

/-- Lemma: a lower sum is no larger than the corresponding upper sum. -/
theorem lowerSum_le_upperSum {I : Box Unit} (f α : ℝ → ℝ) (P : Partition I)
    (hf : Bornology.IsBounded (f '' Icc (-I.upper ()) (-I.lower ())))
    (hα : MonotoneOn α (Icc (-I.upper ()) (-I.lower ()))) :
    lowerSum f α P ≤ upperSum f α P := by
  apply Finset.sum_le_sum
  intro J hJ
  exact mul_le_mul_of_nonneg_right (cellInf_le_cellSup f (P.val.le_of_mem hJ) hf)
    (increment_nonneg α (P.val.le_of_mem hJ) hα)

/-- Theorem: refinement increases lower sums and decreases upper sums. -/
theorem refinement_sums {I : Box Unit} (f α : ℝ → ℝ) (P Q : Partition I)
    (hQP : Refines Q P)
    (hf : Bornology.IsBounded (f '' Icc (-I.upper ()) (-I.lower ())))
    (hα : MonotoneOn α (Icc (-I.upper ()) (-I.lower ()))) :
    lowerSum f α P ≤ lowerSum f α Q ∧ upperSum f α Q ≤ upperSum f α P := by
  have heq : Q.val = P.val.biUnion (fun J => Q.val.restrict J) := by
    rw [← Prepartition.inf_def, inf_eq_right.mpr hQP]
  have hsum (v : Box Unit → ℝ) :
      (∑ K ∈ Q.val.boxes, v K) =
        ∑ J ∈ P.val.boxes, ∑ K ∈ (Q.val.restrict J).boxes, v K := by
    conv_lhs => rw [heq]
    rw [Prepartition.biUnion_boxes, Prepartition.sum_biUnion_boxes]
  have hweights (J : Box Unit) (hJ : J ∈ P.val.boxes) :
      (∑ K ∈ (Q.val.restrict J).boxes, increment α K) = increment α J :=
    (incrementAdditive α).sum_partition_boxes le_top
      (Q.property.restrict (P.val.le_of_mem hJ))
  constructor
  · dsimp only [lowerSum]
    rw [hsum]
    apply Finset.sum_le_sum
    intro J hJ
    rw [← hweights J hJ, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro K hK
    have hKJ := (Q.val.restrict J).le_of_mem hK
    have hJI := P.val.le_of_mem hJ
    exact mul_le_mul_of_nonneg_right (cell_extrema_mono f hJI hKJ hf).2
      (increment_nonneg α (hKJ.trans hJI) hα)
  · dsimp only [upperSum]
    rw [hsum]
    apply Finset.sum_le_sum
    intro J hJ
    rw [← hweights J hJ, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro K hK
    have hKJ := (Q.val.restrict J).le_of_mem hK
    have hJI := P.val.le_of_mem hJ
    exact mul_le_mul_of_nonneg_right (cell_extrema_mono f hJI hKJ hf).1
      (increment_nonneg α (hKJ.trans hJI) hα)

/-- Lemma: every lower sum is at most every upper sum, using a common refinement. -/
theorem lowerSum_le_upperSum_other {I : Box Unit} (f α : ℝ → ℝ) (P Q : Partition I)
    (hf : Bornology.IsBounded (f '' Icc (-I.upper ()) (-I.lower ())))
    (hα : MonotoneOn α (Icc (-I.upper ()) (-I.lower ()))) :
    lowerSum f α P ≤ upperSum f α Q := by
  let R := commonRefinement P Q
  exact ((refinement_sums f α P R inf_le_left hf hα).1.trans
    (lowerSum_le_upperSum f α R hf hα)).trans
      (refinement_sums f α Q R inf_le_right hf hα).2

end

end MathematicalAnalysis.Chapter05
