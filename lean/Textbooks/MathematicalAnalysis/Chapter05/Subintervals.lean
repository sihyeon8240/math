import Textbooks.MathematicalAnalysis.Chapter05.IntegralValues

namespace MathematicalAnalysis.Chapter05

open Set BoxIntegral

noncomputable section

/-- Lemma: a partition of a subinterval is induced by restriction. -/
def restrictPartition {I : Box Unit} (P : Partition I) (J : Box Unit) (hJI : J ≤ I) :
    Partition J := ⟨P.val.restrict J, P.property.restrict hJI⟩

/-- Lemma: boundedness restricts to a closed subinterval. -/
theorem bounded_subinterval {I J : Box Unit} (f : ℝ → ℝ) (hJI : J ≤ I)
    (hf : Bornology.IsBounded (f '' Icc (-I.upper ()) (-I.lower ()))) :
    Bornology.IsBounded (f '' Icc (-J.upper ()) (-J.lower ())) := by
  apply hf.subset
  apply image_mono
  intro x hx
  have h := Box.le_iff_bounds.mp hJI
  exact ⟨(neg_le_neg (h.2 ())).trans hx.1, hx.2.trans (neg_le_neg (h.1 ()))⟩

/-- Lemma: the Darboux gap of a restricted partition is no larger than the
original gap. -/
theorem restricted_gap_le {I J : Box Unit} (f : ℝ → ℝ) (P : Partition I)
    (hJI : J ≤ I) (hf : Bornology.IsBounded (f '' Icc (-I.upper ()) (-I.lower ()))) :
    upperSum f id (restrictPartition P J hJI) - lowerSum f id (restrictPartition P J hJI) ≤
      upperSum f id P - lowerSum f id P := by
  classical

  let v := fun K : Box Unit => (cellSup f K - cellInf f K) * cellLength K
  have hi (K : Box Unit) : increment id K = cellLength K := by
    dsimp [increment, cellLength]
    ring
  simp only [upperSum, lowerSum, ← Finset.sum_sub_distrib, hi, ← sub_mul]
  change (∑ K ∈ (P.val.restrict J).boxes, v K) ≤ ∑ L ∈ P.val.boxes, v L
  rw [Prepartition.restrict, Prepartition.sum_ofWithBot]

  let w := fun K : WithBot (Box Unit) => K.elim' 0 v
  have hn : ∀ K ∈ P.val.boxes.image
      (fun L : Box Unit => (J : WithBot (Box Unit)) ⊓ L), 0 ≤ w K := by
    intro K hK
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hK

    cases he : (J : WithBot (Box Unit)) ⊓ L with
    | bot => exact le_rfl
    | coe K =>
      have hKL : K ≤ L := WithBot.coe_le_coe.mp (he ▸ inf_le_right)
      exact mul_nonneg (sub_nonneg.mpr
        (cellInf_le_cellSup f (hKL.trans (P.val.le_of_mem hL)) hf)) (cellLength_pos K).le

  apply (Finset.sum_image_le_of_nonneg hn).trans
  apply Finset.sum_le_sum
  intro L hL
  have ho := sub_nonneg.mpr (cellInf_le_cellSup f (P.val.le_of_mem hL) hf)

  cases he : (J : WithBot (Box Unit)) ⊓ L with
  | bot => exact mul_nonneg ho (cellLength_pos L).le
  | coe K =>
    have hKL : K ≤ L := WithBot.coe_le_coe.mp (he ▸ inf_le_right)
    have hext := cell_extrema_mono f (P.val.le_of_mem hL) hKL hf
    have hlen : cellLength K ≤ cellLength L := by
      have hb := Box.le_iff_bounds.mp hKL
      dsimp [cellLength]
      linarith [hb.1 (), hb.2 ()]

    exact mul_le_mul (by linarith [hext.1, hext.2]) hlen (cellLength_pos K).le ho

/-- Theorem: Riemann integrability passes to every nondegenerate subinterval. -/
theorem riemannIntegrable_subinterval {I J : Box Unit} (f : ℝ → ℝ)
    (hJI : J ≤ I) (hf : RiemannIntegrable I f) : RiemannIntegrable J f := by
  apply (riemannIntegrable_iff_gap J f (bounded_subinterval f hJI hf.1)).mpr
  intro ε hε
  obtain ⟨P, hP⟩ := (riemannIntegrable_iff_gap I f hf.1).mp hf ε hε
  exact ⟨restrictPartition P J hJI, (restricted_gap_le f P hJI hf.1).trans_lt hP⟩

/-- Theorem: the integral is the sum of its integrals over a finite partition. -/
theorem riemannIntegral_partition (I : Box Unit) (f : ℝ → ℝ)
    (hf : RiemannIntegrable I f) (P : Partition I) :
    riemannIntegral I f = ∑ J ∈ P.val.boxes, riemannIntegral J f := by
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨Q, hQ⟩ := (riemannIntegrable_iff_gap I f hf.1).mp hf ε hε
  let R := commonRefinement P Q
  have hr := refinement_sums f id Q R inf_le_right hf.1 (fun _ _ _ _ h => h)
  have heq : R.val = P.val.biUnion (fun J => R.val.restrict J) := by
    rw [← Prepartition.inf_def, inf_eq_right.mpr (show R.val ≤ P.val from inf_le_left)]

  have hsum (v : Box Unit → ℝ) : (∑ K ∈ R.val.boxes, v K) =
      ∑ J ∈ P.val.boxes, ∑ K ∈ (R.val.restrict J).boxes, v K := by
    conv_lhs => rw [heq]
    rw [Prepartition.biUnion_boxes, Prepartition.sum_biUnion_boxes]

  have hb : lowerSum f id R ≤ ∑ J ∈ P.val.boxes, riemannIntegral J f ∧
      (∑ J ∈ P.val.boxes, riemannIntegral J f) ≤ upperSum f id R := by
    constructor
    · dsimp only [lowerSum]
      rw [hsum]
      apply Finset.sum_le_sum
      intro J hJ
      have hj := riemannIntegrable_subinterval f (P.val.le_of_mem hJ) hf
      have hv := (integral_bounds J f id
        (restrictPartition R J (P.val.le_of_mem hJ)) hj.1 (fun _ _ _ _ h => h)).1
      dsimp only [riemannIntegral]
      exact hv.trans_eq hj.2

    · dsimp only [upperSum]
      rw [hsum]
      apply Finset.sum_le_sum
      intro J hJ
      exact (integral_bounds J f id (restrictPartition R J (P.val.le_of_mem hJ))
        (bounded_subinterval f (P.val.le_of_mem hJ) hf.1) (fun _ _ _ _ h => h)).2.2

  obtain ⟨hl, _, hu⟩ := integral_bounds I f id R hf.1 (fun _ _ _ _ h => h)
  dsimp only [riemannIntegral] at hb ⊢
  exact abs_le.mpr ⟨by linarith [hf.2, hb.1, hb.2, hr.1, hr.2],
    by linarith [hf.2, hb.1, hb.2, hr.1, hr.2]⟩

/-- Theorem: the integral is additive across an interior endpoint. -/
theorem riemannIntegral_split (a c b : ℝ) (hac : a < c) (hcb : c < b)
    (f : ℝ → ℝ) (hf : RiemannIntegrable (intervalBox a b (hac.trans hcb)) f) :
    riemannIntegral (intervalBox a b (hac.trans hcb)) f =
      riemannIntegral (intervalBox a c hac) f + riemannIntegral (intervalBox c b hcb) f := by
  let I := intervalBox a b (hac.trans hcb)
  let P : Partition I := ⟨Prepartition.split I () (-c), Prepartition.isPartitionSplit _ _ _⟩
  have hv := riemannIntegral_partition I f hf P
  rw [Prepartition.sum_split_boxes] at hv

  have hx : -c ∈ Ioo (I.lower ()) (I.upper ()) := ⟨neg_lt_neg hcb, neg_lt_neg hac⟩
  rw [Box.splitLower_def hx, Box.splitUpper_def hx] at hv
  exact hv.trans (by
    change riemannIntegral (intervalBox c b hcb) f + riemannIntegral (intervalBox a c hac) f = _
    ring)

end

end MathematicalAnalysis.Chapter05
