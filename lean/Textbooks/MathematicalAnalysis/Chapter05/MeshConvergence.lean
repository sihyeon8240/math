import Textbooks.MathematicalAnalysis.Chapter05.FiniteDiscontinuities
import Textbooks.MathematicalAnalysis.Chapter05.IntegralValues
import Textbooks.MathematicalAnalysis.Chapter05.Subintervals
import Textbooks.MathematicalAnalysis.Chapter02.ConvergentSequences

namespace MathematicalAnalysis.Chapter05

open Set Filter BoxIntegral
open scoped Topology

noncomputable section

private theorem neg_mem_box (K : Box Unit) (x : ℝ) :
    (fun _ : Unit => -x) ∈ K ↔ x ∈ cell K := by
  constructor
  · intro h
    have hh := h ()
    exact ⟨by linarith [hh.2], by linarith [hh.1]⟩
  · intro h i
    cases i
    exact ⟨by linarith [h.2], by linarith [h.1]⟩

/-- Lemma: every cell length is at most the partition mesh. -/
theorem cellLength_le_mesh {I : Box Unit} (P : Partition I) (J : Box Unit)
    (hJ : J ∈ P.val.boxes) : cellLength J ≤ mesh P := Finset.le_sup' cellLength hJ

/-- Lemma: every partition mesh is positive. -/
theorem mesh_pos {I : Box Unit} (P : Partition I) : 0 < mesh P := by
  obtain ⟨J, hJ⟩ := P.property.nonempty_boxes
  exact (cellLength_pos J).trans_le (cellLength_le_mesh P J hJ)

/-- Lemma: crossing a coarse partition boundary contributes at most a bound
times the mesh and the number of coarse cells. -/
theorem upperSum_mesh_bound (I : Box Unit) (f : ℝ → ℝ)
    (hf : RiemannIntegrable I f) (P Q : Partition I)
    (C : ℝ) (hC : 0 < C)
    (hb : ∀ x ∈ Icc (-I.upper ()) (-I.lower ()), |f x| ≤ C) :
    upperSum f id Q - riemannIntegral I f ≤ upperSum f id P - lowerSum f id P +
      4 * C * mesh Q * P.val.boxes.card := by
  classical

  let E := P.val.boxes.image (fun L => -L.lower ())
  let w := fun K : Box Unit => ∑ e ∈ E, increment (neighborhoodLength e (mesh Q)) K
  have hw (K : Box Unit) : 0 ≤ w K := by
    apply Finset.sum_nonneg
    intro e _
    exact sub_nonneg.mpr ((neighborhoodLength_bounds e (mesh Q) (mesh_pos Q).le).1
      (neg_le_neg (K.lower_le_upper ())))

  let R := commonRefinement Q P
  have hr : R.val = Q.val.biUnion (fun K => P.val.restrict K) := rfl
  have hsum (v : Box Unit → ℝ) : (∑ L ∈ R.val.boxes, v L) =
      ∑ K ∈ Q.val.boxes, ∑ L ∈ (P.val.restrict K).boxes, v L := by
    rw [hr, Prepartition.biUnion_boxes, Prepartition.sum_biUnion_boxes]
  have hi (K : Box Unit) : increment id K = cellLength K := by
    dsimp [increment, cellLength]
    ring

  have hlocal : ∀ K ∈ Q.val.boxes, cellSup f K * cellLength K -
      (∑ L ∈ (P.val.restrict K).boxes, cellSup f L * cellLength L) ≤ 2 * C * w K := by
    intro K hK
    have hKI := Q.val.le_of_mem hK
    have htag : -K.upper () ∈ cell I := cell_mono hKI
      ⟨le_rfl, neg_lt_neg (K.lower_lt_upper ())⟩

    obtain ⟨L, hL, htagL⟩ := P.property _ ((neg_mem_box I _).mpr htag)
    have hLtag := (neg_mem_box L _).mp htagL

    by_cases hKL : K ≤ L
    · have ht : P.val.restrict K = ⊤ := by
        apply le_antisymm le_top
        intro J hJ
        have he : J = K := Prepartition.mem_top.mp hJ
        subst J
        refine ⟨K, (Prepartition.mem_restrict _).mpr ⟨L, hL, ?_⟩, le_rfl⟩
        exact (inf_eq_left.mpr (WithBot.coe_le_coe.mpr hKL)).symm
      rw [ht, Prepartition.top_boxes, Finset.sum_singleton, sub_self]
      exact mul_nonneg (by positivity) (hw K)

    · have hcross : -L.lower () < -K.lower () := by
        by_contra hn
        apply hKL
        apply Box.le_iff_bounds.mpr
        exact ⟨fun _ => by linarith, fun _ => by linarith [hLtag.1]⟩
      have hleft : -K.upper () ≤ -L.lower () := hLtag.2.le
      have hm := cellLength_le_mesh Q K hK
      have hcover : increment (neighborhoodLength (-L.lower ()) (mesh Q)) K = cellLength K := by
        apply neighborhoodLength_increment
        · dsimp [cellLength] at hm
          linarith
        · dsimp [cellLength] at hm
          linarith

      have hlen : cellLength K ≤ w K := by
        rw [← hcover]
        dsimp only [w]
        apply Finset.single_le_sum (f := fun e : ℝ => increment (neighborhoodLength e (mesh Q)) K)
          (a := -L.lower ())
        · intro e _
          exact sub_nonneg.mpr ((neighborhoodLength_bounds e (mesh Q) (mesh_pos Q).le).1
            (neg_le_neg (K.lower_le_upper ())))
        · exact Finset.mem_image.mpr ⟨L, hL, rfl⟩

      have hsup : cellSup f K ≤ C := by
        apply csSup_le (cell_image_nonempty f K)
        rintro z ⟨x, hx, rfl⟩
        exact (abs_le.mp (hb x (cell_subset_closed hKI hx))).2

      have hlow : -C * cellLength K ≤ ∑ L ∈ (P.val.restrict K).boxes,
          cellSup f L * cellLength L := by
        have hlength := sum_cellLengths (restrictPartition P K hKI)
        rw [← hlength, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro J hJ
        have hJI := ((P.val.restrict K).le_of_mem hJ).trans hKI
        have hs : -C ≤ cellSup f J := by
          have hp := hb (-J.upper ()) (cell_subset_closed hJI
            ⟨le_rfl, neg_lt_neg (J.lower_lt_upper ())⟩)
          have hu := le_csSup (cell_image_bounded f hJI hf.1).bddAbove
            (show f (-J.upper ()) ∈ f '' cell J from ⟨_,
              ⟨le_rfl, neg_lt_neg (J.lower_lt_upper ())⟩, rfl⟩)
          change f (-J.upper ()) ≤ cellSup f J at hu

          linarith [(abs_le.mp hp).1]

        exact mul_le_mul_of_nonneg_right hs (cellLength_pos J).le

      have hu := mul_le_mul_of_nonneg_right hsup (cellLength_pos K).le
      have he := mul_le_mul_of_nonneg_left hlen (show 0 ≤ 2 * C by positivity)

      linarith

  have htotal : upperSum f id Q - upperSum f id R ≤
      2 * C * (E.card * (2 * mesh Q)) := by
    have hsw : ∑ K ∈ Q.val.boxes, w K ≤ E.card * (2 * mesh Q) := by
      dsimp only [w]
      rw [Finset.sum_comm]
      simp only [sum_increments]
      calc
        _ ≤ ∑ e ∈ E, 2 * mesh Q := by
          apply Finset.sum_le_sum
          intro e _
          have hl := (neighborhoodLength_bounds e (mesh Q) (mesh_pos Q).le).2 (-I.upper ())
          have hu := (neighborhoodLength_bounds e (mesh Q) (mesh_pos Q).le).2 (-I.lower ())
          dsimp only [increment]
          linarith [hl.1, hu.2]
        _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
    dsimp only [upperSum]
    rw [hsum, ← Finset.sum_sub_distrib]
    simp only [hi]
    exact (Finset.sum_le_sum hlocal).trans (by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hsw (by positivity))

  have hcard : (E.card : ℝ) ≤ P.val.boxes.card := by
    exact_mod_cast Finset.card_image_le

  have hp := refinement_sums f id P R inf_le_right hf.1 (fun _ _ _ _ h => h)
  have hl := (integral_bounds I f id P hf.1 (fun _ _ _ _ h => h)).1
  have he := mul_le_mul_of_nonneg_left hcard (show 0 ≤ 4 * C * mesh Q by positivity [mesh_pos Q])
  dsimp only [riemannIntegral]
  nlinarith [hf.2, hp.2]

/-- Theorem: upper sums along refining partitions converge to the integral
when their meshes tend to zero. -/
theorem upperSum_tendsto (I : Box Unit) (f : ℝ → ℝ) (hf : RiemannIntegrable I f)
    (Q : ℕ → Partition I) (_hQ : ∀ n, Refines (Q (n + 1)) (Q n))
    (hm : Tendsto (fun n => mesh (Q n)) atTop (𝓝 0)) :
    Tendsto (fun n => upperSum f id (Q n)) atTop (𝓝 (riemannIntegral I f)) := by
  obtain ⟨C, hC, hb⟩ := absolute_bound I f hf.1
  apply (Chapter02.real_tendsto_iff _ _).mpr
  intro ε hε
  obtain ⟨P, hP⟩ := (riemannIntegrable_iff_gap I f hf.1).mp hf (ε / 2) (half_pos hε)
  let D := 4 * C * P.val.boxes.card + 1
  have hD : 0 < D := by
    dsimp [D]
    positivity

  obtain ⟨N, hN⟩ := (Chapter02.real_tendsto_iff _ _).mp hm
    (ε / (2 * D)) (div_pos hε (by positivity))

  refine ⟨N, ?_⟩
  intro n hn
  have hs := upperSum_mesh_bound I f hf P (Q n) C hC hb
  have hu := (integral_bounds I f id (Q n) hf.1 (fun _ _ _ _ h => h)).2.2
  change riemannIntegral I f ≤ upperSum f id (Q n) at hu
  rw [abs_of_nonneg (sub_nonneg.mpr hu)]

  have hh := hN n hn
  rw [sub_zero, abs_of_pos (mesh_pos (Q n))] at hh

  have he : mesh (Q n) * (2 * D) < ε := (lt_div_iff₀ (by positivity)).mp hh
  dsimp only [D] at he
  nlinarith [mesh_pos (Q n)]

end

end MathematicalAnalysis.Chapter05
