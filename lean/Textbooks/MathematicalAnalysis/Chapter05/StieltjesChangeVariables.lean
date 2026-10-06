import Textbooks.MathematicalAnalysis.Chapter05.IntegralValues
import Textbooks.MathematicalAnalysis.Chapter05.Subintervals

namespace MathematicalAnalysis.Chapter05

open Set BoxIntegral

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

/-- Definition: an increasing bijection transports interval endpoints. -/
def mapInterval (φ : ℝ ≃o ℝ) (I : Box Unit) : Box Unit :=
  intervalBox (φ (-I.upper ())) (φ (-I.lower ())) (φ.strictMono (neg_lt_neg (I.lower_lt_upper ())))

private theorem mapInterval_cell (φ : ℝ ≃o ℝ) (I : Box Unit) :
    cell (mapInterval φ I) = φ '' cell I := by
  rw [mapInterval, cell_intervalBox]
  exact (φ.image_Ico _ _).symm

private theorem mapInterval_le (φ : ℝ ≃o ℝ) {I J : Box Unit} (h : I ≤ J) :
    mapInterval φ I ≤ mapInterval φ J := by
  apply Box.le_iff_bounds.mpr
  have hb := Box.le_iff_bounds.mp h
  exact ⟨fun _ => neg_le_neg (φ.monotone (neg_le_neg (hb.1 ()))),
    fun _ => neg_le_neg (φ.monotone (neg_le_neg (hb.2 ())))⟩

private theorem mapInterval_inverse (φ : ℝ ≃o ℝ) (I : Box Unit) :
    mapInterval φ.symm (mapInterval φ I) = I := by
  apply Box.ext
  intro u
  simp only [mapInterval, intervalBox, neg_neg, OrderIso.symm_apply_apply]

private theorem mapInterval_injective (φ : ℝ ≃o ℝ) : Function.Injective (mapInterval φ) := by
  intro I J h
  simpa only [mapInterval_inverse] using congrArg (mapInterval φ.symm) h

/-- Definition: an increasing bijection transports every cell of a partition. -/
def mapPartition (φ : ℝ ≃o ℝ) {I : Box Unit} (P : Partition I) :
    Partition (mapInterval φ I) := by
  classical
  let Q : Prepartition (mapInterval φ I) :=
    { boxes := P.val.boxes.image (mapInterval φ)
      le_of_mem' := by
        intro J hJ
        obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hJ
        exact mapInterval_le φ (P.val.le_of_mem hK)
      pairwiseDisjoint := by
        rintro J hJ K hK hne
        obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hJ
        obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hK
        apply Set.disjoint_left.mpr
        intro u hu hv
        have ha := (neg_mem_box _ (-u ())).mp (by simpa using hu)
        have hb := (neg_mem_box _ (-u ())).mp (by simpa using hv)
        rw [mapInterval_cell] at ha hb
        obtain ⟨x, hx, he⟩ := ha
        obtain ⟨y, hy, hf⟩ := hb
        have hxy : x = y := φ.injective (he.trans hf.symm)
        subst y
        apply hne
        congr 1
        exact P.val.eq_of_mem_of_mem hL hM
          ((neg_mem_box L x).mpr hx) ((neg_mem_box M x).mpr hy) }
  refine ⟨Q, ?_⟩
  intro u hu
  have ht := (neg_mem_box _ (-u ())).mp (by simpa using hu)
  rw [mapInterval_cell] at ht
  obtain ⟨x, hx, hval⟩ := ht
  obtain ⟨K, hK, hmem⟩ := P.property _ ((neg_mem_box I x).mpr hx)
  refine ⟨mapInterval φ K, Finset.mem_image.mpr ⟨K, hK, rfl⟩, ?_⟩
  have hm : -u () ∈ cell (mapInterval φ K) := by
    rw [mapInterval_cell]
    exact ⟨x, (neg_mem_box K x).mp hmem, hval⟩
  have hh := (neg_mem_box _ (-u ())).mpr hm
  simpa only [neg_neg] using hh

private theorem transported_sums (φ : ℝ ≃o ℝ) (I : Box Unit) (f : ℝ → ℝ) (P : Partition I) :
    upperSum (fun x => f (φ x)) φ P = upperSum f id (mapPartition φ P) ∧
      lowerSum (fun x => f (φ x)) φ P = lowerSum f id (mapPartition φ P) := by
  classical
  have he (K : Box Unit) : f '' cell (mapInterval φ K) = (fun x => f (φ x)) '' cell K := by
    rw [mapInterval_cell, image_image]
  have hi (K : Box Unit) : increment id (mapInterval φ K) = increment φ K := by
    simp only [increment, mapInterval, intervalBox, neg_neg, id_eq]
  constructor <;> dsimp only [upperSum, lowerSum, mapPartition]
  all_goals
    rw [Finset.sum_image (fun _ _ _ _ h => mapInterval_injective φ h)]
    apply Finset.sum_congr rfl
    intro K _
    simp only [cellSup, cellInf, he, hi]

/-- Definition: the Riemann–Stieltjes integral is the common Darboux value. -/
def stieltjesIntegral (I : Box Unit) (f α : ℝ → ℝ) : ℝ := upperIntegral I f α

/-- Theorem: an increasing bijection changes a Riemann integral into a
Riemann–Stieltjes integral with that bijection as integrator. -/
theorem stieltjes_change_orderIso (φ : ℝ ≃o ℝ) (I : Box Unit) (f : ℝ → ℝ)
    (hf : RiemannIntegrable (mapInterval φ I) f) :
    StieltjesIntegrable I (fun x => f (φ x)) φ ∧
      stieltjesIntegral I (fun x => f (φ x)) φ = riemannIntegral (mapInterval φ I) f := by
  classical
  have hb : Bornology.IsBounded ((fun x => f (φ x)) '' Icc (-I.upper ()) (-I.lower ())) := by
    apply hf.1.subset
    rintro y ⟨x, hx, rfl⟩
    refine ⟨φ x, ?_, rfl⟩
    simp only [mapInterval, intervalBox, neg_neg]
    exact ⟨φ.monotone hx.1, φ.monotone hx.2⟩
  have hα : MonotoneOn (fun x => φ x) (Icc (-I.upper ()) (-I.lower ())) :=
    φ.monotone.monotoneOn _
  have hgap : StieltjesIntegrable I (fun x => f (φ x)) φ := by
    apply (stieltjesIntegrable_iff_gap I _ _ hb hα).mpr
    intro ε hε
    obtain ⟨Q, hQ⟩ := (riemannIntegrable_iff_gap _ f hf.1).mp hf ε hε
    have hi := mapInterval_inverse φ I
    let P : Partition I := restrictPartition (mapPartition φ.symm Q) I hi.symm.le
    have hboxes : P.val.boxes = Q.val.boxes.image (mapInterval φ.symm) :=
      Prepartition.restrict_boxes_of_le _ hi.le
    have hP : mapPartition φ P = Q := by
      apply Subtype.ext
      apply Prepartition.injective_boxes
      change (P.val.boxes.image (mapInterval φ)) = Q.val.boxes
      rw [hboxes, Finset.image_image]
      have hinv : ∀ K, mapInterval φ (mapInterval φ.symm K) = K := by
        intro K
        simpa only [OrderIso.symm_symm] using mapInterval_inverse φ.symm K
      simp only [Function.comp_def, hinv, Finset.image_id']
    obtain ⟨hu, hl⟩ := transported_sums φ I f P
    exact ⟨P, by
      rw [hu, hl, hP]
      exact hQ⟩
  refine ⟨hgap, ?_⟩
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨P, hP⟩ := (stieltjesIntegrable_iff_gap I _ _ hb hα).mp hgap ε hε
  obtain ⟨hu, hl⟩ := transported_sums φ I f P
  obtain ⟨hsl, _, hsu⟩ := integral_bounds I (fun x => f (φ x)) φ P hb hα
  obtain ⟨hrl, _, hru⟩ := integral_bounds _ f id (mapPartition φ P) hf.1 (fun _ _ _ _ h => h)
  dsimp only [stieltjesIntegral, riemannIntegral]
  exact abs_le.mpr ⟨by linarith [hgap.2, hf.2], by linarith [hgap.2, hf.2]⟩

private theorem extend_interval_bijection (A B a b : ℝ) (hAB : A < B) (hab : a < b)
    (φ : ℝ → ℝ) (hmono : StrictMonoOn φ (Icc A B))
    (hmap : MapsTo φ (Icc A B) (Icc a b)) (honto : SurjOn φ (Icc A B) (Icc a b)) :
    ∃ ψ : ℝ ≃o ℝ, (∀ x ∈ Icc A B, ψ x = φ x) ∧ ψ A = a ∧ ψ B = b := by
  classical
  have hA : A ∈ Icc A B := ⟨le_rfl, hAB.le⟩
  have hB : B ∈ Icc A B := ⟨hAB.le, le_rfl⟩
  have ha : φ A = a := by
    obtain ⟨x, hx, he⟩ := honto ⟨le_rfl, hab.le⟩
    have hm := hmono.monotoneOn hA hx hx.1
    linarith [(hmap hA).1]
  have hb : φ B = b := by
    obtain ⟨x, hx, he⟩ := honto ⟨hab.le, le_rfl⟩
    have hm := hmono.monotoneOn hx hB hx.2
    linarith [(hmap hB).2]
  let g := fun x => if x < A then x - A + a else if B < x then x - B + b else φ x
  have hg : ∀ x ∈ Icc A B, g x = φ x := by
    intro x hx
    simp only [g, not_lt.mpr hx.1, not_lt.mpr hx.2, ↓reduceIte]
  have hm : StrictMono g := by
    intro x y hxy
    by_cases hx : x < A
    · by_cases hy : y < A
      · simp only [g, hx, hy, ↓reduceIte]
        linarith
      · by_cases hyB : B < y
        · simp only [g, hx, hy, hyB, ↓reduceIte]
          linarith
        · simp only [g, hx, hy, hyB, ↓reduceIte]
          have hyI : y ∈ Icc A B := ⟨le_of_not_gt hy, le_of_not_gt hyB⟩
          linarith [(hmap hyI).1]
    · have hy : ¬ y < A := by linarith
      by_cases hxB : B < x
      · have hyB : B < y := hxB.trans hxy
        simp only [g, hx, hy, hxB, hyB, ↓reduceIte]
        linarith
      · have hxI : x ∈ Icc A B := ⟨le_of_not_gt hx, le_of_not_gt hxB⟩
        by_cases hyB : B < y
        · simp only [g, hx, hy, hxB, hyB, ↓reduceIte]
          linarith [(hmap hxI).2]
        · rw [hg x hxI, hg y ⟨le_of_not_gt hy, le_of_not_gt hyB⟩]
          exact hmono hxI ⟨le_of_not_gt hy, le_of_not_gt hyB⟩ hxy
  have hs : Function.Surjective g := by
    intro t
    by_cases ht : t < a
    · refine ⟨t - a + A, ?_⟩
      simp only [g, show t - a + A < A by linarith, ↓reduceIte]
      ring
    · by_cases hbt : b < t
      · refine ⟨t - b + B, ?_⟩
        simp only [g, show ¬t - b + B < A by linarith,
          show B < t - b + B by linarith, ↓reduceIte]
        ring
      · obtain ⟨x, hx, he⟩ := honto ⟨le_of_not_gt ht, le_of_not_gt hbt⟩
        exact ⟨x, (hg x hx).trans he⟩
  let ψ := hm.orderIsoOfRightInverse g (Function.surjInv hs) (Function.rightInverse_surjInv hs)
  exact ⟨ψ, hg, (hg A hA).trans ha, (hg B hB).trans hb⟩

private theorem stieltjes_congr (I : Box Unit) (f g α β : ℝ → ℝ)
    (hfg : ∀ x ∈ Icc (-I.upper ()) (-I.lower ()), f x = g x)
    (hαβ : ∀ x ∈ Icc (-I.upper ()) (-I.lower ()), α x = β x) :
    StieltjesIntegrable I f α ↔ StieltjesIntegrable I g β := by
  have him : f '' Icc (-I.upper ()) (-I.lower ()) = g '' Icc (-I.upper ()) (-I.lower ()) :=
    image_congr hfg
  have hc (J : Box Unit) (hJI : J ≤ I) : f '' cell J = g '' cell J :=
    image_congr (fun x hx => hfg x (cell_subset_closed hJI hx))
  have hi (J : Box Unit) (hJI : J ≤ I) : increment α J = increment β J := by
    have h := Box.le_iff_bounds.mp hJI
    have hl : -J.upper () ∈ Icc (-I.upper ()) (-I.lower ()) :=
      ⟨neg_le_neg (h.2 ()), (neg_le_neg (J.lower_le_upper ())).trans (neg_le_neg (h.1 ()))⟩
    have hu : -J.lower () ∈ Icc (-I.upper ()) (-I.lower ()) :=
      ⟨(neg_le_neg (h.2 ())).trans (neg_le_neg (J.lower_le_upper ())), neg_le_neg (h.1 ())⟩
    simp only [increment, hαβ _ hl, hαβ _ hu]
  have hs (P : Partition I) :
      upperSum f α P = upperSum g β P ∧ lowerSum f α P = lowerSum g β P := by
    constructor <;> apply Finset.sum_congr rfl <;> intro J hJ
    all_goals simp only [cellSup, cellInf, hc J (P.val.le_of_mem hJ), hi J (P.val.le_of_mem hJ)]
  have hU : upperIntegral I f α = upperIntegral I g β := by
    unfold upperIntegral
    rw [show upperSum (I := I) f α = upperSum g β from funext (fun P => (hs P).1)]
  have hL : lowerIntegral I f α = lowerIntegral I g β := by
    unfold lowerIntegral
    rw [show lowerSum (I := I) f α = lowerSum g β from funext (fun P => (hs P).2)]
  simp only [StieltjesIntegrable, him, hU, hL]

/-- Theorem: a continuous strictly increasing map of one closed interval onto
another gives the Riemann–Stieltjes change of variables. -/
theorem stieltjes_change_variables (A B a b : ℝ) (hAB : A < B) (hab : a < b)
    (φ f : ℝ → ℝ) (_hcont : ContinuousOn φ (Icc A B))
    (hmono : StrictMonoOn φ (Icc A B)) (hmap : MapsTo φ (Icc A B) (Icc a b))
    (honto : SurjOn φ (Icc A B) (Icc a b))
    (hf : RiemannIntegrable (intervalBox a b hab) f) :
    StieltjesIntegrable (intervalBox A B hAB) (fun x => f (φ x)) φ ∧
      stieltjesIntegral (intervalBox A B hAB) (fun x => f (φ x)) φ =
        riemannIntegral (intervalBox a b hab) f := by
  obtain ⟨ψ, he, ha, hb⟩ := extend_interval_bijection A B a b hAB hab φ hmono hmap honto
  have hI : mapInterval ψ (intervalBox A B hAB) = intervalBox a b hab := by
    simp only [mapInterval, intervalBox, neg_neg, ha, hb]
  have hψ := stieltjes_change_orderIso ψ (intervalBox A B hAB) f (hI ▸ hf)
  have hfg : ∀ x ∈ Icc (-(intervalBox A B hAB).upper ()) (-(intervalBox A B hAB).lower ()),
      f (ψ x) = f (φ x) := by
    simp only [intervalBox, neg_neg]
    intro x hx
    rw [he x hx]
  have hα : ∀ x ∈ Icc (-(intervalBox A B hAB).upper ()) (-(intervalBox A B hAB).lower ()),
      ψ x = φ x := by simpa only [intervalBox, neg_neg] using he
  refine ⟨(stieltjes_congr _ _ _ _ _ hfg hα).mp hψ.1, ?_⟩
  have hsum (P : Partition (intervalBox A B hAB)) :
      upperSum (fun x => f (ψ x)) ψ P = upperSum (fun x => f (φ x)) φ P := by
    apply Finset.sum_congr rfl
    intro J hJ
    have hJI := P.val.le_of_mem hJ
    have him : (fun x => f (ψ x)) '' cell J = (fun x => f (φ x)) '' cell J :=
      image_congr (fun x hx => hfg x (cell_subset_closed hJI hx))
    have hj := Box.le_iff_bounds.mp hJI
    have hl : -J.upper () ∈ Icc A B := by
      dsimp only [intervalBox] at hj
      exact ⟨by linarith [hj.2 ()], by linarith [hj.1 (), J.lower_lt_upper ()]⟩
    have hu : -J.lower () ∈ Icc A B := by
      dsimp only [intervalBox] at hj
      exact ⟨by linarith [hj.2 (), J.lower_lt_upper ()], by linarith [hj.1 ()]⟩
    simp only [cellSup, him, increment, he _ hl, he _ hu]
  have hvalue : stieltjesIntegral (intervalBox A B hAB) (fun x => f (ψ x)) ψ =
      stieltjesIntegral (intervalBox A B hAB) (fun x => f (φ x)) φ := by
    unfold stieltjesIntegral upperIntegral
    rw [show upperSum (I := intervalBox A B hAB) (fun x => f (ψ x)) ψ =
      upperSum (fun x => f (φ x)) φ from funext hsum]
  rw [← hvalue, hψ.2, hI]

end

end MathematicalAnalysis.Chapter05
