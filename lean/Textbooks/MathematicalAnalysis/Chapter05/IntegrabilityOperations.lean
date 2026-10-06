import Textbooks.MathematicalAnalysis.Chapter05.DarbouxCriterion

namespace MathematicalAnalysis.Chapter05

open Set BoxIntegral

noncomputable section

/-- Lemma: a bounded real function on an interval has a positive absolute bound. -/
theorem absolute_bound (I : Box Unit) (f : ℝ → ℝ)
    (hf : Bornology.IsBounded (f '' Icc (-I.upper ()) (-I.lower ()))) :
    ∃ C > 0, ∀ x ∈ Icc (-I.upper ()) (-I.lower ()), |f x| ≤ C := by
  obtain ⟨u, hu⟩ := hf.bddAbove
  obtain ⟨l, hl⟩ := hf.bddBelow
  refine ⟨|u| + |l| + 1, by positivity, ?_⟩
  intro x hx
  have hup := hu ⟨x, hx, rfl⟩
  have hlo := hl ⟨x, hx, rfl⟩
  exact abs_le.mpr ⟨by linarith [le_abs_self l, neg_abs_le l, abs_nonneg u],
    by linarith [le_abs_self u, abs_nonneg l]⟩

/-- Lemma: an absolute bound implies boundedness of the image. -/
theorem bounded_of_absolute_bound (I : Box Unit) (f : ℝ → ℝ) (C : ℝ)
    (hC : ∀ x ∈ Icc (-I.upper ()) (-I.lower ()), |f x| ≤ C) :
    Bornology.IsBounded (f '' Icc (-I.upper ()) (-I.lower ())) := by
  have hu : BddAbove (f '' Icc (-I.upper ()) (-I.lower ())) := by
    refine ⟨C, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact (abs_le.mp (hC x hx)).2

  have hl : BddBelow (f '' Icc (-I.upper ()) (-I.lower ())) := by
    refine ⟨-C, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact (abs_le.mp (hC x hx)).1

  exact hu.isBounded hl

/-- Lemma: the oscillation on a cell bounds every difference of two function values. -/
theorem cell_difference_bound {I J : Box Unit} (f : ℝ → ℝ) (hJI : J ≤ I)
    (hf : Bornology.IsBounded (f '' Icc (-I.upper ()) (-I.lower ())))
    (x y : ℝ) (hx : x ∈ cell J) (hy : y ∈ cell J) :
    |f x - f y| ≤ cellSup f J - cellInf f J := by
  have hb := cell_image_bounded f hJI hf
  have hxu := le_csSup hb.bddAbove (show f x ∈ f '' cell J from ⟨x, hx, rfl⟩)
  have hyu := le_csSup hb.bddAbove (show f y ∈ f '' cell J from ⟨y, hy, rfl⟩)
  have hxl := csInf_le hb.bddBelow (show f x ∈ f '' cell J from ⟨x, hx, rfl⟩)
  have hyl := csInf_le hb.bddBelow (show f y ∈ f '' cell J from ⟨y, hy, rfl⟩)
  dsimp only [cellSup, cellInf]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Lemma: a bound on every pairwise difference bounds the cell oscillation. -/
theorem cell_oscillation_bound {I J : Box Unit} (f : ℝ → ℝ) (hJI : J ≤ I)
    (hf : Bornology.IsBounded (f '' Icc (-I.upper ()) (-I.lower ()))) (C : ℝ)
    (hC : ∀ x ∈ cell J, ∀ y ∈ cell J, |f x - f y| ≤ C) :
    cellSup f J - cellInf f J ≤ C := by
  have hb := cell_image_bounded f hJI hf
  have hsup : ∀ y ∈ cell J, cellSup f J ≤ C + f y := by
    intro y hy
    apply csSup_le (cell_image_nonempty f J)
    rintro z ⟨x, hx, rfl⟩
    have h := (abs_le.mp (hC x hx y hy)).2
    linarith

  have hinf : cellSup f J - C ≤ cellInf f J := by
    apply le_csInf (cell_image_nonempty f J)
    rintro z ⟨y, hy, rfl⟩
    have h := hsup y hy
    linarith

  linarith

/-- Lemma: an oscillation bound transfers Riemann integrability to a function
controlled by two integrable functions. -/
theorem riemannIntegrable_of_difference_bound (I : Box Unit) (f g h : ℝ → ℝ)
    (hf : RiemannIntegrable I f) (hg : RiemannIntegrable I g)
    (hh : Bornology.IsBounded (h '' Icc (-I.upper ()) (-I.lower ())))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcontrol : ∀ x ∈ Icc (-I.upper ()) (-I.lower ()),
      ∀ y ∈ Icc (-I.upper ()) (-I.lower ()),
      |h x - h y| ≤ A * |f x - f y| + B * |g x - g y|) : RiemannIntegrable I h := by
  apply (riemannIntegrable_iff_gap I h hh).mpr
  intro ε hε
  let δ := ε / (2 * (A + B + 1))
  have hp : 0 < 2 * (A + B + 1) := by linarith
  have hδ : 0 < δ := div_pos hε hp

  obtain ⟨P, hP⟩ := (riemannIntegrable_iff_gap I f hf.1).mp hf δ hδ
  obtain ⟨Q, hQ⟩ := (riemannIntegrable_iff_gap I g hg.1).mp hg δ hδ
  let R := commonRefinement P Q
  have hfr := refinement_sums f id P R inf_le_left hf.1 (fun _ _ _ _ h => h)
  have hgr := refinement_sums g id Q R inf_le_right hg.1 (fun _ _ _ _ h => h)
  have hosc : ∀ J ∈ R.val.boxes, cellSup h J - cellInf h J ≤
      A * (cellSup f J - cellInf f J) + B * (cellSup g J - cellInf g J) := by
    intro J hJ
    apply cell_oscillation_bound h (R.val.le_of_mem hJ) hh
    intro x hx y hy
    have hxy := hcontrol x (cell_subset_closed (R.val.le_of_mem hJ) hx)
      y (cell_subset_closed (R.val.le_of_mem hJ) hy)
    exact hxy.trans (add_le_add
      (mul_le_mul_of_nonneg_left (cell_difference_bound f (R.val.le_of_mem hJ) hf.1 x y hx hy) hA)
      (mul_le_mul_of_nonneg_left (cell_difference_bound g (R.val.le_of_mem hJ) hg.1 x y hx hy) hB))

  have hsum : upperSum h id R - lowerSum h id R ≤
      A * (upperSum f id R - lowerSum f id R) +
        B * (upperSum g id R - lowerSum g id R) := by
    simp only [upperSum, lowerSum, ← Finset.sum_sub_distrib, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro J hJ
    have hweight : 0 ≤ increment id J := by
      dsimp only [increment, id_eq]
      linarith [J.lower_lt_upper ()]

    have hmul := mul_le_mul_of_nonneg_right (hosc J hJ) hweight
    nlinarith only [hmul]

  have hfsmall : upperSum f id R - lowerSum f id R ≤ δ := by linarith [hfr.1, hfr.2]
  have hgsmall : upperSum g id R - lowerSum g id R ≤ δ := by linarith [hgr.1, hgr.2]
  have ha := mul_le_mul_of_nonneg_left hfsmall hA
  have hb := mul_le_mul_of_nonneg_left hgsmall hB
  have heq : δ * (2 * (A + B + 1)) = ε := div_mul_cancel₀ ε hp.ne'

  exact ⟨R, by nlinarith⟩

/-- Theorem: the sum of Riemann integrable functions is Riemann integrable. -/
theorem riemannIntegrable_add (I : Box Unit) (f g : ℝ → ℝ)
    (hf : RiemannIntegrable I f) (hg : RiemannIntegrable I g) :
    RiemannIntegrable I (fun x => f x + g x) := by
  obtain ⟨C, _, hC⟩ := absolute_bound I f hf.1
  obtain ⟨D, _, hD⟩ := absolute_bound I g hg.1
  have hb := bounded_of_absolute_bound I (fun x => f x + g x) (C + D)
    (fun x hx => (abs_add_le _ _).trans (add_le_add (hC x hx) (hD x hx)))

  apply riemannIntegrable_of_difference_bound I f g _ hf hg hb 1 1 zero_le_one zero_le_one
  intro x _ y _
  rw [show f x + g x - (f y + g y) = (f x - f y) + (g x - g y) by ring, one_mul, one_mul]
  exact abs_add_le _ _

/-- Theorem: scalar multiples of Riemann integrable functions are integrable. -/
theorem riemannIntegrable_const_mul (I : Box Unit) (f : ℝ → ℝ) (c : ℝ)
    (hf : RiemannIntegrable I f) : RiemannIntegrable I (fun x => c * f x) := by
  obtain ⟨C, _, hC⟩ := absolute_bound I f hf.1
  have hb := bounded_of_absolute_bound I (fun x => c * f x) (|c| * C) (by
    intro x hx
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hC x hx) (abs_nonneg c))

  apply riemannIntegrable_of_difference_bound I f f _ hf hf hb |c| 0 (abs_nonneg c) le_rfl
  intro x _ y _
  rw [← mul_sub, abs_mul, zero_mul, add_zero]

/-- Theorem: the absolute value of a Riemann integrable function is integrable. -/
theorem riemannIntegrable_abs (I : Box Unit) (f : ℝ → ℝ) (hf : RiemannIntegrable I f) :
    RiemannIntegrable I (fun x => |f x|) := by
  obtain ⟨C, _, hC⟩ := absolute_bound I f hf.1
  have hb := bounded_of_absolute_bound I (fun x => |f x|) C (by
    intro x hx
    simpa only [abs_abs] using hC x hx)
  apply riemannIntegrable_of_difference_bound I f f _ hf hf hb 1 0 zero_le_one le_rfl
  intro x _ y _
  simpa only [one_mul, zero_mul, add_zero] using abs_abs_sub_abs_le_abs_sub (f x) (f y)

/-- Theorem: the product of bounded Riemann integrable functions is integrable. -/
theorem riemannIntegrable_mul (I : Box Unit) (f g : ℝ → ℝ)
    (hf : RiemannIntegrable I f) (hg : RiemannIntegrable I g) :
    RiemannIntegrable I (fun x => f x * g x) := by
  obtain ⟨C, hCpos, hC⟩ := absolute_bound I f hf.1
  obtain ⟨D, hDpos, hD⟩ := absolute_bound I g hg.1
  have hb := bounded_of_absolute_bound I (fun x => f x * g x) (C * D) (by
    intro x hx
    rw [abs_mul]
    exact mul_le_mul (hC x hx) (hD x hx) (abs_nonneg _) hCpos.le)

  apply riemannIntegrable_of_difference_bound I f g _ hf hg hb D C hDpos.le hCpos.le
  intro x hx y hy
  rw [show f x * g x - f y * g y = (f x - f y) * g x + f y * (g x - g y) by ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]

  have hleft := mul_le_mul_of_nonneg_left (hD x hx) (abs_nonneg (f x - f y))
  have hright := mul_le_mul_of_nonneg_right (hC y hy) (abs_nonneg (g x - g y))
  nlinarith only [hleft, hright]

end

end MathematicalAnalysis.Chapter05
