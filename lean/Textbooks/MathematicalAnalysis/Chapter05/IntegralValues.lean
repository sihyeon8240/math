import Textbooks.MathematicalAnalysis.Chapter05.IntegrabilityOperations

namespace MathematicalAnalysis.Chapter05

open Set BoxIntegral

noncomputable section

/-- Definition: the Riemann integral is the common Darboux value when integrable. -/
def riemannIntegral (I : Box Unit) (f : ℝ → ℝ) : ℝ := upperIntegral I f id

/-- Definition: a tagged Riemann sum selects one point in each interval cell. -/
def taggedSum {I : Box Unit} (f : ℝ → ℝ) (P : Partition I) (τ : Box Unit → ℝ) : ℝ :=
  ∑ J ∈ P.val.boxes, f (τ J) * cellLength J

/-- Lemma: every tagged sum lies between the lower and upper sums. -/
theorem taggedSum_bounds {I : Box Unit} (f : ℝ → ℝ) (P : Partition I) (τ : Box Unit → ℝ)
    (hτ : ∀ J ∈ P.val.boxes, τ J ∈ cell J)
    (hf : Bornology.IsBounded (f '' Icc (-I.upper ()) (-I.lower ()))) :
    lowerSum f id P ≤ taggedSum f P τ ∧ taggedSum f P τ ≤ upperSum f id P := by
  constructor
  · apply Finset.sum_le_sum
    intro J hJ
    have hb := cell_image_bounded f (P.val.le_of_mem hJ) hf
    have hi : increment id J = cellLength J := by
      dsimp [increment, cellLength]
      ring
    rw [hi]
    exact mul_le_mul_of_nonneg_right (csInf_le hb.bddBelow ⟨τ J, hτ J hJ, rfl⟩)
      (cellLength_pos J).le

  · apply Finset.sum_le_sum
    intro J hJ
    have hb := cell_image_bounded f (P.val.le_of_mem hJ) hf
    have hi : increment id J = cellLength J := by
      dsimp [increment, cellLength]
      ring
    rw [hi]
    exact mul_le_mul_of_nonneg_right (le_csSup hb.bddAbove ⟨τ J, hτ J hJ, rfl⟩)
      (cellLength_pos J).le

/-- Lemma: the error of a tagged sum is bounded by the Darboux gap. -/
theorem taggedSum_error {I : Box Unit} (f : ℝ → ℝ) (P : Partition I) (τ : Box Unit → ℝ)
    (hτ : ∀ J ∈ P.val.boxes, τ J ∈ cell J) (hf : RiemannIntegrable I f) :
    |riemannIntegral I f - taggedSum f P τ| ≤ upperSum f id P - lowerSum f id P := by
  obtain ⟨hl, _, hu⟩ := integral_bounds I f id P hf.1 (fun _ _ _ _ h => h)
  obtain ⟨htl, htu⟩ := taggedSum_bounds f P τ hτ hf.1
  dsimp only [riemannIntegral]
  exact abs_le.mpr ⟨by linarith [hf.2], by linarith [hf.2]⟩

/-- Theorem: the Riemann integral preserves pointwise inequalities. -/
theorem riemannIntegral_mono (I : Box Unit) (f g : ℝ → ℝ)
    (hf : RiemannIntegrable I f) (hg : RiemannIntegrable I g)
    (hfg : ∀ x ∈ Icc (-I.upper ()) (-I.lower ()), f x ≤ g x) :
    riemannIntegral I f ≤ riemannIntegral I g := by
  obtain ⟨hU, _, _, _⟩ := sum_ranges_bounded I g id hg.1 (fun _ _ _ _ h => h)
  apply le_csInf hU
  rintro z ⟨P, rfl⟩
  have hsum : upperSum f id P ≤ upperSum g id P := by
    apply Finset.sum_le_sum
    intro J hJ
    have hjg := cell_image_bounded g (P.val.le_of_mem hJ) hg.1
    have hsup : cellSup f J ≤ cellSup g J := by
      apply csSup_le (cell_image_nonempty f J)
      rintro y ⟨x, hx, rfl⟩
      exact (hfg x (cell_subset_closed (P.val.le_of_mem hJ) hx)).trans
        (le_csSup hjg.bddAbove ⟨x, hx, rfl⟩)

    exact mul_le_mul_of_nonneg_right hsup
      (increment_nonneg id (P.val.le_of_mem hJ) (fun _ _ _ _ h => h))

  exact (integral_bounds I f id P hf.1 (fun _ _ _ _ h => h)).2.2.trans hsum

/-- Theorem: an absolute bound on the integrand bounds the absolute integral
by that bound times the interval length. -/
theorem riemannIntegral_abs_le (I : Box Unit) (f : ℝ → ℝ) (hf : RiemannIntegrable I f)
    (C : ℝ) (hC : ∀ x ∈ Icc (-I.upper ()) (-I.lower ()), |f x| ≤ C) :
    |riemannIntegral I f| ≤ C * cellLength I := by
  let P : Partition I := ⟨⊤, Prepartition.isPartitionTop I⟩
  have hupper : upperSum f id P ≤ C * cellLength I := by
    dsimp only [upperSum]
    rw [← sum_cellLengths P, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro J hJ
    have hsup : cellSup f J ≤ C := by
      apply csSup_le (cell_image_nonempty f J)
      rintro y ⟨x, hx, rfl⟩
      exact (abs_le.mp (hC x (cell_subset_closed (P.val.le_of_mem hJ) hx))).2

    have hi : increment id J = cellLength J := by
      dsimp [increment, cellLength]
      ring
    rw [hi]
    exact mul_le_mul_of_nonneg_right hsup (cellLength_pos J).le

  have hlower : -C * cellLength I ≤ lowerSum f id P := by
    dsimp only [lowerSum]
    rw [← sum_cellLengths P, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro J hJ
    have hinf : -C ≤ cellInf f J := by
      apply le_csInf (cell_image_nonempty f J)
      rintro y ⟨x, hx, rfl⟩
      exact (abs_le.mp (hC x (cell_subset_closed (P.val.le_of_mem hJ) hx))).1

    have hi : increment id J = cellLength J := by
      dsimp [increment, cellLength]
      ring
    rw [hi]
    exact mul_le_mul_of_nonneg_right hinf (cellLength_pos J).le

  obtain ⟨hl, _, hu⟩ := integral_bounds I f id P hf.1 (fun _ _ _ _ h => h)
  dsimp only [riemannIntegral]
  exact abs_le.mpr ⟨by linarith [hf.2], by linarith⟩

/-- Lemma: partitions with a small Darboux gap approximate the integral. -/
theorem riemannIntegral_eq_of_taggedSum (I : Box Unit) (f : ℝ → ℝ)
    (hf : RiemannIntegrable I f) (v : ℝ)
    (hv : ∀ P : Partition I, ∃ τ : Box Unit → ℝ,
      (∀ J ∈ P.val.boxes, τ J ∈ cell J) ∧ taggedSum f P τ = v) :
    riemannIntegral I f = v := by
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨P, hP⟩ := (riemannIntegrable_iff_gap I f hf.1).mp hf ε hε
  obtain ⟨τ, hτ, hval⟩ := hv P
  have he := taggedSum_error f P τ hτ hf
  rw [hval] at he
  linarith

/-- Theorem: the Riemann integral is linear. -/
theorem riemannIntegral_linear (I : Box Unit) (f g : ℝ → ℝ) (A B : ℝ)
    (hf : RiemannIntegrable I f) (hg : RiemannIntegrable I g) :
    riemannIntegral I (fun x => A * f x + B * g x) =
      A * riemannIntegral I f + B * riemannIntegral I g := by
  let h := fun x => A * f x + B * g x
  have hh := riemannIntegrable_add I _ _
    (riemannIntegrable_const_mul I f A hf) (riemannIntegrable_const_mul I g B hg)
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / (2 * (|A| + |B| + 1))
  have hp : 0 < 2 * (|A| + |B| + 1) := by positivity
  have hδ : 0 < δ := div_pos hε hp

  obtain ⟨P, hP⟩ := (riemannIntegrable_iff_gap I f hf.1).mp hf δ hδ
  obtain ⟨Q, hQ⟩ := (riemannIntegrable_iff_gap I g hg.1).mp hg δ hδ
  obtain ⟨S, hS⟩ := (riemannIntegrable_iff_gap I h hh.1).mp hh δ hδ
  let R := commonRefinement (commonRefinement P Q) S
  let τ := fun J : Box Unit => -J.upper ()
  have hτ : ∀ J ∈ R.val.boxes, τ J ∈ cell J := by
    intro J _
    exact ⟨le_rfl, neg_lt_neg (J.lower_lt_upper ())⟩

  have he (k : ℝ → ℝ) (hk : RiemannIntegrable I k) (T : Partition I)
      (hRT : Refines R T) (hT : upperSum k id T - lowerSum k id T < δ) :
      |riemannIntegral I k - taggedSum k R τ| ≤ δ := by
    have hr := refinement_sums k id T R hRT hk.1 (fun _ _ _ _ h => h)
    have ht := taggedSum_error k R τ hτ hk
    linarith [hr.1, hr.2]

  have ef := he f hf P (inf_le_left.trans inf_le_left) hP
  have eg := he g hg Q (inf_le_left.trans inf_le_right) hQ
  have eh := he h hh S inf_le_right hS
  have hs : taggedSum h R τ = A * taggedSum f R τ + B * taggedSum g R τ := by
    simp only [taggedSum, h, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro J _
    ring

  have hid : riemannIntegral I h - (A * riemannIntegral I f + B * riemannIntegral I g) =
      (riemannIntegral I h - taggedSum h R τ) -
        (A * (riemannIntegral I f - taggedSum f R τ) +
          B * (riemannIntegral I g - taggedSum g R τ)) := by
    rw [hs]
    ring
  rw [hid]

  have hb : |(riemannIntegral I h - taggedSum h R τ) -
      (A * (riemannIntegral I f - taggedSum f R τ) +
        B * (riemannIntegral I g - taggedSum g R τ))| ≤
      |riemannIntegral I h - taggedSum h R τ| +
        |A * (riemannIntegral I f - taggedSum f R τ)| +
        |B * (riemannIntegral I g - taggedSum g R τ)| := by
    calc
      _ ≤ |riemannIntegral I h - taggedSum h R τ| +
          |A * (riemannIntegral I f - taggedSum f R τ) +
            B * (riemannIntegral I g - taggedSum g R τ)| := abs_sub _ _
      _ ≤ _ := by linarith [(abs_add_le
        (A * (riemannIntegral I f - taggedSum f R τ))
        (B * (riemannIntegral I g - taggedSum g R τ)))]
  rw [abs_mul, abs_mul] at hb

  have ea := mul_le_mul_of_nonneg_left ef (abs_nonneg A)
  have eb := mul_le_mul_of_nonneg_left eg (abs_nonneg B)
  have hd : δ * (2 * (|A| + |B| + 1)) = ε := div_mul_cancel₀ ε hp.ne'

  nlinarith only [hb, ea, eb, eh, hd, hδ, abs_nonneg A, abs_nonneg B]

/-- Theorem: the absolute integral is at most the integral of the absolute value. -/
theorem abs_riemannIntegral_le (I : Box Unit) (f : ℝ → ℝ)
    (hf : RiemannIntegrable I f) :
    |riemannIntegral I f| ≤ riemannIntegral I (fun x => |f x|) := by
  have ha := riemannIntegrable_abs I f hf
  have hu := riemannIntegral_mono I f _ hf ha (fun x _ => le_abs_self (f x))
  have hn := riemannIntegrable_const_mul I f (-1) hf
  have hl := riemannIntegral_mono I (fun x => -1 * f x) _ hn ha
    (fun x _ => by simpa using neg_le_abs (f x))
  have he := riemannIntegral_linear I f f (-1) 0 hf hf
  simp only [zero_mul, add_zero, neg_one_mul] at he hl
  rw [he] at hl
  exact abs_le.mpr ⟨by linarith, hu⟩

end

end MathematicalAnalysis.Chapter05
