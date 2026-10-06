import Textbooks.MathematicalAnalysis.Chapter05.ContinuousIntegrability
import Textbooks.MathematicalAnalysis.Chapter05.IntegrabilityOperations

namespace MathematicalAnalysis.Chapter05

open Set Metric BoxIntegral

noncomputable section

/-- Definition: a clipped linear function counts interval length in a neighborhood. -/
def neighborhoodLength (q r : ℝ) (x : ℝ) : ℝ := min (max (x - (q - r)) 0) (2 * r)

/-- Lemma: the clipped length is increasing and lies between zero and twice the radius. -/
theorem neighborhoodLength_bounds (q r : ℝ) (hr : 0 ≤ r) :
    Monotone (neighborhoodLength q r) ∧
      ∀ x, 0 ≤ neighborhoodLength q r x ∧ neighborhoodLength q r x ≤ 2 * r := by
  constructor
  · intro x y hxy
    exact min_le_min (max_le_max (sub_le_sub_right hxy _) le_rfl) le_rfl
  · intro x
    exact ⟨le_min (le_max_right _ _) (by positivity), min_le_right _ _⟩

/-- Lemma: the increment of the clipped length is the full length of a cell
contained in the corresponding closed neighborhood. -/
theorem neighborhoodLength_increment (J : Box Unit) (q r : ℝ)
    (hl : q - r ≤ -J.upper ()) (hu : -J.lower () ≤ q + r) :
    increment (neighborhoodLength q r) J = cellLength J := by
  have hm : -J.upper () ≤ -J.lower () := neg_le_neg (J.lower_le_upper ())
  have he (x : ℝ) (hx : q - r ≤ x) (hy : x ≤ q + r) :
      neighborhoodLength q r x = x - (q - r) := by
    dsimp only [neighborhoodLength]
    rw [max_eq_left (sub_nonneg.mpr hx), min_eq_left (by linarith)]
  dsimp only [increment]
  rw [he _ (hl.trans hm) hu, he _ hl (hm.trans hu)]
  dsimp only [cellLength]
  ring

/-- Theorem: a bounded function continuous outside a finite set is Riemann integrable. -/
theorem riemannIntegrable_finite_discontinuities (I : Box Unit) (f : ℝ → ℝ)
    (hf : Bornology.IsBounded (f '' Icc (-I.upper ()) (-I.lower ())))
    (E : Finset ℝ)
    (hc : ∀ x ∈ Icc (-I.upper ()) (-I.lower ()), x ∉ E →
      ContinuousWithinAt f (Icc (-I.upper ()) (-I.lower ())) x) :
    RiemannIntegrable I f := by
  classical
  obtain ⟨C, hC, hb⟩ := absolute_bound I f hf
  apply (riemannIntegrable_iff_gap I f hf).mpr
  intro ε hε
  let η := ε / (4 * (cellLength I + 1))
  let r := ε / (16 * (C + 1) * (E.card + 1))
  have hL := cellLength_pos I
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hr : 0 < r := by
    dsimp [r]
    positivity
  let A := Icc (-I.upper ()) (-I.lower ())
  have hex : ∀ q : A, ∃ d > 0, q.val ∉ E →
      ∀ x ∈ A, |x - q.val| < d → |f x - f q.val| < η := by
    intro q
    by_cases hq : q.val ∈ E
    · exact ⟨1, zero_lt_one, fun hn => (hn hq).elim⟩
    · obtain ⟨d, hd, he⟩ := Metric.continuousWithinAt_iff.mp
        (hc q q.property hq) η hη
      exact ⟨d, hd, fun _ x hx hnear => he hx (by simpa only [Real.dist_eq] using hnear)⟩
  choose d hd he using hex
  let radii := fun q : A => if q.val ∈ E then r else d q / 2
  obtain ⟨P, hP⟩ := partition_subordinate I radii (by
    intro q
    dsimp only [radii]
    split_ifs
    · exact hr
    · exact half_pos (hd q))
  choose q hq using hP
  let w := fun J : Box Unit => ∑ e ∈ E, increment (neighborhoodLength e r) J
  have hw : ∀ J ∈ P.val.boxes, 0 ≤ w J := by
    intro J _
    apply Finset.sum_nonneg
    intro e _
    exact sub_nonneg.mpr ((neighborhoodLength_bounds e r hr.le).1
      (neg_le_neg (J.lower_le_upper ())))
  have hosc : ∀ J ∈ P.val.boxes,
      (cellSup f J - cellInf f J) * cellLength J ≤ 2 * η * cellLength J + 2 * C * w J := by
    intro J hJ
    by_cases hbad : (q J hJ).val ∈ E
    · have hradius : radii (q J hJ) = r := by simp only [radii, hbad, ↓reduceIte]
      have hl := hq J hJ (-J.upper ()) ⟨le_rfl, neg_le_neg (J.lower_le_upper ())⟩
      have hu := hq J hJ (-J.lower ()) ⟨neg_le_neg (J.lower_le_upper ()), le_rfl⟩
      rw [hradius] at hl hu
      have hi := neighborhoodLength_increment J (q J hJ) r
        (by linarith [(abs_le.mp hl).1]) (by linarith [(abs_le.mp hu).2])
      have hlen : cellLength J ≤ w J := by
        rw [← hi]
        dsimp only [w]
        apply Finset.single_le_sum (f := fun e : ℝ => increment (neighborhoodLength e r) J)
          (a := (q J hJ).val)
        · intro e _
          exact sub_nonneg.mpr ((neighborhoodLength_bounds e r hr.le).1
            (neg_le_neg (J.lower_le_upper ())))
        · exact hbad
      have ho : cellSup f J - cellInf f J ≤ 2 * C := by
        apply cell_oscillation_bound f (P.val.le_of_mem hJ) hf
        intro x hx y hy
        exact (abs_sub _ _).trans (by
          have hbx := hb x (cell_subset_closed (P.val.le_of_mem hJ) hx)
          have hby := hb y (cell_subset_closed (P.val.le_of_mem hJ) hy)
          linarith)
      have hm := mul_le_mul_of_nonneg_right ho (cellLength_pos J).le
      have hn := mul_le_mul_of_nonneg_left hlen (by positivity : 0 ≤ 2 * C)
      nlinarith [cellLength_pos J]
    · have ho : cellSup f J - cellInf f J ≤ 2 * η := by
        apply cell_oscillation_bound f (P.val.le_of_mem hJ) hf
        intro x hx y hy
        have hn (z : ℝ) (hz : z ∈ cell J) : |f z - f (q J hJ)| < η := by
          apply he (q J hJ) hbad z (cell_subset_closed (P.val.le_of_mem hJ) hz)
          have hh := hq J hJ z ⟨hz.1, hz.2.le⟩
          simp only [radii, hbad, ↓reduceIte] at hh
          exact hh.trans_lt (half_lt_self (hd (q J hJ)))
        have ha := abs_sub_le (f x) (f (q J hJ)) (f y)
        rw [abs_sub_comm (f (q J hJ)) (f y)] at ha
        linarith [hn x hx, hn y hy]
      have hm := mul_le_mul_of_nonneg_right ho (cellLength_pos J).le
      have hn := mul_nonneg (by positivity : 0 ≤ 2 * C) (hw J hJ)
      linarith
  have hsumw : ∑ J ∈ P.val.boxes, w J ≤ E.card * (2 * r) := by
    dsimp only [w]
    rw [Finset.sum_comm]
    simp only [sum_increments]
    calc
      _ ≤ ∑ e ∈ E, 2 * r := by
        apply Finset.sum_le_sum
        intro e _
        have hl := (neighborhoodLength_bounds e r hr.le).2 (-I.upper ())
        have hu := (neighborhoodLength_bounds e r hr.le).2 (-I.lower ())
        dsimp only [increment]
        linarith [hl.1, hu.2]
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hgap : upperSum f id P - lowerSum f id P ≤
      2 * η * cellLength I + 2 * C * (E.card * (2 * r)) := by
    simp only [upperSum, lowerSum, ← Finset.sum_sub_distrib]
    have hi (J : Box Unit) : increment id J = cellLength J := by
      dsimp [increment, cellLength]
      ring
    simp only [hi, ← sub_mul]
    calc
      _ ≤ ∑ J ∈ P.val.boxes, (2 * η * cellLength J + 2 * C * w J) :=
        Finset.sum_le_sum hosc
      _ = 2 * η * cellLength I + 2 * C * ∑ J ∈ P.val.boxes, w J := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_cellLengths]
      _ ≤ _ := by
        have hm := mul_le_mul_of_nonneg_left hsumw (show 0 ≤ 2 * C by positivity)
        linarith
  have hηeq : η * (4 * (cellLength I + 1)) = ε := div_mul_cancel₀ ε (by positivity)
  have hreq : r * (16 * (C + 1) * (E.card + 1)) = ε := div_mul_cancel₀ ε (by positivity)
  refine ⟨P, hgap.trans_lt ?_⟩
  nlinarith [cellLength_pos I, Nat.cast_nonneg (α := ℝ) E.card,
    mul_pos hC hr, mul_nonneg (Nat.cast_nonneg (α := ℝ) E.card) hr.le]

end

end MathematicalAnalysis.Chapter05
