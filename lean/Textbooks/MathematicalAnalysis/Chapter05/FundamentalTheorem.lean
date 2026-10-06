import Textbooks.MathematicalAnalysis.Chapter05.IntegralValues
import Textbooks.MathematicalAnalysis.Chapter04.MeanValue
import Textbooks.MathematicalAnalysis.Chapter04.DerivativeAlgebra
import Textbooks.MathematicalAnalysis.Chapter05.ContinuousIntegrability

namespace MathematicalAnalysis.Chapter05

open Set BoxIntegral

noncomputable section

/-- Theorem: integrating an integrable derivative recovers the endpoint difference. -/
theorem integral_derivative (I : Box Unit) (F f : ℝ → ℝ)
    (hF : ContinuousOn F (Icc (-I.upper ()) (-I.lower ())))
    (hd : ∀ x ∈ Ioo (-I.upper ()) (-I.lower ()), HasDerivAt F (f x) x)
    (hf : RiemannIntegrable I f) :
    riemannIntegral I f = F (-I.lower ()) - F (-I.upper ()) := by
  classical
  apply riemannIntegral_eq_of_taggedSum I f hf
  intro P
  have hm : ∀ J ∈ P.val.boxes, ∃ c ∈ Ioo (-J.upper ()) (-J.lower ()),
      f c = (F (-J.lower ()) - F (-J.upper ())) / cellLength J := by
    intro J hJ
    have hJI := Box.le_iff_bounds.mp (P.val.le_of_mem hJ)
    have hs : Icc (-J.upper ()) (-J.lower ()) ⊆ Icc (-I.upper ()) (-I.lower ()) := by
      intro x hx
      exact ⟨(neg_le_neg (hJI.2 ())).trans hx.1,
        hx.2.trans (neg_le_neg (hJI.1 ()))⟩
    rw [show cellLength J = -J.lower () - -J.upper () by
      dsimp [cellLength]
      ring]
    apply Chapter04.mean_value F f (-J.upper ()) (-J.lower ())
      (neg_lt_neg (J.lower_lt_upper ())) (hF.mono hs)
    intro x hx
    apply hd x
    exact ⟨(neg_le_neg (hJI.2 ())).trans_lt hx.1,
      hx.2.trans_le (neg_le_neg (hJI.1 ()))⟩
  choose τ hτ hval using hm
  let tag := fun J => if hJ : J ∈ P.val.boxes then τ J hJ else -J.upper ()
  refine ⟨tag, ?_, ?_⟩
  · intro J hJ
    simp only [tag, dite_eq_left hJ]
    exact ⟨(hτ J hJ).1.le, (hτ J hJ).2⟩
  · calc
      taggedSum f P tag = ∑ J ∈ P.val.boxes, increment F J := by
        apply Finset.sum_congr rfl
        intro J hJ
        simp only [tag, dite_eq_left hJ]
        rw [hval J hJ, div_mul_cancel₀ _ (cellLength_pos J).ne']
        rfl
      _ = F (-I.lower ()) - F (-I.upper ()) := sum_increments P F

/-- Theorem: integration by parts follows from the product rule and the
fundamental theorem. -/
theorem integration_by_parts (I : Box Unit) (F G f g : ℝ → ℝ)
    (hF : ContinuousOn F (Icc (-I.upper ()) (-I.lower ())))
    (hG : ContinuousOn G (Icc (-I.upper ()) (-I.lower ())))
    (hdF : ∀ x ∈ Ioo (-I.upper ()) (-I.lower ()), HasDerivAt F (f x) x)
    (hdG : ∀ x ∈ Ioo (-I.upper ()) (-I.lower ()), HasDerivAt G (g x) x)
    (hf : RiemannIntegrable I f) (hg : RiemannIntegrable I g) :
    riemannIntegral I (fun x => F x * g x) =
      F (-I.lower ()) * G (-I.lower ()) - F (-I.upper ()) * G (-I.upper ()) -
        riemannIntegral I (fun x => f x * G x) := by
  have hFG : ContinuousOn (fun x => F x * G x)
      (Icc (-I.upper ()) (-I.lower ())) := by
    apply (Chapter03.continuousOn_iff_restrict _ _).mpr
    exact Chapter03.continuous_mul _ _
      ((Chapter03.continuousOn_iff_restrict _ _).mp hF)
      ((Chapter03.continuousOn_iff_restrict _ _).mp hG)
  have hfg := riemannIntegrable_mul I f G hf (continuous_riemannIntegrable I G hG)
  have hFg := riemannIntegrable_mul I F g (continuous_riemannIntegrable I F hF) hg
  have he := integral_derivative I (fun x => F x * G x)
    (fun x => f x * G x + F x * g x) hFG
    (fun x hx => Chapter04.hasDerivAt_product F G (f x) (g x) x (hdF x hx) (hdG x hx))
    (riemannIntegrable_add I _ _ hfg hFg)
  have hl := riemannIntegral_linear I (fun x => f x * G x) (fun x => F x * g x)
    1 1 hfg hFg
  simp only [one_mul] at hl
  rw [hl] at he
  linarith

end

end MathematicalAnalysis.Chapter05
