import Textbooks.MathematicalAnalysis.Chapter03.FunctionLimits
import Textbooks.MathematicalAnalysis.Chapter01.CompactSets

namespace MathematicalAnalysis.Chapter03

open Set Metric Filter
open scoped Topology
open MathematicalAnalysis.Chapter02

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]

/-- Theorem: continuity is equivalent to openness of all open-set preimages. -/
theorem continuous_iff_open_preimage (f : X → Y) :
    Continuous f ↔ ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U) := by
  constructor
  · intro hf U hU
    apply Metric.isOpen_iff.mpr
    intro a ha
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU (f a) ha
    obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hf.continuousAt ε hε
    exact ⟨δ, hδ, fun x hx => hball (hd hx)⟩

  · intro h
    apply Metric.continuous_iff.mpr
    intro a ε hε
    have hopen := h (ball (f a) ε) (MathematicalAnalysis.Chapter01.ball_open _ _)

    obtain ⟨δ, hδ, hd⟩ := Metric.isOpen_iff.mp hopen a (mem_ball_self hε)
    exact ⟨δ, hδ, fun x hx => hd hx⟩

/-- Theorem: composition preserves continuity at a point. Subset domains are
represented by subtypes, so the intermediate map has its stated codomain. -/
theorem continuousAt_comp (f : X → Y) (g : Y → Z) (a : X)
    (hf : ContinuousAt f a) (hg : ContinuousAt g (f a)) :
    ContinuousAt (g ∘ f) a := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨η, hη, houter⟩ := Metric.continuousAt_iff.mp hg ε hε
  obtain ⟨δ, hδ, hinner⟩ := Metric.continuousAt_iff.mp hf η hη
  exact ⟨δ, hδ, fun _ hx => houter (hinner hx)⟩

/-- Corollary: a composition of continuous functions is continuous. -/
theorem continuous_comp (f : X → Y) (g : Y → Z)
    (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  exact continuousAt_comp f g a hf.continuousAt hg.continuousAt

/-- Theorem: the sum of two continuous real functions is continuous. -/
theorem continuous_add (f g : X → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x + g x) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  apply (continuousAt_iff_sequences _ a).mpr
  intro u hu
  exact real_tendsto_add (f ∘ u) (g ∘ u) (f a) (g a)
    ((continuousAt_iff_sequences f a).mp hf.continuousAt u hu)
    ((continuousAt_iff_sequences g a).mp hg.continuousAt u hu)

/-- Theorem: the product of two continuous real functions is continuous. -/
theorem continuous_mul (f g : X → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x * g x) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  apply (continuousAt_iff_sequences _ a).mpr
  intro u hu
  exact real_tendsto_mul (f ∘ u) (g ∘ u) (f a) (g a)
    ((continuousAt_iff_sequences f a).mp hf.continuousAt u hu)
    ((continuousAt_iff_sequences g a).mp hg.continuousAt u hu)

/-- Lemma: a constant real function is continuous. -/
theorem continuous_const (c : ℝ) : Continuous (fun _ : X => c) := by
  apply Metric.continuous_iff.mpr
  intro _ ε hε
  exact ⟨1, zero_lt_one, fun _ _ => by simpa only [dist_self] using hε⟩

/-- Theorem: the difference of two continuous real functions is continuous. -/
theorem continuous_sub (f g : X → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x - g x) := by
  simpa only [neg_one_mul, sub_eq_add_neg] using
    continuous_add f (fun x => -1 * g x) hf
      (continuous_mul (fun _ => -1) g (continuous_const (-1)) hg)

/-- Theorem: reciprocals of a nowhere-zero continuous real function are continuous. -/
theorem continuous_inv (f : X → ℝ) (hf : Continuous f) (h0 : ∀ x, f x ≠ 0) :
    Continuous (fun x => 1 / f x) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  apply (continuousAt_iff_sequences _ a).mpr
  intro u hu
  exact real_tendsto_inv (f ∘ u) (f a)
    ((continuousAt_iff_sequences f a).mp hf.continuousAt u hu)
    (fun n => h0 (u n)) (h0 a)

/-- Theorem: the quotient of continuous real functions is continuous when its
denominator is nowhere zero. -/
theorem continuous_div (f g : X → ℝ) (hf : Continuous f) (hg : Continuous g)
    (h0 : ∀ x, g x ≠ 0) : Continuous (fun x => f x / g x) := by
  simpa only [div_eq_mul_inv, one_mul] using
    continuous_mul f (fun x => 1 / g x) hf (continuous_inv g hg h0)

/-- Theorem: a Euclidean-valued function is continuous exactly when each
coordinate function is continuous, including dimension zero. -/
theorem continuous_euclidean_iff (m : ℕ) (f : X → EuclideanSpace ℝ (Fin m)) :
    Continuous f ↔ ∀ j, Continuous (fun x => f x j) := by
  constructor
  · intro hf j
    apply Metric.continuous_iff.mpr
    intro a ε hε
    obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hf.continuousAt ε hε
    exact ⟨δ, hδ, fun x hx => (PiLp.dist_apply_le (f x) (f a) j).trans_lt (hd hx)⟩

  · intro h
    have hpi : Continuous (fun x => (fun j => f x j : Fin m → ℝ)) := by
      apply Metric.continuous_iff.mpr
      intro a ε hε
      have hex : ∀ j, ∃ δ > 0, ∀ ⦃x⦄,
          dist x a < δ → dist (f x j) (f a j) < ε := by
        intro j
        exact Metric.continuousAt_iff.mp (h j).continuousAt ε hε

      choose r hr hd using hex
      obtain ⟨δ, hδ, hle⟩ := MathematicalAnalysis.Chapter01.finite_positive_lower_bound
        Finset.univ r (fun j _ => hr j)

      refine ⟨δ, hδ, ?_⟩
      intro x hx
      exact (dist_pi_lt_iff hε).mpr (fun j => hd j (hx.trans_le (hle j (Finset.mem_univ j))))

    exact continuous_comp (fun x => (fun j => f x j : Fin m → ℝ))
      (fun x => (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))) hpi
      (MathematicalAnalysis.Chapter01.continuous_to_euclidean m)

end MathematicalAnalysis.Chapter03
