import Textbooks.MathematicalAnalysis.Chapter03.CompactContinuity
import Mathlib.Topology.MetricSpace.Lipschitz

namespace MathematicalAnalysis.Chapter03

open Set Metric NNReal
open scoped Topology

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- Definition: a Lipschitz map admits a positive real constant bounding the
distance between images by that constant times the original distance.
Allowing zero in the standard nonnegative constant gives the same class of maps. -/
theorem lipschitz_iff (f : X → Y) :
    (∃ K : ℝ≥0, LipschitzWith K f) ↔
      ∃ C : ℝ, 0 < C ∧ ∀ x y, dist (f x) (f y) ≤ C * dist x y := by
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K + 1, by positivity, ?_⟩
    intro x y
    exact (hK.dist_le_mul x y).trans
      (mul_le_mul_of_nonneg_right (by linarith) dist_nonneg)
  · rintro ⟨C, hC, h⟩
    exact ⟨⟨C, hC.le⟩, lipschitzWith_iff_dist_le_mul.mpr h⟩

/-- Definition: a locally Lipschitz function on a subset has a positive Lipschitz
constant on some ball intersected with that subset at every point of it. -/
theorem locallyLipschitzOn_iff (A : Set X) (f : X → Y) :
    LocallyLipschitzOn A f ↔ ∀ a ∈ A, ∃ δ > 0, ∃ C : ℝ, 0 < C ∧
      ∀ x ∈ ball a δ ∩ A, ∀ y ∈ ball a δ ∩ A,
        dist (f x) (f y) ≤ C * dist x y := by
  constructor
  · intro h a ha
    obtain ⟨K, t, ht, hK⟩ := h ha
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhdsWithin_iff.mp ht
    refine ⟨δ, hδ, K + 1, by positivity, ?_⟩
    intro x hx y hy
    exact (lipschitzOnWith_iff_dist_le_mul.mp hK x (hsub hx) y (hsub hy)).trans
      (mul_le_mul_of_nonneg_right (by linarith) dist_nonneg)
  · intro h a ha
    obtain ⟨δ, hδ, C, hC, hd⟩ := h a ha
    refine ⟨⟨C, hC.le⟩, ball a δ ∩ A,
      Metric.mem_nhdsWithin_iff.mpr ⟨δ, hδ, Subset.rfl⟩, ?_⟩
    exact lipschitzOnWith_iff_dist_le_mul.mpr hd

/-- Theorem: Lipschitz functions are uniformly continuous. -/
theorem uniformContinuous_of_lipschitz (f : X → Y) (K : ℝ≥0)
    (hf : LipschitzWith K f) : UniformContinuous f := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  have hK : 0 ≤ (K : ℝ) := K.property
  have hp : 0 < (K : ℝ) + 1 := by positivity
  refine ⟨ε / (K + 1), div_pos hε hp, ?_⟩
  intro x y hxy
  have hsmall := (lt_div_iff₀ hp).mp hxy
  have hbound := hf.dist_le_mul x y
  have hd : 0 ≤ dist x y := dist_nonneg
  nlinarith

/-- Corollary: the same uniform bound holds when the domain is a subset. -/
theorem uniformContinuousOn_of_lipschitz (A : Set X) (f : X → Y) (K : ℝ≥0)
    (hf : LipschitzOnWith K f A) : UniformContinuousOn f A := by
  have hsub : LipschitzWith K (fun x : A => f x) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    exact lipschitzOnWith_iff_dist_le_mul.mp hf x x.property y y.property
  have hu := uniformContinuous_of_lipschitz (fun x : A => f x) K hsub
  apply Metric.uniformContinuousOn_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  exact ⟨δ, hδ, fun x hx y hy hxy => hd (a := ⟨x, hx⟩) (b := ⟨y, hy⟩) hxy⟩

end MathematicalAnalysis.Chapter03
