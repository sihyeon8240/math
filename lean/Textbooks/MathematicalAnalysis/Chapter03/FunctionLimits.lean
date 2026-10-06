import Textbooks.MathematicalAnalysis.Chapter02.SpecialSequences

namespace MathematicalAnalysis.Chapter03

open Set Metric Filter
open scoped Topology

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- Lemma: an open real ball is the corresponding open interval. -/
theorem real_ball_eq_Ioo (a r : ℝ) : ball a r = Ioo (a - r) (a + r) := by
  ext x
  rw [mem_ball, Real.dist_eq, abs_lt, mem_Ioo]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Definition: a punctured function limit uses the neighborhood filter with the
point itself removed; the value at that point is unrestricted. -/
theorem punctured_limit_iff (f : X → Y) (a : X) (L : Y) :
    Tendsto f (𝓝[≠] a) (𝓝 L) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < dist x a → dist x a < δ → dist (f x) L < ε := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  simp only [mem_compl_iff, mem_singleton_iff, dist_pos]

/-- Lemma: the punctured epsilon-delta condition says that the image of a
small punctured ball lies in the prescribed ball about the limit. -/
theorem punctured_limit_iff_image (f : X → Y) (a : X) (L : Y) :
    Tendsto f (𝓝[≠] a) (𝓝 L) ↔ ∀ ε > 0, ∃ δ > 0,
      f '' (ball a δ \ {a}) ⊆ ball L ε := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hd⟩ := h ε hε
    refine ⟨δ, hδ, ?_⟩
    rintro y ⟨x, ⟨hx, hxa⟩, rfl⟩
    exact hd hxa hx

  · intro h ε hε
    obtain ⟨δ, hδ, hd⟩ := h ε hε
    exact ⟨δ, hδ, fun x hx hxa => hd ⟨x, ⟨hxa, hx⟩, rfl⟩⟩

/-- Lemma: limits within a set are characterized by sequences lying in that set. -/
theorem tendsto_within_iff_sequences (f : X → Y) (s : Set X) (a : X) (L : Y) :
    Tendsto f (𝓝[s] a) (𝓝 L) ↔
      ∀ u : ℕ → X, (∀ n, u n ∈ s) → Tendsto u atTop (𝓝 a) →
        Tendsto (f ∘ u) atTop (𝓝 L) := by
  classical
  constructor

  · intro hf u hs hu
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := Metric.tendsto_nhdsWithin_nhds.mp hf ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hu δ hδ
    exact ⟨N, fun n hn => h (hs n) (hN n hn)⟩

  · intro h
    by_contra hf
    rw [Metric.tendsto_nhdsWithin_nhds] at hf
    push Not at hf

    obtain ⟨ε, hε, hbad⟩ := hf
    have hex : ∀ n : ℕ, ∃ x ∈ s,
        dist x a < 1 / (n + 1 : ℝ) ∧ ε ≤ dist (f x) L := by
      intro n
      obtain ⟨x, hx, hd, he⟩ := hbad (1 / (n + 1 : ℝ)) (by positivity)
      exact ⟨x, hx, hd, he⟩

    choose u hs hd he using hex

    have hu : Tendsto u atTop (𝓝 a) := by
      apply Metric.tendsto_atTop.mpr
      intro r hr
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
        MathematicalAnalysis.Chapter02.reciprocal_tendsto_zero r hr
      refine ⟨N, fun n hn => (hd n).trans ?_⟩

      have ht := hN n hn
      simpa only [Real.dist_eq, sub_zero, abs_of_pos (by positivity :
        0 < 1 / (n + 1 : ℝ))] using ht

    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (h u hs hu) ε hε

    exact (not_lt_of_ge (he N)) (hN N le_rfl)

/-- Theorem: a punctured limit is equivalent to convergence along every
convergent sequence that avoids the limiting point. -/
theorem punctured_limit_iff_sequences (f : X → Y) (a : X) (L : Y) :
    Tendsto f (𝓝[≠] a) (𝓝 L) ↔
      ∀ u : ℕ → X, (∀ n, u n ≠ a) → Tendsto u atTop (𝓝 a) →
        Tendsto (f ∘ u) atTop (𝓝 L) := by
  simpa only [mem_compl_iff, mem_singleton_iff] using
    tendsto_within_iff_sequences f ({a}ᶜ) a L

/-- Definition: continuity within a subset uses the epsilon-delta condition
only for points of that subset. -/
theorem continuousWithinAt_iff (f : X → Y) (s : Set X) (a : X) :
    ContinuousWithinAt f s a ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x ∈ s, dist x a < δ → dist (f x) (f a) < ε :=
  Metric.continuousWithinAt_iff

/-- Lemma: continuity within a subset can also be expressed using images of
balls intersected with that subset. -/
theorem continuousWithinAt_iff_image (f : X → Y) (s : Set X) (a : X) :
    ContinuousWithinAt f s a ↔ ∀ ε > 0, ∃ δ > 0,
      f '' (ball a δ ∩ s) ⊆ ball (f a) ε := by
  rw [Metric.continuousWithinAt_iff]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hd⟩ := h ε hε
    refine ⟨δ, hδ, ?_⟩
    rintro y ⟨x, ⟨hx, hs⟩, rfl⟩
    exact hd hs hx

  · intro h ε hε
    obtain ⟨δ, hδ, hd⟩ := h ε hε
    exact ⟨δ, hδ, fun x hx hxa => hd ⟨x, ⟨hxa, hx⟩, rfl⟩⟩

/-- Definition: continuity on a subset means continuity within it at every point. -/
theorem continuousOn_iff (f : X → Y) (s : Set X) :
    ContinuousOn f s ↔ ∀ a ∈ s, ContinuousWithinAt f s a := Iff.rfl

/-- Lemma: pointwise continuity is equivalent to preserving convergent sequences. -/
theorem continuousAt_iff_sequences (f : X → Y) (a : X) :
    ContinuousAt f a ↔ ∀ u : ℕ → X, Tendsto u atTop (𝓝 a) →
      Tendsto (f ∘ u) atTop (𝓝 (f a)) := by
  simpa only [ContinuousAt, nhdsWithin_univ, mem_univ, forall_const] using
    tendsto_within_iff_sequences f univ a (f a)

end MathematicalAnalysis.Chapter03
