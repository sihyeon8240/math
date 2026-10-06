import Textbooks.MathematicalAnalysis.Chapter03.ContinuousFunctions
import Textbooks.MathematicalAnalysis.Chapter01.ConnectedSets

namespace MathematicalAnalysis.Chapter03

open Set Metric
open MathematicalAnalysis.Chapter01

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- Lemma: an open-set preimage under a map continuous on a subset is relatively open. -/
theorem continuousOn_open_preimage (K : Set X) (f : X → Y) (hf : ContinuousOn f K)
    (U : Set Y) (hU : IsOpen U) :
    ∃ V : Set X, IsOpen V ∧ ∀ x ∈ K, (x ∈ V ↔ f x ∈ U) := by
  classical
  let A := {x : X | x ∈ K ∧ f x ∈ U}
  have hex : ∀ a : A, ∃ δ > 0, ∀ x ∈ K, dist x a.val < δ → f x ∈ U := by
    intro a
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU (f a) a.property.2
    obtain ⟨δ, hδ, hd⟩ := Metric.continuousWithinAt_iff.mp
      (hf a a.property.1) ε hε
    exact ⟨δ, hδ, fun x hx hxa => hball (hd hx hxa)⟩
  choose r hr hd using hex
  refine ⟨⋃ a : A, ball a.val (r a), open_union _ (fun a => ball_open _ _), ?_⟩
  intro x hx
  constructor
  · intro h
    obtain ⟨a, ha⟩ := mem_iUnion.mp h
    exact hd a x hx ha
  · intro h
    let a : A := ⟨x, hx, h⟩
    exact mem_iUnion.mpr ⟨a, mem_ball_self (hr a)⟩

/-- Theorem: the continuous image of a connected subset is connected. Here
connectedness includes the empty set. -/
theorem connected_image (K : Set X) (hK : IsPreconnected K) (f : X → Y)
    (hf : ContinuousOn f K) : IsPreconnected (f '' K) := by
  intro U V hU hV hcover hIU hIV
  obtain ⟨P, hP, hPeq⟩ := continuousOn_open_preimage K f hf U hU
  obtain ⟨Q, hQ, hQeq⟩ := continuousOn_open_preimage K f hf V hV
  have hcov : K ⊆ P ∪ Q := by
    intro x hx
    rcases hcover ⟨x, hx, rfl⟩ with h | h
    · exact Or.inl ((hPeq x hx).mpr h)
    · exact Or.inr ((hQeq x hx).mpr h)
  obtain ⟨u, ⟨x, hx, rfl⟩, hu⟩ := hIU
  obtain ⟨v, ⟨y, hy, rfl⟩, hv⟩ := hIV
  obtain ⟨z, hz, hzP, hzQ⟩ := hK P Q hP hQ hcov
    ⟨x, hx, (hPeq x hx).mpr hu⟩ ⟨y, hy, (hQeq y hy).mpr hv⟩
  exact ⟨f z, ⟨z, hz, rfl⟩, (hPeq z hz).mp hzP, (hQeq z hz).mp hzQ⟩

/-- Lemma: every closed real interval is connected, including empty intervals. -/
theorem connected_interval (a b : ℝ) : IsPreconnected (Icc a b) := by
  apply (isPreconnected_iff_between _).mpr
  intro x hx y hy z hxz hzy
  exact ⟨hx.1.trans hxz.le, hzy.le.trans hy.2⟩

/-- Theorem: a continuous real function on a connected set takes every value
strictly between any two of its values. -/
theorem intermediate_value_connected (K : Set X) (hK : IsPreconnected K)
    (f : X → ℝ) (hf : ContinuousOn f K) (a b : X) (ha : a ∈ K) (hb : b ∈ K)
    (c : ℝ) (hac : f a < c) (hcb : c < f b) : ∃ x ∈ K, f x = c := by
  exact (isPreconnected_iff_between (f '' K)).mp (connected_image K hK f hf)
    (f a) ⟨a, ha, rfl⟩ (f b) ⟨b, hb, rfl⟩ c hac hcb

/-- Theorem: a continuous function on a closed real interval takes every value
between its endpoint values, in either order and including the endpoints. -/
theorem intermediate_value_interval (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc a b)) (c : ℝ)
    (hc : min (f a) (f b) ≤ c ∧ c ≤ max (f a) (f b)) :
    ∃ x ∈ Icc a b, f x = c := by
  by_cases ha : c = f a
  · exact ⟨a, ⟨le_rfl, hab⟩, ha.symm⟩
  by_cases hb : c = f b
  · exact ⟨b, ⟨hab, le_rfl⟩, hb.symm⟩

  rcases le_total (f a) (f b) with h | h
  · rw [min_eq_left h, max_eq_right h] at hc
    exact intermediate_value_connected _ (connected_interval a b) f hf a b
      ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ c
      (lt_of_le_of_ne hc.1 (Ne.symm ha)) (lt_of_le_of_ne hc.2 hb)
  · rw [min_eq_right h, max_eq_left h] at hc
    exact intermediate_value_connected _ (connected_interval a b) f hf b a
      ⟨hab, le_rfl⟩ ⟨le_rfl, hab⟩ c
      (lt_of_le_of_ne hc.1 (Ne.symm hb)) (lt_of_le_of_ne hc.2 ha)

end MathematicalAnalysis.Chapter03
