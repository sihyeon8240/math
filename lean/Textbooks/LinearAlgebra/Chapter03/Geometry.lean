import Textbooks.LinearAlgebra.Chapter03.LinearMappings
import Mathlib.Analysis.Convex.Basic

namespace LinearAlgebra.Chapter03

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- Definition: the closed line segment joining two vectors. -/
abbrev lineSegment (v w : V) : Set V := segment ℝ v w

/-- Definition: a convex set contains every convex combination of any two of its points. -/
abbrev IsConvex (S : Set V) : Prop := Convex ℝ S

/-- Proposition: a segment consists of the combinations `(1-t)v+tw` for `0 ≤ t ≤ 1`. -/
theorem mem_lineSegment_iff (v w x : V) :
    x ∈ lineSegment v w ↔ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ (1 - t) • v + t • w = x := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, he⟩
    refine ⟨b, hb, ?_, ?_⟩
    · calc
        b ≤ a + b := le_add_of_nonneg_left ha
        _ = 1 := hab
    · have h : 1 - b = a := (eq_sub_iff_add_eq.mpr hab).symm
      simpa only [h] using he
  · rintro ⟨t, ht, ht1, he⟩
    exact ⟨1 - t, t, sub_nonneg.mpr ht1, ht, sub_add_cancel 1 t, he⟩

/-- Proposition: convexity means containing the segment between any two points. -/
theorem convex_iff_segments (S : Set V) :
    IsConvex S ↔ ∀ v ∈ S, ∀ w ∈ S, lineSegment v w ⊆ S := by
  constructor
  · intro h v hv w hw x hx
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
    exact h hv hw ha hb hab
  · intro h v hv w hw a b ha hb hab
    exact h v hv w hw ⟨a, b, ha, hb, hab, rfl⟩

/-- Proposition: a linear map preserves a segment's scalar parameter. -/
theorem map_segment_point (f : V →ₗ[ℝ] W) (v w : V) (t : ℝ) :
    f ((1 - t) • v + t • w) = (1 - t) • f v + t • f w := by
  rw [f.map_add, f.map_smul, f.map_smul]

/-- Theorem: the image of a segment is the segment between the images of its endpoints. -/
theorem image_lineSegment (f : V →ₗ[ℝ] W) (v w : V) :
    f '' lineSegment v w = lineSegment (f v) (f w) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, ht, ht1, rfl⟩ := (mem_lineSegment_iff v w x).mp hx
    exact (mem_lineSegment_iff _ _ _).mpr ⟨t, ht, ht1, (map_segment_point f v w t).symm⟩
  · intro hy
    obtain ⟨t, ht, ht1, he⟩ := (mem_lineSegment_iff _ _ _).mp hy
    refine ⟨(1 - t) • v + t • w, (mem_lineSegment_iff _ _ _).mpr ⟨t, ht, ht1, rfl⟩, ?_⟩
    exact (map_segment_point f v w t).trans he

/-- Theorem: the image of a convex set under a linear map is convex. -/
theorem image_convex (f : V →ₗ[ℝ] W) {S : Set V} (hS : IsConvex S) : IsConvex (f '' S) := by
  apply (convex_iff_segments _).mpr
  rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩ y hy
  rw [← image_lineSegment] at hy
  obtain ⟨x, hx, he⟩ := hy
  exact ⟨x, (convex_iff_segments S).mp hS v hv w hw hx, he⟩

end LinearAlgebra.Chapter03
