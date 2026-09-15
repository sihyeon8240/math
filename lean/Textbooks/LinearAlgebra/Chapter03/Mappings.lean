import Mathlib.Logic.Function.Basic

namespace LinearAlgebra.Chapter03

/-- Definition: a mapping assigns an element of the target to each element of the source. -/
abbrev Mapping (S T : Type*) := S → T

/-- Definition: a two-sided inverse reverses a mapping in both directions. -/
def HasInverse {S T : Type*} (f : S → T) : Prop :=
  ∃ g : T → S, Function.LeftInverse g f ∧ Function.RightInverse g f

/-- Proposition: composition of mappings is associative. -/
theorem composition_assoc {R S T U : Type*} (f : R → S) (g : S → T) (h : T → U) :
    h ∘ (g ∘ f) = (h ∘ g) ∘ f := rfl

/-- Theorem: a mapping has an inverse exactly when it is bijective. -/
theorem hasInverse_iff_bijective {S T : Type*} (f : S → T) :
    HasInverse f ↔ Function.Bijective f := by
  constructor
  · rintro ⟨g, hgf, hfg⟩
    constructor
    · intro x y h
      calc
        x = g (f x) := (hgf x).symm
        _ = g (f y) := congrArg g h
        _ = y := hgf y
    · intro y
      exact ⟨g y, hfg y⟩
  · intro h
    let g : T → S := fun y => Classical.choose (h.2 y)
    have hg : ∀ y, f (g y) = y := fun y => Classical.choose_spec (h.2 y)
    exact ⟨g, fun x => h.1 (hg (f x)), hg⟩

end LinearAlgebra.Chapter03
