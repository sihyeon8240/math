import Textbooks.ElementaryNumberTheory.Chapter03.Congruences
import Mathlib.Data.ZMod.Basic

namespace ElementaryNumberTheory.Chapter03

/-- Definition: a complete residue system represents every congruence class exactly once. -/
def IsCompleteResidueSystem (n : ℕ) (a : Fin n → ℤ) : Prop :=
  ∀ x : ℤ, ∃! i : Fin n, x ≡ a i [ZMOD (n : ℤ)]

/-- Theorem: n pairwise incongruent integers form a complete residue system. -/
theorem complete_residue_system_iff (n : ℕ) (hn : 0 < n) (a : Fin n → ℤ) :
    IsCompleteResidueSystem n a ↔ ∀ i j : Fin n, a i ≡ a j [ZMOD (n : ℤ)] → i = j := by
  let : NeZero n := ⟨ne_of_gt hn⟩

  constructor

  · intro h i j hij

    obtain ⟨k, hk, hu⟩ := h (a i)

    exact (hu i (modEq_refl _ _)).trans (hu j hij).symm

  · intro h

    have hinj : Function.Injective (fun i : Fin n => (a i : ZMod n)) := by
      intro i j heq
      exact h i j ((ZMod.intCast_eq_intCast_iff _ _ n).1 heq)

    have hsurj := (Finite.injective_iff_surjective_of_equiv (ZMod.finEquiv n).toEquiv).1 hinj

    intro x

    obtain ⟨i, hi⟩ := hsurj (x : ZMod n)

    refine ⟨i, (ZMod.intCast_eq_intCast_iff _ _ n).1 hi.symm, ?_⟩

    intro j hj
    apply hinj
    exact ((ZMod.intCast_eq_intCast_iff _ _ n).2 hj).symm.trans hi.symm

end ElementaryNumberTheory.Chapter03
