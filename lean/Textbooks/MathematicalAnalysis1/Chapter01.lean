import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Find

/-! Formalization of results from Chapter 1 of *Mathematical Analysis I*. -/

namespace Textbooks.MathematicalAnalysis1

set_option autoImplicit false

/-- The textbook's natural numbers, whose first element is one rather than zero. -/
abbrev Natural := {n : ℕ // 0 < n}

namespace Chapter01

/-- Every nonempty set of textbook natural numbers has a least element. -/
theorem wellOrderingProperty (S : Set Natural) (hS : S.Nonempty) :
    ∃ m ∈ S, ∀ n ∈ S, m ≤ n := by
  classical
  rcases hS with ⟨n, hn⟩
  let h : ∃ k : ℕ, ∃ m ∈ S, m.val = k := ⟨n.val, n, hn, rfl⟩
  obtain ⟨m, hm, hmk⟩ := Nat.find_spec h
  refine ⟨m, hm, ?_⟩
  intro k hk
  change m.val ≤ k.val
  rw [hmk]
  exact Nat.find_min' h ⟨k, hk, rfl⟩

end Chapter01

end Textbooks.MathematicalAnalysis1
