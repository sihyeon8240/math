import Textbooks.ElementaryNumberTheory.Chapter04.Wilson
import Textbooks.ElementaryNumberTheory.Chapter02.SieveOfEratosthenes

namespace ElementaryNumberTheory.Chapter04

/-- Lemma: factorials dominate twice their argument from three onward. -/
private theorem double_le_factorial (n : ℕ) (hn : 3 ≤ n) : 2 * n ≤ n.factorial := by
  induction n with
  | zero => omega

  | succ n ih =>
    by_cases h : 3 ≤ n

    · have hh := ih h
      rw [Nat.factorial_succ]
      nlinarith

    · have he : n = 2 := by
        omega
      subst n
      decide

/-- Theorem: composite integers of the form n!+1 exceed every bound. -/
theorem exists_composite_factorial_add_one_gt (B : ℕ) :
    ∃ n : ℕ, B < n.factorial + 1 ∧ Chapter02.isComposite (n.factorial + 1) := by
  obtain ⟨p, hp, hlarge⟩ := Chapter02.exists_prime_gt (B + 5)

  have hp3 : 3 ≤ p - 1 := by
    omega

  have hfac := double_le_factorial (p - 1) hp3

  have hpbound : p < (p - 1).factorial + 1 := by
    omega

  have hd : p ∣ (p - 1).factorial + 1 := by
    apply Int.natCast_dvd_natCast.mp

    have h := (Chapter03.modEq_iff_dvd_sub _ _ _).1 (wilson p hp)
    simpa only [Nat.cast_add, Nat.cast_one, sub_neg_eq_add] using h

  refine ⟨p - 1, by omega, ⟨by omega, ?_⟩⟩
  intro hprime
  rcases hprime.2 p hd with h | h

  · have := hp.1
    omega

  · omega

/-- Corollary: infinitely many composite integers have the form n!+1. -/
theorem infinite_factorial_composites :
    {k : ℕ | (∃ n : ℕ, k = n.factorial + 1) ∧ Chapter02.isComposite k}.Infinite := by

  apply Set.infinite_of_forall_exists_gt
  intro B

  obtain ⟨n, hB, hn⟩ := exists_composite_factorial_add_one_gt B

  exact ⟨n.factorial + 1, ⟨⟨n, rfl⟩, hn⟩, hB⟩

end ElementaryNumberTheory.Chapter04
