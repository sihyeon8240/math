import Textbooks.ElementaryNumberTheory.Chapter01.GreatestCommonDivisor
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace ElementaryNumberTheory.Chapter02

/-- Definition: a prime is a natural number greater than one with no divisors
other than one and itself. Natural numbers represent the positive integers here. -/
def isPrime (p : ℕ) : Prop :=
  1 < p ∧ ∀ d : ℕ, d ∣ p → d = 1 ∨ d = p

/-- Definition: a composite number is greater than one and is not prime. -/
def isComposite (n : ℕ) : Prop :=
  1 < n ∧ ¬isPrime n

/-- Lemma: the divisor definition agrees with the standard prime predicate.
This bridge only compares definitions; it supplies no factorization theorem. -/
theorem isPrime_iff_nat_prime (p : ℕ) : isPrime p ↔ Nat.Prime p := by
  rw [Nat.prime_def]
  rfl

/-- Theorem: a prime dividing a product of integers divides one factor. -/
theorem prime_dvd_mul (p : ℕ) (hp : isPrime p) (a b : ℤ)
    (h : (p : ℤ) ∣ a * b) : (p : ℤ) ∣ a ∨ (p : ℤ) ∣ b := by
  classical
  by_cases hpa : (p : ℤ) ∣ a

  · exact Or.inl hpa

  · have hnz : (p : ℤ) ≠ 0 := by
      have := hp.1
      omega

    obtain ⟨_, hdp, hda, _, _⟩ := Chapter01.gcd_spec (p : ℤ) a (Or.inl hnz)
    have hd : Chapter01.gcd (p : ℤ) a ∣ p := Int.natCast_dvd_natCast.mp hdp
    have hcoprime : Chapter01.gcd (p : ℤ) a = 1 := by
      rcases hp.2 _ hd with hone | heq

      · exact hone
      · rw [heq] at hda
        exact (hpa hda).elim

    exact Or.inr (Chapter01.dvd_of_dvd_mul_of_coprime (p : ℤ) a b hcoprime h)

/-- Corollary: a prime dividing a finite product of integers divides a member.
For the empty product, the hypothesis is impossible. -/
theorem prime_dvd_list_prod (p : ℕ) (hp : isPrime p) (l : List ℤ)
    (h : (p : ℤ) ∣ l.prod) : ∃ a ∈ l, (p : ℤ) ∣ a := by
  induction l with
  | nil =>
    obtain ⟨k, hk⟩ := h
    have hpos : (1 : ℤ) < p := by exact_mod_cast hp.1
    change 1 = (p : ℤ) * k at hk
    have hkpos : 0 < k := by nlinarith
    nlinarith

  | cons a l ih =>
    rcases prime_dvd_mul p hp a l.prod h with ha | hl

    · exact ⟨a, List.mem_cons_self, ha⟩
    · obtain ⟨b, hb, hpb⟩ := ih hl
      exact ⟨b, List.mem_cons_of_mem a hb, hpb⟩

/-- Lemma: the integer product result specializes to natural numbers. -/
theorem prime_dvd_mul_nat (p a b : ℕ) (hp : isPrime p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  have h' : (p : ℤ) ∣ (a : ℤ) * (b : ℤ) := by exact_mod_cast h
  rcases prime_dvd_mul p hp a b h' with ha | hb

  · exact Or.inl (Int.natCast_dvd_natCast.mp ha)
  · exact Or.inr (Int.natCast_dvd_natCast.mp hb)

/-- Corollary: a prime dividing a product of primes equals one of those primes. -/
theorem prime_eq_of_dvd_prod (p : ℕ) (hp : isPrime p) (l : List ℕ)
    (hl : ∀ q ∈ l, isPrime q) (h : p ∣ l.prod) : p ∈ l := by
  induction l with
  | nil =>
    obtain ⟨k, hk⟩ := h
    change 1 = p * k at hk
    have hkpos : 0 < k := by nlinarith [hp.1]
    nlinarith [hp.1]

  | cons q l ih =>
    rcases prime_dvd_mul_nat p q l.prod hp h with hq | ht

    · rcases (hl q List.mem_cons_self).2 p hq with hone | heq

      · have := hp.1
        omega
      · exact List.mem_cons.mpr (Or.inl heq)

    · exact List.mem_cons.mpr
        (Or.inr (ih (fun r hr => hl r (List.mem_cons_of_mem q hr)) ht))

end ElementaryNumberTheory.Chapter02
