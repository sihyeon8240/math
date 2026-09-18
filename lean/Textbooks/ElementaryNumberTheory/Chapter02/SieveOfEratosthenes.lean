import Textbooks.ElementaryNumberTheory.Chapter02.PrimeFactorization
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

namespace ElementaryNumberTheory.Chapter02

/-- Lemma: an integer greater than one has a prime divisor no larger than itself. -/
theorem exists_prime_divisor (n : ℕ) (hn : 1 < n) :
    ∃ p : ℕ, isPrime p ∧ p ∣ n ∧ p ≤ n := by
  obtain ⟨l, hne, hl, hprod, _⟩ := fundamental_theorem_of_arithmetic n hn
  cases l with
  | nil => exact (hne rfl).elim
  | cons p l =>
    have hp := hl p List.mem_cons_self
    have heq : n = p * l.prod := hprod.symm
    have hpos : 0 < l.prod := by
      nlinarith
    exact ⟨p, hp, ⟨l.prod, heq⟩, by nlinarith⟩

/-- Theorem: a composite integer has a prime divisor at most its square root.
The natural square root is the floor of the real square root. -/
theorem exists_prime_divisor_le_sqrt (n : ℕ) (hn : isComposite n) :
    ∃ p : ℕ, isPrime p ∧ p ∣ n ∧ p ≤ Nat.sqrt n := by
  classical
  have hdiv : ∃ d : ℕ, d ∣ n ∧ d ≠ 1 ∧ d ≠ n := by
    simpa only [isPrime, hn.1, true_and, not_forall, not_or, exists_prop] using hn.2

  obtain ⟨d, ⟨k, hk⟩, hd1, hdn⟩ := hdiv
  have hdpos : 0 < d := by
    nlinarith [hn.1]
  have hd : 1 < d := by
    omega
  have hkgt : 1 < k := by
    by_contra h
    have hk1 : k = 1 := by
      nlinarith [hn.1]
    simp only [hk1, mul_one] at hk
    exact hdn hk.symm

  obtain ⟨p, hp, ⟨t, ht⟩, hle⟩ := exists_prime_divisor (min d k) (by omega)
  refine ⟨p, hp, ?_, Nat.le_sqrt.mpr ?_⟩

  · rcases le_total d k with hdk | hkd

    · rw [min_eq_left hdk] at ht
      refine ⟨t * k, ?_⟩
      rw [hk, ht]
      ring
    · rw [min_eq_right hkd] at ht
      refine ⟨d * t, ?_⟩
      rw [hk, ht]
      ring

  · have hpd : p ≤ d := le_trans hle (min_le_left _ _)
    have hpk : p ≤ k := le_trans hle (min_le_right _ _)
    nlinarith [Nat.mul_le_mul hpd hpk]

/-- Lemma: each positive integer at most n occurs as a factor of n factorial. -/
theorem factorial_multiple (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    ∃ t : ℕ, n.factorial = k * t := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases heq : k = n + 1

    · exact ⟨n.factorial, by rw [heq, Nat.factorial_succ]⟩
    · obtain ⟨t, ht⟩ := ih (by omega)
      refine ⟨(n + 1) * t, ?_⟩
      rw [Nat.factorial_succ, ht]
      ring

/-- Lemma: a prime divisor of M + 1 cannot also divide M. -/
theorem not_dvd_of_dvd_add_one (p M : ℕ) (hp : isPrime p) (h : p ∣ M + 1) :
    ¬p ∣ M := by
  rintro ⟨j, hj⟩
  obtain ⟨k, hk⟩ := h
  have hjk : j + 1 ≤ k := by
    nlinarith [hp.1]
  nlinarith [Nat.mul_le_mul_left p hjk, hp.1]

/-- Lemma: there is a prime above any prescribed natural bound. -/
theorem exists_prime_gt (m : ℕ) : ∃ p : ℕ, isPrime p ∧ m < p := by
  obtain ⟨p, hp, hdiv, _⟩ :=
    exists_prime_divisor (m.factorial + 1) (by
      have := Nat.factorial_pos m
      omega)
  refine ⟨p, hp, ?_⟩
  by_contra h
  obtain ⟨t, ht⟩ := factorial_multiple m p (lt_trans Nat.zero_lt_one hp.1) (by omega)
  exact not_dvd_of_dvd_add_one p m.factorial hp hdiv ⟨t, ht⟩

/-- Theorem: the set of primes is infinite, by Euclid's factorial-plus-one argument. -/
theorem infinite_primes : Set.Infinite {p : ℕ | isPrime p} := by
  apply Set.infinite_of_forall_exists_gt
  intro m
  obtain ⟨p, hp, hgt⟩ := exists_prime_gt m
  exact ⟨p, hp, hgt⟩

/-- Lemma: the next prime is no larger than one plus the product of its predecessors.
The generic enumeration `Nat.nth` starts at index zero. -/
theorem nth_prime_le_prod_add_one (n : ℕ) :
    Nat.nth isPrime n ≤ (∏ i ∈ Finset.range n, Nat.nth isPrime i) + 1 := by
  classical
  let P := ∏ i ∈ Finset.range n, Nat.nth isPrime i
  have hP : 0 < P := by
    apply Finset.prod_pos
    intro i _
    exact lt_trans Nat.zero_lt_one (Nat.nth_mem_of_infinite infinite_primes i).1

  obtain ⟨q, hq, hdiv, hqle⟩ := exists_prime_divisor (P + 1) (by omega)
  obtain ⟨k, hk⟩ := Nat.subset_range_nth (p := isPrime) (show q ∈ Set.ofPred isPrime from hq)
  have hnk : n ≤ k := by
    by_contra h
    have hmem : k ∈ Finset.range n := Finset.mem_range.mpr (by omega)
    have hfactor := Finset.prod_erase_mul (Finset.range n) (Nat.nth isPrime) hmem
    have hqP : q ∣ P := by
      refine ⟨∏ i ∈ (Finset.range n).erase k, Nat.nth isPrime i, ?_⟩
      dsimp [P]
      rw [← hfactor, hk, mul_comm]

    exact not_dvd_of_dvd_add_one q P hq hdiv hqP

  calc
    Nat.nth isPrime n ≤ Nat.nth isPrime k := Nat.nth_monotone infinite_primes hnk
    _ = q := hk
    _ ≤ P + 1 := hqle

/-- Lemma: the product of the first n primes is less than the double exponential. -/
theorem prod_initial_primes_lt (n : ℕ) :
    (∏ i ∈ Finset.range n, Nat.nth isPrime i) < 2 ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hnext := nth_prime_le_prod_add_one n
    have hbound : Nat.nth isPrime n ≤ 2 ^ (2 ^ n) := by
      omega
    rw [Finset.prod_range_succ]
    calc
      (∏ i ∈ Finset.range n, Nat.nth isPrime i) * Nat.nth isPrime n ≤
          (∏ i ∈ Finset.range n, Nat.nth isPrime i) * 2 ^ (2 ^ n) :=
        Nat.mul_le_mul_left _ hbound
      _ < 2 ^ (2 ^ n) * 2 ^ (2 ^ n) :=
        Nat.mul_lt_mul_of_pos_right ih (pow_pos (by omega) _)
      _ = 2 ^ (2 ^ (n + 1)) := by
        rw [pow_succ (2 : ℕ) n, pow_mul, pow_two]

/-- Theorem: the nth prime, with one-based mathematical indexing, is at most
2 raised to 2 raised to n - 1. -/
theorem nth_prime_le_double_exponential (n : ℕ) (hn : 0 < n) :
    Nat.nth isPrime (n - 1) ≤ 2 ^ (2 ^ (n - 1)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hproduct := prod_initial_primes_lt m
  have hnext := nth_prime_le_prod_add_one m
  simpa only [Nat.succ_sub_one] using
    (show Nat.nth isPrime m ≤ 2 ^ (2 ^ m) by omega)

end ElementaryNumberTheory.Chapter02
