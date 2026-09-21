import Textbooks.ElementaryNumberTheory.Chapter02.SieveOfEratosthenes
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace ElementaryNumberTheory.Chapter02

/-- Theorem: arbitrarily long blocks of consecutive composite integers exist. -/
theorem exists_consecutive_composites (n : ℕ) (_hn : 0 < n) :
    ∃ M : ℕ, ∀ i : ℕ, i < n → isComposite (M + i) := by
  let F := (n + 1).factorial
  refine ⟨F + 2, ?_⟩
  intro i hi
  obtain ⟨t, ht⟩ := factorial_multiple (n + 1) (i + 2) (by omega) (by omega)
  have hF : 0 < F := Nat.factorial_pos (n + 1)
  have hdiv : i + 2 ∣ F + 2 + i := by
    refine ⟨t + 1, ?_⟩
    dsimp [F]
    rw [ht]
    ring

  refine ⟨by omega, ?_⟩
  intro hp
  rcases hp.2 (i + 2) hdiv with hone | heq

  · omega
  · omega

/-- Lemma: a finite product of integers of the form 4k + 1 has the same form.
This includes the empty product and hence the stated case of at least two factors. -/
theorem prod_four_mul_add_one (l : List ℤ)
    (hl : ∀ a ∈ l, ∃ k : ℤ, a = 4 * k + 1) :
    ∃ k : ℤ, l.prod = 4 * k + 1 := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons a l ih =>
    obtain ⟨u, hu⟩ := hl a List.mem_cons_self
    obtain ⟨v, hv⟩ := ih (fun b hb => hl b (List.mem_cons_of_mem a hb))
    refine ⟨4 * u * v + u + v, ?_⟩
    rw [List.prod_cons, hu, hv]
    ring

/-- Lemma: a prime is either two or has remainder one or three upon division by four. -/
theorem prime_eq_two_or_mod_four (p : ℕ) (hp : isPrime p) :
    p = 2 ∨ p % 4 = 1 ∨ p % 4 = 3 := by
  have hmod : p % 4 < 4 := Nat.mod_lt p (by omega)
  by_cases hone : p % 4 = 1

  · exact Or.inr (Or.inl hone)

  · by_cases hthree : p % 4 = 3

    · exact Or.inr (Or.inr hthree)

    · have hdiv : 2 ∣ p := by
        rcases (show p % 4 = 0 ∨ p % 4 = 2 by omega) with hzero | htwo

        · exact ⟨2 * (p / 4), by omega⟩
        · exact ⟨2 * (p / 4) + 1, by omega⟩

      rcases hp.2 2 hdiv with h | h

      · omega
      · exact Or.inl h.symm

/-- Lemma: an integer with remainder three modulo four has a prime divisor
with the same remainder. -/
theorem exists_prime_divisor_mod_four_three (n : ℕ) (hn : n % 4 = 3) :
    ∃ p : ℕ, isPrime p ∧ p ∣ n ∧ p % 4 = 3 := by
  classical
  obtain ⟨l, hl, hprod⟩ := exists_prime_factors n (by omega)
  by_contra h
  push Not at h
  have hone : ∀ p ∈ l, p % 4 = 1 := by
    intro p hp
    have hdiv : p ∣ n := ⟨(l.erase p).prod, by rw [← hprod, List.prod_erase hp]⟩
    rcases prime_eq_two_or_mod_four p (hl p hp) with htwo | hrest

    · obtain ⟨k, hk⟩ := hdiv
      rw [htwo] at hk
      omega

    · exact hrest.resolve_right (h p (hl p hp) hdiv)

  have hform : ∀ a ∈ l.map (fun p : ℕ => (p : ℤ)), ∃ k : ℤ, a = 4 * k + 1 := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    refine ⟨(p / 4 : ℕ), ?_⟩
    have heq : p = 4 * (p / 4) + 1 := by
      have := hone p hp
      omega
    exact_mod_cast heq

  obtain ⟨k, hk⟩ := prod_four_mul_add_one _ hform
  have hcast : (l.map (fun p : ℕ => (p : ℤ))).prod = (n : ℤ) := by
    rw [← Nat.cast_list_prod, hprod]

  rw [hcast] at hk
  omega

/-- Lemma: primes of the form 4k + 3 exceed every prescribed bound. -/
theorem exists_prime_mod_four_three_gt (m : ℕ) :
    ∃ p : ℕ, isPrime p ∧ m < p ∧ ∃ k : ℕ, p = 4 * k + 3 := by
  let N := 4 * m.factorial - 1
  have hfac := Nat.factorial_pos m
  have hN : N % 4 = 3 := by
    dsimp [N]
    omega
  obtain ⟨p, hp, hdiv, hmod⟩ := exists_prime_divisor_mod_four_three N hN
  refine ⟨p, hp, ?_, p / 4, by omega⟩
  by_contra h
  obtain ⟨t, ht⟩ := factorial_multiple m p (lt_trans Nat.zero_lt_one hp.1) (by omega)
  have hsucc : p ∣ N + 1 := by
    refine ⟨4 * t, ?_⟩
    have hNsucc : N + 1 = 4 * m.factorial := by
      dsimp [N]
      omega

    rw [hNsucc, ht]
    ring

  exact not_dvd_of_dvd_add_one p N hp hsucc hdiv

/-- Theorem: infinitely many primes are of the form 4k + 3. -/
theorem infinite_primes_four_mul_add_three :
    Set.Infinite {p : ℕ | isPrime p ∧ ∃ k : ℕ, p = 4 * k + 3} := by
  apply Set.infinite_of_forall_exists_gt
  intro m
  obtain ⟨p, hp, hgt, hform⟩ := exists_prime_mod_four_three_gt m
  exact ⟨p, ⟨hp, hform⟩, hgt⟩

/-- Theorem: if n > 2 terms of a natural-number arithmetic progression are prime,
every prime less than n divides the common difference, including difference zero. -/
theorem prime_dvd_common_difference (p d n : ℕ) (hn : 2 < n)
    (hterms : ∀ i : ℕ, i < n → isPrime (p + i * d)) :
    ∀ q : ℕ, isPrime q → q < n → q ∣ d := by
  have hp : isPrime p := by
    simpa only [zero_mul, add_zero] using hterms 0 (by omega)

  intro q hq hqn
  by_cases hd : d = 0

  · exact ⟨0, by rw [hd, mul_zero]⟩

  · have hnp : n ≤ p := by
      by_contra h
      have hterm := hterms p (by omega)
      have hdiv : p ∣ p + p * d := ⟨1 + d, by ring⟩
      rcases hterm.2 p hdiv with hone | heq

      · have := hp.1
        omega
      · have hdpos : 0 < d := by omega
        nlinarith [hp.1]

    by_contra hqd
    have hqpos : 0 < q := lt_trans Nat.zero_lt_one hq.1
    have hqne : (q : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hqpos)
    obtain ⟨_, hgq, hgd, _, _⟩ :=
      Chapter01.gcd_spec (q : ℤ) (d : ℤ) (Or.inl hqne)
    have hg : Chapter01.gcd (q : ℤ) (d : ℤ) = 1 := by
      rcases hq.2 _ (Int.natCast_dvd_natCast.mp hgq) with hone | heq

      · exact hone
      · rw [heq] at hgd
        exact (hqd (Int.natCast_dvd_natCast.mp hgd)).elim

    obtain ⟨r, s, hrs⟩ :=
      (Chapter01.gcd_eq_one_iff_exists_mul_add_mul (q : ℤ) (d : ℤ) (Or.inl hqne)).mp hg
    obtain ⟨⟨a, i⟩, ⟨hrem, hi⟩, _⟩ :=
      Chapter01.existsUnique_quotient_remainder (-(p : ℤ) * s) ⟨q, hqpos⟩
    change -(p : ℤ) * s = a * (q : ℤ) + (i : ℤ) at hrem
    change i < q at hi

    have hdiv : q ∣ p + i * d := by
      apply Int.natCast_dvd_natCast.mp
      refine ⟨(p : ℤ) * r - (d : ℤ) * a, ?_⟩
      push_cast
      nlinarith [congrArg (fun z => (p : ℤ) * z) hrs,
        congrArg (fun z => (d : ℤ) * z) hrem]

    have hterm := hterms i (lt_trans hi hqn)
    rcases hterm.2 q hdiv with hone | heq

    · have := hq.1
      omega
    · omega

end ElementaryNumberTheory.Chapter02
