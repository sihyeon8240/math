import Textbooks.ElementaryNumberTheory.Chapter05.DivisorFormulas

namespace ElementaryNumberTheory.Chapter05

/-- Definition: the prime-power contribution to the Möbius function. -/
def mobiusWeight (k : ℕ) : ℤ := if k = 0 then 1 else if k = 1 then -1 else 0

/-- Definition: Möbius values are products of their prime-power contributions. Zero is assigned
zero; all lecture identities concern positive arguments. -/
noncomputable def mobius (n : ℕ) : ℤ :=
  if n = 0 then 0 else (primeExponents n).prod (fun _ k => mobiusWeight k)

/-- Lemma: membership in the prime support implies divisibility. -/
theorem prime_dvd_of_mem_support (n p : ℕ) (hn : 0 < n)
    (hp : p ∈ (primeExponents n).support) : p ∣ n := by
  have hprime := (primeExponents_spec n hn).1 p hp
  apply (dvd_iff_primeExponents_le p n (by
      have := hprime.1
      omega) hn).2

  have he : primeExponents p = Finsupp.single p 1 := by
    simpa only [pow_one] using primeExponents_prime_pow p 1 hprime
  rw [he, Finsupp.single_le_iff]
  exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)

/-- Lemma: relatively prime integers have disjoint prime supports. -/
theorem prime_support_disjoint (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hcop : Chapter01.gcd m n = 1) :
    Disjoint (primeExponents m).support (primeExponents n).support := by

  apply Finset.disjoint_left.mpr
  intro p hpm hpn

  have hp := (primeExponents_spec m hm).1 p hpm

  have hdiv := (Chapter01.gcd_spec m n (Or.inl (by omega))).2.2.2.2 p
    (Int.natCast_dvd_natCast.mpr (prime_dvd_of_mem_support m p hm hpm))
    (Int.natCast_dvd_natCast.mpr (prime_dvd_of_mem_support n p hn hpn))
  rw [hcop, Nat.cast_one] at hdiv

  obtain ⟨k, hk⟩ := hdiv

  have hp' : (1 : ℤ) < p := by
    exact_mod_cast hp.1

  have hkpos : 0 < k := by
    nlinarith
  nlinarith

/-- Theorem: the Möbius function is multiplicative. -/
theorem mobius_multiplicative : IsMultiplicative mobius := by
  intro m n hm hn hcop
  rw [mobius, mobius, mobius, ite_eq_right (ne_of_gt (mul_pos hm hn)),
    ite_eq_right (ne_of_gt hm), ite_eq_right (ne_of_gt hn), primeExponents_mul m n hm hn]

  exact Finsupp.prod_add_index_of_disjoint (prime_support_disjoint m n hm hn hcop) _

/-- Theorem: the value of Möbius at one is one. -/
theorem mobius_one : mobius 1 = 1 := by
  simp only [mobius, one_ne_zero, ↓reduceIte, primeExponents_one, Finsupp.prod_zero_index]

/-- Theorem: the prime-power values are one, minus one, and then zero. -/
theorem mobius_prime_pow (p k : ℕ) (hp : Chapter02.isPrime p) :
    mobius (p ^ k) = mobiusWeight k := by
  have hpos : 0 < p ^ k := pow_pos (by
      have := hp.1
      omega) k
  rw [mobius, ite_eq_right (ne_of_gt hpos), primeExponents_prime_pow p k hp]
  exact Finsupp.prod_single_index (by simp only [mobiusWeight, ↓reduceIte])

/-- Theorem: Möbius is zero when a prime square divides its argument. -/
theorem mobius_eq_zero_of_prime_sq_dvd (n p : ℕ) (hn : 0 < n)
    (hp : Chapter02.isPrime p) (hdiv : p ^ 2 ∣ n) : mobius n = 0 := by
  have hle := (dvd_iff_primeExponents_le (p ^ 2) n
    (pow_pos (by
        have := hp.1
        omega) 2) hn).1 hdiv
  rw [primeExponents_prime_pow p 2 hp, Finsupp.single_le_iff] at hle
  rw [mobius, ite_eq_right (ne_of_gt hn), Finsupp.prod]

  have hmem : p ∈ (primeExponents n).support :=
    Finsupp.mem_support_iff.mpr (by omega)

  apply Finset.prod_eq_zero hmem
  simp only [mobiusWeight, ite_eq_right (by omega : primeExponents n p ≠ 0),
    ite_eq_right (by omega : primeExponents n p ≠ 1)]

/-- Theorem: without prime-square divisors, Möbius is the parity sign of the number of distinct
prime factors, including the empty product at one. -/
theorem mobius_eq_sign (n : ℕ) (hn : 0 < n)
    (hsq : ∀ p : ℕ, Chapter02.isPrime p → ¬p ^ 2 ∣ n) :
    mobius n = (-1 : ℤ) ^ (primeExponents n).support.card := by
  rw [mobius, ite_eq_right (ne_of_gt hn), Finsupp.prod]

  have hweight : ∀ p ∈ (primeExponents n).support, mobiusWeight (primeExponents n p) = -1 := by
    intro p hps

    have hp := (primeExponents_spec n hn).1 p hps

    have hpos := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hps)

    have hlt : primeExponents n p < 2 := by
      by_contra hh
      apply hsq p hp
      apply (dvd_iff_primeExponents_le _ n (pow_pos (by
          have := hp.1
          omega) 2) hn).2
      rw [primeExponents_prime_pow p 2 hp, Finsupp.single_le_iff]
      omega

    have he : primeExponents n p = 1 := by
      omega
    simp only [he, mobiusWeight, one_ne_zero, ↓reduceIte]
  rw [Finset.prod_congr rfl hweight, Finset.prod_const]

/-- Lemma: summing the prime-power Möbius contributions cancels after the first power. -/
theorem sum_mobiusWeight (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), mobiusWeight j) = if k = 0 then 1 else 0 := by
  induction k with
  | zero => simp only [Nat.zero_add, Finset.sum_range_one, mobiusWeight, ↓reduceIte]

  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hk : k = 0

    · subst k
      norm_num [mobiusWeight]

    · have hne : k + 1 ≠ 1 := by
        omega

      simp only [hk, ↓reduceIte, mobiusWeight, Nat.succ_ne_zero, hne, zero_add]

/-- Lemma: the divisor sum of Möbius vanishes on every positive prime power. -/
theorem divisorSum_mobius_prime_pow (p k : ℕ) (hp : Chapter02.isPrime p) (hk : 0 < k) :
    divisorSum mobius (p ^ k) = 0 := by
  rw [divisorSum, divisors_prime_pow p k hp, Finset.sum_image]

  · simp only [mobius_prime_pow p _ hp]
    rw [sum_mobiusWeight, ite_eq_right (ne_of_gt hk)]

  · intro i hi j hj h
    exact pow_right_injective₀ (by
        have := hp.1
        omega : 0 < p)
      (by
          have := hp.1
          omega : p ≠ 1) h

/-- Theorem: the divisor sum of Möbius is one at one and zero otherwise. -/
theorem sum_mobius (n : ℕ) (hn : 0 < n) :
    divisorSum mobius n = if n = 1 then 1 else 0 := by
  by_cases he : n = 1

  · subst n
    simp only [divisorSum, Nat.divisors_one, Finset.sum_singleton, mobius_one, ↓reduceIte]

  · rw [ite_eq_right he, multiplicative_prime_powers _
      (divisorSum_multiplicative _ mobius_multiplicative) n (by omega)]

    have hs : (primeExponents n).support.Nonempty := by
      by_contra h

      have hh := (primeExponents_spec n hn).2
      change (∏ p ∈ (primeExponents n).support, p ^ primeExponents n p) = n at hh
      rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.prod_empty] at hh
      exact he hh.symm

    obtain ⟨p, hp⟩ := hs
    apply Finset.prod_eq_zero hp
    exact divisorSum_mobius_prime_pow p _ ((primeExponents_spec n hn).1 p hp)
      (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp))

/-- Definition: the summatory Möbius function, indexed by all positive integers up to N, rather
than by the divisors of N. -/
noncomputable def mertens (N : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 N, mobius k

end ElementaryNumberTheory.Chapter05
