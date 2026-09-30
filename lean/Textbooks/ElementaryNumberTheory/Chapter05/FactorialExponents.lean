import Textbooks.ElementaryNumberTheory.Chapter05.SummatoryFunctions

namespace ElementaryNumberTheory.Chapter05

/-- Lemma: the exponent of a prime is bounded by the positive integer itself. -/
theorem primeExponent_le (n p : ℕ) (hn : 0 < n) (hp : Chapter02.isPrime p) :
    primeExponents n p ≤ n := by
  have hpp : 0 < p := by
    have := hp.1
    omega

  have hd : p ^ primeExponents n p ∣ n := by
    apply (dvd_iff_primeExponents_le _ n (pow_pos hpp _) hn).2
    rw [primeExponents_prime_pow p _ hp, Finsupp.single_le_iff]

  have hpower : ∀ k : ℕ, k ≤ p ^ k := by
    intro k
    induction k with
    | zero => simp only [pow_zero, Nat.zero_le]

    | succ k ih =>
      rw [pow_succ]

      have hpos := pow_pos hpp k

      have := hp.1
      nlinarith

  exact (hpower _).trans (Nat.le_of_dvd hn hd)

/-- Lemma: prime-power divisibility counts the exponent. -/
theorem primeExponent_eq_count (n p N : ℕ) (hn : 0 < n) (hp : Chapter02.isPrime p)
    (hN : n ≤ N) :
    primeExponents n p = ((Finset.Icc 1 N).filter (fun j => p ^ j ∣ n)).card := by
  have hset : (Finset.Icc 1 N).filter (fun j => p ^ j ∣ n) =
      Finset.Icc 1 (primeExponents n p) := by
    ext j

    have hdiv : p ^ j ∣ n ↔ j ≤ primeExponents n p := by
      rw [dvd_iff_primeExponents_le _ n
        (pow_pos (by
            have := hp.1
            omega) j) hn,
        primeExponents_prime_pow p j hp, Finsupp.single_le_iff]

    simp only [Finset.mem_filter, Finset.mem_Icc, hdiv]

    have hle := (primeExponent_le n p hn hp).trans hN
    omega

  rw [hset, Nat.card_Icc, Nat.add_sub_cancel]

/-- Lemma: a factorial exponent is the sum of the exponents of its factors. -/
theorem primeExponent_factorial (n p : ℕ) :
    primeExponents n.factorial p = ∑ k ∈ Finset.Icc 1 n, primeExponents k p := by
  induction n with
  | zero =>
    simp only [Nat.factorial_zero, primeExponents_one, Finsupp.zero_apply,
      Finset.Icc_eq_empty_of_lt (by decide : 0 < 1), Finset.sum_empty]

  | succ n ih =>
    rw [Nat.factorial_succ, primeExponents_mul (n + 1) n.factorial
      (Nat.succ_pos n) (Nat.factorial_pos n), Finsupp.add_apply, ih,
      Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), add_comm]

/-- Theorem: Legendre's formula with any upper bound at least n. -/
theorem legendre_with_bound (n p N : ℕ) (hp : Chapter02.isPrime p) (hN : n ≤ N) :
    primeExponents n.factorial p = ∑ j ∈ Finset.Icc 1 N, n / p ^ j := by
  rw [primeExponent_factorial]

  have hexpand (k : ℕ) (hk : k ∈ Finset.Icc 1 n) :
      primeExponents k p = ∑ j ∈ Finset.Icc 1 N, if p ^ j ∣ k then 1 else 0 := by
    rw [primeExponent_eq_count k p N (Finset.mem_Icc.mp hk).1 hp
      ((Finset.mem_Icc.mp hk).2.trans hN),
      ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]

  rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj

  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one,
    card_multiples n (p ^ j) (pow_pos (by
        have := hp.1
        omega) j)]

/-- Corollary: Legendre's sum can be truncated at n. -/
theorem legendre (n p : ℕ) (hp : Chapter02.isPrime p) :
    primeExponents n.factorial p = ∑ j ∈ Finset.Icc 1 n, n / p ^ j :=
  legendre_with_bound n p n hp le_rfl

/-- Theorem: the factorial quotient defining a binomial coefficient is integral. -/
theorem factorials_dvd_factorial (n r : ℕ) (hr : r ≤ n) :
    r.factorial * (n - r).factorial ∣ n.factorial := by

  apply (dvd_iff_primeExponents_le _ _
    (mul_pos (Nat.factorial_pos r) (Nat.factorial_pos (n - r))) (Nat.factorial_pos n)).2

  intro p
  by_cases he : primeExponents (r.factorial * (n - r).factorial) p = 0

  · rw [he]
    exact Nat.zero_le _

  · have hp := (primeExponents_spec (r.factorial * (n - r).factorial)
      (mul_pos (Nat.factorial_pos r) (Nat.factorial_pos (n - r)))).1 p
      (Finsupp.mem_support_iff.mpr he)

    rw [primeExponents_mul _ _ (Nat.factorial_pos r) (Nat.factorial_pos (n - r)),
      Finsupp.add_apply, legendre_with_bound r p n hp hr,
      legendre_with_bound (n - r) p n hp (Nat.sub_le n r), legendre n p hp,
      ← Finset.sum_add_distrib]

    apply Finset.sum_le_sum
    intro j hj

    have hpos : 0 < p ^ j := pow_pos (by
        have := hp.1
        omega) j

    apply (Nat.le_div_iff_mul_le hpos).2

    have h₁ := Nat.div_mul_le_self r (p ^ j)

    have h₂ := Nat.div_mul_le_self (n - r) (p ^ j)

    have hsum : r + (n - r) = n := Nat.add_sub_cancel' hr

    nlinarith

/-- Corollary: the product of r consecutive positive integers is divisible by r!. -/
theorem factorial_dvd_consecutive_product (a r : ℕ) :
    r.factorial ∣ ∏ k ∈ Finset.Ico (a + 1) (a + r + 1), k := by
  have hfactor : (∏ k ∈ Finset.Ico (a + 1) (a + r + 1), k) * a.factorial =
      (a + r).factorial := by
    induction r with
    | zero => simp only [Nat.add_zero, Finset.Ico_self, Finset.prod_empty, one_mul]

    | succ r ih =>
      rw [show a + (r + 1) + 1 = (a + r + 1) + 1 by omega,
        Finset.prod_Ico_succ_top (by omega : a + 1 ≤ a + r + 1)]
      rw [mul_right_comm, ih]
      rw [show a + (r + 1) = (a + r) + 1 by omega, Nat.factorial_succ]
      ring

  obtain ⟨k, hk⟩ := factorials_dvd_factorial (a + r) r (by omega)
  rw [show a + r - r = a by omega] at hk

  refine ⟨k, ?_⟩
  apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos a)
  rw [hfactor, hk]
  ring

end ElementaryNumberTheory.Chapter05
