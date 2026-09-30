import Textbooks.ElementaryNumberTheory.Chapter05.PrimeExponents
import Mathlib.Data.Finsupp.Interval

namespace ElementaryNumberTheory.Chapter05

/-- Theorem: the number of divisors is the product of one plus each prime exponent. -/
theorem tau_eq_prod (n : ℕ) (hn : 0 < n) :
    tau n = ∏ p ∈ (primeExponents n).support, (primeExponents n p + 1) := by
  classical

  have hcard : n.divisors.card = (Finset.Iic (primeExponents n)).card := by
    apply Finset.card_bij (fun d _ => primeExponents d)

    · intro d hd
      exact Finset.mem_Iic.mpr ((dvd_iff_primeExponents_le d n
        (Nat.pos_of_mem_divisors hd) hn).1 (Nat.dvd_of_mem_divisors hd))

    · intro d hd e he hde

      have hh := congrArg factorValue hde
      rwa [(primeExponents_spec d (Nat.pos_of_mem_divisors hd)).2,
        (primeExponents_spec e (Nat.pos_of_mem_divisors he)).2] at hh

    · intro e he

      obtain ⟨hpos, hdiv, heq⟩ := divisor_exponents n hn e (Finset.mem_Iic.mp he)

      exact ⟨factorValue e, Nat.mem_divisors.mpr ⟨hdiv, ne_of_gt hn⟩, heq⟩
  rw [tau, hcard, Finsupp.card_Iic]
  simp only [Nat.card_Iic]

/-- Lemma: the divisors of a prime power are exactly the lower powers. -/
theorem divisors_prime_pow (p k : ℕ) (hp : Chapter02.isPrime p) :
    (p ^ k).divisors = (Finset.range (k + 1)).image (fun j => p ^ j) := by
  classical

  have hpos : 0 < p := by
    have := hp.1
    omega
  ext d
  constructor

  · intro hd

    have hdpos := Nat.pos_of_mem_divisors hd

    have hle := (dvd_iff_primeExponents_le d (p ^ k) hdpos (pow_pos hpos k)).1
      (Nat.dvd_of_mem_divisors hd)
    rw [primeExponents_prime_pow p k hp] at hle

    have he : primeExponents d = Finsupp.single p (primeExponents d p) := by
      ext q
      by_cases hq : q = p

      · subst q
        simp only [Finsupp.single_eq_same]

      · have hh := hle q
        simp only [Finsupp.single_eq_of_ne hq] at hh ⊢
        omega

    have hk : primeExponents d p < k + 1 := by
      have hh := hle p
      simp only [Finsupp.single_eq_same] at hh
      omega

    refine Finset.mem_image.mpr ⟨primeExponents d p, Finset.mem_range.mpr hk, ?_⟩

    have hh := (primeExponents_spec d hdpos).2
    rw [he, factorValue, Finsupp.prod_single_index (pow_zero p)] at hh
    exact hh

  · rintro hd

    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd

    have hjk : j ≤ k := by
      have := Finset.mem_range.mp hj
      omega

    apply Nat.mem_divisors.mpr
    exact ⟨⟨p ^ (k - j), by rw [← pow_add, Nat.add_sub_cancel' hjk]⟩,
      ne_of_gt (pow_pos hpos k)⟩

/-- Theorem: a prime power has k+1 divisors. -/
theorem tau_prime_pow (p k : ℕ) (hp : Chapter02.isPrime p) : tau (p ^ k) = k + 1 := by
  classical
  rw [tau, divisors_prime_pow p k hp, Finset.card_image_of_injective,
    Finset.card_range]

  exact pow_right_injective₀ (by have := hp.1; omega : 0 < p) (by have := hp.1; omega : p ≠ 1)

/-- Theorem: the sum of divisors of a prime power is a geometric sum. -/
theorem sigma_prime_pow (p k : ℕ) (hp : Chapter02.isPrime p) :
    sigma (p ^ k) = ∑ j ∈ Finset.range (k + 1), p ^ j := by
  classical
  rw [sigma, divisors_prime_pow p k hp, Finset.sum_image]
  intro i hi j hj h
  exact pow_right_injective₀ (by have := hp.1; omega : 0 < p) (by have := hp.1; omega : p ≠ 1) h

/-- Lemma: finite geometric sums give the quotient appearing in the divisor formula. -/
theorem geometric_sum_eq_div (p k : ℕ) (hp : 1 < p) :
    (∑ j ∈ Finset.range (k + 1), p ^ j) = (p ^ (k + 1) - 1) / (p - 1) := by
  have hgeom : ∀ r : ℕ, (p - 1) * (∑ j ∈ Finset.range r, p ^ j) + 1 = p ^ r := by
    intro r
    induction r with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, mul_zero, zero_add, pow_zero]

    | succ r ih =>
      rw [Finset.sum_range_succ, pow_succ]

      have hpp : p - 1 + 1 = p := by omega
      nlinarith [congrArg (fun z => z * p ^ r) hpp]

  have h := hgeom (k + 1)

  have hh : p ^ (k + 1) - 1 = (p - 1) * (∑ j ∈ Finset.range (k + 1), p ^ j) := by omega
  rw [hh, Nat.mul_div_right _ (by omega : 0 < p - 1)]

/-- Corollary: the geometric quotient formula for the sum of prime-power divisors. -/
theorem sigma_prime_pow_eq_div (p k : ℕ) (hp : Chapter02.isPrime p) :
    sigma (p ^ k) = (p ^ (k + 1) - 1) / (p - 1) := by
  rw [sigma_prime_pow p k hp, geometric_sum_eq_div p k hp.1]

/-- Lemma: coprimality of positive integers is symmetric. -/
theorem gcd_eq_one_symm (a b : ℕ) (h : Chapter01.gcd a b = 1) :
    Chapter01.gcd b a = 1 := by
  have hnz : (a : ℤ) ≠ 0 ∨ (b : ℤ) ≠ 0 := by
    by_contra hh
    push Not at hh

    have ha : a = 0 := by exact_mod_cast hh.1

    have hb : b = 0 := by exact_mod_cast hh.2
    subst a b
    rw [Nat.cast_zero, Chapter01.gcd_zero_zero] at h
    contradiction

  obtain ⟨u, v, huv⟩ :=
    (Chapter01.gcd_eq_one_iff_exists_mul_add_mul a b hnz).1 h

  apply (Chapter01.gcd_eq_one_iff_exists_mul_add_mul b a hnz.symm).2
  exact ⟨v, u, by linarith⟩

/-- Lemma: powers preserve coprimality. -/
theorem gcd_pow_left (a b k : ℕ) (hb : 0 < b) (h : Chapter01.gcd a b = 1) :
    Chapter01.gcd (a ^ k) b = 1 := by
  induction k with
  | zero =>
    exact (Chapter01.gcd_eq_one_iff_exists_mul_add_mul 1 b (Or.inl (by decide))).2
      ⟨1, 0, by ring⟩

  | succ k ih =>
    rw [pow_succ]
    exact Chapter03.gcd_mul_eq_one _ _ _ ih h (by omega)

/-- Lemma: distinct prime powers are relatively prime. -/
theorem gcd_prime_powers (p q i j : ℕ) (hp : Chapter02.isPrime p)
    (hq : Chapter02.isPrime q) (hne : p ≠ q) : Chapter01.gcd (p ^ i) (q ^ j) = 1 := by
  have hpn : (p : ℤ) ≠ 0 := by
    have := hp.1
    omega

  obtain ⟨_, hdp, hdq, _, _⟩ := Chapter01.gcd_spec p q (Or.inl hpn)

  have hcop : Chapter01.gcd p q = 1 := by
    rcases hp.2 _ (Int.natCast_dvd_natCast.mp hdp) with he | he

    · exact he

    · rw [he] at hdq
      rcases hq.2 p (Int.natCast_dvd_natCast.mp hdq) with hh | hh

      · have := hp.1
        omega

      · exact (hne hh).elim

  apply gcd_pow_left p (q ^ j) i (pow_pos (by
      have := hq.1
      omega) j)

  exact gcd_eq_one_symm _ _ (gcd_pow_left q p j (by
      have := hp.1
      omega)
    (gcd_eq_one_symm p q hcop))

/-- Theorem: a multiplicative function on a nonempty product of pairwise coprime positive
factors is the product of its values. -/
theorem multiplicative_prod {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (g : ι → ℕ) (hg : ∀ i ∈ s, 0 < g i)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Chapter01.gcd (g i) (g j) = 1)
    (f : ℕ → ℤ) (hf : IsMultiplicative f) :
    f (∏ i ∈ s, g i) = ∏ i ∈ s, f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (Finset.not_nonempty_empty hs).elim

  | @insert i s hi ih =>
    by_cases hempty : s = ∅

    · subst s
      simp only [Finset.prod_insert hi, Finset.prod_empty, mul_one]

    · have hgs : ∀ j ∈ s, 0 < g j := fun j hj => hg j (Finset.mem_insert_of_mem hj)

      have hcop := Chapter03.gcd_prod_eq_one s (fun j => (g j : ℤ)) (g i)
        (by
            have := hg i (Finset.mem_insert_self i s)
            omega)
        (fun j hj => hpair j (Finset.mem_insert_of_mem hj) i
          (Finset.mem_insert_self i s) (by
              intro heq
              subst j
              exact hi hj))
      rw [← Nat.cast_prod] at hcop
      rw [Finset.prod_insert hi, mul_comm (g i), hf _ _ (Finset.prod_pos hgs)
        (hg i (Finset.mem_insert_self i s)) hcop,
        ih (Finset.nonempty_iff_ne_empty.mpr hempty) hgs
          (fun j hj k hk => hpair j (Finset.mem_insert_of_mem hj) k
            (Finset.mem_insert_of_mem hk)), Finset.prod_insert hi, mul_comm]

/-- Theorem: a multiplicative function is determined by its prime-power values away from one,
including Burton's identically zero function. -/
theorem multiplicative_prime_powers (f : ℕ → ℤ) (hf : IsMultiplicative f)
    (n : ℕ) (hn : 1 < n) :
    f n = ∏ p ∈ (primeExponents n).support, f (p ^ primeExponents n p) := by
  have hnpos : 0 < n := by omega

  have hspec := primeExponents_spec n hnpos

  have hs : (primeExponents n).support.Nonempty := by
    by_contra h

    have he := Finset.not_nonempty_iff_eq_empty.mp h

    have hv := hspec.2
    change (∏ p ∈ (primeExponents n).support, p ^ primeExponents n p) = n at hv
    rw [he, Finset.prod_empty] at hv
    omega
  calc
    f n = f (factorValue (primeExponents n)) := congrArg f hspec.2.symm
    _ = _ := multiplicative_prod _ hs (fun p => p ^ primeExponents n p)
      (fun p hp => pow_pos (by
          have := (hspec.1 p hp).1
          omega) _)
      (fun p hp q hq hne => gcd_prime_powers p q _ _ (hspec.1 p hp) (hspec.1 q hq) hne) f hf

/-- Theorem: the sum of divisors is the product of the prime-power geometric sums. -/
theorem sigma_eq_prod (n : ℕ) (hn : 1 < n) :
    (sigma n : ℤ) = ∏ p ∈ (primeExponents n).support,
      ((∑ j ∈ Finset.range (primeExponents n p + 1), p ^ j : ℕ) : ℤ) := by
  rw [multiplicative_prime_powers _ sigma_multiplicative n hn]
  apply Finset.prod_congr rfl
  intro p hp
  rw [sigma_prime_pow p _ ((primeExponents_spec n (by omega)).1 p hp)]

/-- Corollary: the geometric quotient form of the divisor-sum product. -/
theorem sigma_eq_prod_quotients (n : ℕ) (hn : 1 < n) :
    (sigma n : ℤ) = ∏ p ∈ (primeExponents n).support,
      (((p ^ (primeExponents n p + 1) - 1) / (p - 1) : ℕ) : ℤ) := by
  rw [sigma_eq_prod n hn]
  apply Finset.prod_congr rfl
  intro p hp

  rw [geometric_sum_eq_div p _ ((primeExponents_spec n (by omega)).1 p hp).1]

end ElementaryNumberTheory.Chapter05
