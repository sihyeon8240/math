import Textbooks.ElementaryNumberTheory.Chapter04.Fermat
import Textbooks.ElementaryNumberTheory.Chapter02.PrimeFactorization

namespace ElementaryNumberTheory.Chapter04

/-- Definition: Burton's pseudoprime to base a is composite and satisfies the unrestricted
Fermat congruence. No coprimality assumption is imposed. -/
def IsPseudoprime (a : ℤ) (n : ℕ) : Prop :=
  Chapter02.isComposite n ∧ a ^ n ≡ a [ZMOD (n : ℤ)]

/-- Definition: an absolute pseudoprime satisfies the congruence for every base. -/
def IsAbsolutePseudoprime (n : ℕ) : Prop :=
  Chapter02.isComposite n ∧ ∀ a : ℤ, a ^ n ≡ a [ZMOD (n : ℤ)]

/-- Definition: a positive integer is square-free when no prime square divides it. -/
def IsSquareFree (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, Chapter02.isPrime p → ¬p ^ 2 ∣ n

/-- Lemma: an odd modulus is coprime to two. -/
theorem gcd_odd_two (n : ℕ) (hn : Odd n) : Chapter01.gcd n 2 = 1 := by
  obtain ⟨k, hk⟩ := hn
  apply (Chapter01.gcd_eq_one_iff_exists_mul_add_mul n 2 (Or.inr (by decide))).2
  refine ⟨1, -(k : ℤ), ?_⟩
  exact_mod_cast (show (1 : ℤ) = (n : ℤ) * 1 + 2 * -(k : ℤ) by
    have hh : (n : ℤ) = 2 * (k : ℤ) + 1 := by
      exact_mod_cast hk
    linarith)

/-- Theorem: for odd composite n, the two customary base-two congruences agree. -/
theorem pseudoprime_two_iff (n : ℕ) (hn : Odd n) (hc : Chapter02.isComposite n) :
    IsPseudoprime 2 n ↔ (2 : ℤ) ^ (n - 1) ≡ 1 [ZMOD (n : ℤ)] := by
  have hpos : 0 < n := by
    have := hc.1
    omega

  constructor

  · intro h
    apply Chapter03.modEq_cancel (gcd_odd_two n hn)
    simpa only [← pow_succ', Nat.sub_add_cancel hpos, mul_one] using h.2

  · intro h
    refine ⟨hc, ?_⟩

    have hh := Chapter03.modEq_mul h (Chapter03.modEq_refl (n : ℤ) 2)
    simpa only [← pow_succ, Nat.sub_add_cancel hpos, one_mul] using hh

/-- Lemma: a prime power congruence follows when p-1 divides n-1. -/
theorem fermat_of_sub_one_dvd (p n : ℕ) (hp : Chapter02.isPrime p) (hn : 0 < n)
    (hdiv : p - 1 ∣ n - 1) (a : ℤ) : a ^ n ≡ a [ZMOD (p : ℤ)] := by
  by_cases hpa : (p : ℤ) ∣ a

  · have hh := Chapter03.modEq_pow ((Chapter03.modEq_zero_iff _ _).2 hpa) n
    rw [zero_pow (ne_of_gt hn)] at hh
    exact Chapter03.modEq_trans hh
      (Chapter03.modEq_symm ((Chapter03.modEq_zero_iff _ _).2 hpa))

  · obtain ⟨k, hk⟩ := hdiv

    have hh := Chapter03.modEq_pow (fermat p hp a hpa) k
    rw [← pow_mul, ← hk, one_pow] at hh

    have hh' := Chapter03.modEq_mul hh (Chapter03.modEq_refl (p : ℤ) a)
    simpa only [← pow_succ, Nat.sub_add_cancel hn, one_mul] using hh'

/-- Theorem: a composite product of distinct primes is an absolute pseudoprime if each p-1
divides n-1 (the sufficient criterion in the lecture). -/
theorem absolutePseudoprime_of_prime_product (s : Finset ℕ)
    (hp : ∀ p ∈ s, Chapter02.isPrime p)
    (hc : Chapter02.isComposite (∏ p ∈ s, p))
    (hdiv : ∀ p ∈ s, p - 1 ∣ (∏ q ∈ s, q) - 1) :
    IsAbsolutePseudoprime (∏ p ∈ s, p) := by

  refine ⟨hc, ?_⟩
  intro a
  apply (Chapter03.modEq_iff_dvd_sub _ _ _).2
  rw [Nat.cast_prod]
  apply Chapter03.prod_dvd_of_pairwise s (fun p => (p : ℤ))

  · intro p hps

    have := (hp p hps).1
    omega

  · intro p hps q hqs hne
    exact gcd_distinct_primes p q (hp p hps) (hp q hqs) hne

  · intro p hps
    exact (Chapter03.modEq_iff_dvd_sub _ _ _).1
      (fermat_of_sub_one_dvd p _ (hp p hps) (by
          have := hc.1
          omega) (hdiv p hps) a)

/-- Theorem: every absolute pseudoprime is square-free. -/
theorem absolutePseudoprime_squareFree (n : ℕ) (h : IsAbsolutePseudoprime n) :
    IsSquareFree n := by

  refine ⟨by
      have := h.1.1
      omega, ?_⟩
  intro p hp hpn

  have hn : 2 ≤ n := h.1.1

  obtain ⟨k, hk⟩ := (Chapter03.modEq_iff_dvd_sub _ _ _).1 (h.2 p)
  obtain ⟨t, ht⟩ := hpn

  have ht' : (n : ℤ) = (p : ℤ) ^ 2 * t := by
    exact_mod_cast ht

  have hpow : (p : ℤ) ^ n = (p : ℤ) ^ 2 * (p : ℤ) ^ (n - 2) := by
    rw [← pow_add, Nat.add_sub_cancel' hn]

  have hcancel : (p : ℤ) * ((p : ℤ) ^ (n - 2) - (t : ℤ) * k) = 1 := by
    have hpne : (p : ℤ) ≠ 0 := by
      have := hp.1
      omega

    apply mul_left_cancel₀ hpne
    rw [ht', hpow] at hk
    nlinarith [hk]

  have hd : p ∣ 1 := Int.natCast_dvd_natCast.mp
    ⟨(p : ℤ) ^ (n - 2) - (t : ℤ) * k, hcancel.symm⟩

  obtain ⟨u, hu⟩ := hd

  have := hp.1

  have hu' : 0 < u := by
    nlinarith
  nlinarith

end ElementaryNumberTheory.Chapter04
