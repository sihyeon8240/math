import Textbooks.ElementaryNumberTheory.Chapter06.Totient
import Mathlib.Tactic.FieldSimp

namespace ElementaryNumberTheory.Chapter06

open Chapter05

/-- Lemma: coprimality has a Bezout characterization even at zero inputs. -/
theorem gcd_eq_one_iff_bezout (a b : ℤ) :
    Chapter01.gcd a b = 1 ↔ ∃ x y : ℤ, 1 = a * x + b * y := by
  by_cases h : a ≠ 0 ∨ b ≠ 0
  · exact Chapter01.gcd_eq_one_iff_exists_mul_add_mul a b h
  · push Not at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Chapter01.gcd_zero_zero, zero_ne_one, zero_mul, zero_add, one_ne_zero,
      exists_const]

/-- Lemma: an integer is coprime with a product exactly when it is coprime with each factor. -/
theorem gcd_mul_iff (a b c : ℤ) :
    Chapter01.gcd a (b * c) = 1 ↔
      Chapter01.gcd a b = 1 ∧ Chapter01.gcd a c = 1 := by
  simp only [gcd_eq_one_iff_bezout]
  constructor

  · rintro ⟨x, y, h⟩
    exact ⟨⟨x, c * y, by nlinarith [h]⟩, ⟨x, b * y, by nlinarith [h]⟩⟩

  · rintro ⟨⟨x, y, h⟩, ⟨u, v, k⟩⟩
    refine ⟨a * x * u + x * c * v + b * y * u, y * v, ?_⟩
    calc
      1 = (a * x + b * y) * (a * u + c * v) := by
        rw [← h, ← k]
        ring
      _ = _ := by ring

/-- Theorem: the rational Euler product for phi, including the empty product at one. -/
theorem totient_eq_mul_prod (n : ℕ) (hn : 0 < n) :
    (Nat.totient n : ℚ) = (n : ℚ) *
      ∏ p ∈ (primeExponents n).support, (1 - 1 / (p : ℚ)) := by
  by_cases hne : n = 1
  · subst n
    simp only [Nat.totient_one, Nat.cast_one, primeExponents_one,
      Finsupp.support_zero, Finset.prod_empty, mul_one]

  have hprod : (Nat.totient n : ℚ) =
      ∏ p ∈ (primeExponents n).support, (Nat.totient (p ^ primeExponents n p) : ℚ) := by
    exact_mod_cast multiplicative_prime_powers _ totient_multiplicative n (by omega)
  have hnprod : (n : ℚ) = ∏ p ∈ (primeExponents n).support, (p : ℚ) ^ primeExponents n p := by
    have h := (primeExponents_spec n hn).2
    change (∏ p ∈ (primeExponents n).support, p ^ primeExponents n p) = n at h
    exact_mod_cast h.symm

  rw [hprod, hnprod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := (primeExponents_spec n hn).1 p hp
  have hk := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
  rw [hr, totient_prime_pow_succ p r hprime]
  have hp1 : 1 ≤ p := by
    have := hprime.1
    omega
  have hpq : (p : ℚ) ≠ 0 := by
    have := hprime.1
    exact_mod_cast (by omega : p ≠ 0)
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp1, Nat.cast_one, pow_succ]
  field_simp

/-- Theorem: the rational form of Möbius inversion for phi. -/
theorem totient_eq_mul_sum_mobius (n : ℕ) (hn : 0 < n) :
    (Nat.totient n : ℚ) = (n : ℚ) * ∑ d ∈ n.divisors, (mobius d : ℚ) / d := by
  have h : (Nat.totient n : ℚ) =
      ∑ d ∈ n.divisors, (mobius d : ℚ) * (n / d : ℕ) := by
    have hcast := congrArg (fun z : ℤ => (z : ℚ)) (totient_eq_sum_mobius n hn)
    simpa only [Int.cast_natCast, Int.cast_sum, Int.cast_mul] using hcast
  rw [h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.cast_div_charZero (Nat.dvd_of_mem_divisors hd)]
  ring

end ElementaryNumberTheory.Chapter06
