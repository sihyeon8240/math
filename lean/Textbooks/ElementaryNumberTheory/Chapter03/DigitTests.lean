import Textbooks.ElementaryNumberTheory.Chapter03.Congruences
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ElementaryNumberTheory.Chapter03

/-- Definition: evaluate a list of integer coefficients, least significant first. -/
def positionalValue (b : ℤ) : List ℤ → ℤ

  | [] => 0

  | d :: ds => d + b * positionalValue b ds

/-- Theorem: substitution of congruent arguments preserves polynomial values. -/
theorem positionalValue_modEq (n a b : ℤ) (h : a ≡ b [ZMOD n]) (ds : List ℤ) :
    positionalValue a ds ≡ positionalValue b ds [ZMOD n] := by
  induction ds with
  | nil => exact modEq_refl n 0

  | cons d ds ih => exact modEq_add (modEq_refl n d) (modEq_mul h ih)

/-- Lemma: evaluation at one is the sum of the coefficients. -/
theorem positionalValue_one (ds : List ℤ) : positionalValue 1 ds = ds.sum := by
  induction ds with
  | nil => rfl

  | cons d ds ih => simp only [positionalValue, one_mul, List.sum_cons, ih]

/-- Lemma: congruence preserves divisibility by the modulus. -/
theorem dvd_iff_of_modEq {n a b : ℤ} (h : a ≡ b [ZMOD n]) : n ∣ a ↔ n ∣ b := by
  rw [← modEq_zero_iff, ← modEq_zero_iff]
  exact ⟨fun ha => modEq_trans (modEq_symm h) ha, fun hb => modEq_trans h hb⟩

/-- Theorem: the decimal digit-sum test for nine. -/
theorem nine_dvd_iff_digit_sum (ds : List ℤ) :
    9 ∣ positionalValue 10 ds ↔ 9 ∣ ds.sum := by
  have h := positionalValue_modEq 9 10 1 (by decide) ds
  rw [positionalValue_one] at h
  exact dvd_iff_of_modEq h

/-- Theorem: the decimal digit-sum test for three. -/
theorem three_dvd_iff_digit_sum (ds : List ℤ) :
    3 ∣ positionalValue 10 ds ↔ 3 ∣ ds.sum := by
  have h := positionalValue_modEq 3 10 1 (by decide) ds
  rw [positionalValue_one] at h
  exact dvd_iff_of_modEq h

/-- Definition: the alternating digit sum, starting with the units digit. -/
def alternatingSum : List ℤ → ℤ

  | [] => 0

  | d :: ds => d - alternatingSum ds

/-- Lemma: evaluation at minus one is the alternating sum. -/
theorem positionalValue_neg_one (ds : List ℤ) :
    positionalValue (-1) ds = alternatingSum ds := by
  induction ds with
  | nil => rfl

  | cons d ds ih => simp only [positionalValue, alternatingSum, ih, neg_one_mul, sub_eq_add_neg]

/-- Theorem: the alternating decimal digit-sum test for eleven. -/
theorem eleven_dvd_iff_alternating_sum (ds : List ℤ) :
    11 ∣ positionalValue 10 ds ↔ 11 ∣ alternatingSum ds := by
  have h := positionalValue_modEq 11 10 (-1) (by decide) ds
  rw [positionalValue_neg_one] at h
  exact dvd_iff_of_modEq h

/-- Theorem: a divisor of the base tests only the last digit. -/
theorem dvd_positionalValue_cons_iff (n b d : ℤ) (ds : List ℤ) (h : n ∣ b) :
    n ∣ positionalValue b (d :: ds) ↔ n ∣ d := by

  apply dvd_iff_of_modEq

  obtain ⟨k, hk⟩ := h

  exact (modEq_iff_dvd_sub _ _ _).2
    ⟨k * positionalValue b ds, by
        simp only [positionalValue]
        rw [hk]
        ring⟩

/-- Corollary: divisibility by two is determined by the units digit. -/
theorem two_dvd_iff_last_digit (d : ℤ) (ds : List ℤ) :
    2 ∣ positionalValue 10 (d :: ds) ↔ 2 ∣ d :=
  dvd_positionalValue_cons_iff 2 10 d ds (by decide)

/-- Corollary: divisibility by five means that the units digit is zero or five. -/
theorem five_dvd_iff_last_digit (d : ℤ) (ds : List ℤ) (hd : 0 ≤ d ∧ d < 10) :
    5 ∣ positionalValue 10 (d :: ds) ↔ d = 0 ∨ d = 5 := by
  rw [dvd_positionalValue_cons_iff 5 10 d ds (by decide)]
  constructor

  · rintro ⟨k, hk⟩
    omega

  · rintro (rfl | rfl) <;> decide

/-- Theorem: divisibility by four is determined by the last two digits. -/
theorem four_dvd_iff_last_two_digits (d e : ℤ) (ds : List ℤ) :
    4 ∣ positionalValue 10 (d :: e :: ds) ↔ 4 ∣ d + 10 * e := by

  apply dvd_iff_of_modEq
  exact (modEq_iff_dvd_sub _ _ _).2
    ⟨25 * positionalValue 10 ds, by
        simp only [positionalValue]
        ring⟩

/-- Theorem: a coprime check-digit weight detects every change of a decimal digit. -/
theorem detects_single_digit_error (w d e : ℤ) (hw : Chapter01.gcd 10 w = 1)
    (hd : 0 ≤ d ∧ d < 10) (he : 0 ≤ e ∧ e < 10) (hne : d ≠ e) :
    ¬w * d ≡ w * e [ZMOD 10] := by
  intro h

  obtain ⟨k, hk⟩ := (modEq_iff_dvd_sub _ _ _).1 (modEq_cancel hw h)
  omega

end ElementaryNumberTheory.Chapter03
