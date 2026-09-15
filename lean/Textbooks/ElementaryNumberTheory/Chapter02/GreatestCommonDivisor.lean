import Textbooks.ElementaryNumberTheory.Chapter02.DivisionAlgorithm
import Mathlib.Tactic.Ring

namespace ElementaryNumberTheory.Chapter02

/-- Theorem: a positive common divisor that is a linear combination exists.
Every common divisor divides this combination, by expanding its witnesses. -/
theorem exists_positive_common_divisor (a b : ℤ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ d : ℕ, 0 < d ∧ (d : ℤ) ∣ a ∧ (d : ℤ) ∣ b ∧
      (∃ x y : ℤ, (d : ℤ) = a * x + b * y) ∧
      (∀ c : ℤ, c ∣ a → c ∣ b → c ∣ (d : ℤ)) := by

  classical

  have hpos : 0 < a * a + b * b := by
    rcases hab with ha | hb
    · nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]
    · nlinarith [sq_nonneg a, sq_pos_of_ne_zero hb]

  have hS : ∃ n : ℕ, 0 < n ∧ ∃ x y : ℤ, a * x + b * y = (n : ℤ) := by
    refine ⟨(a * a + b * b).toNat, ?_, a, b, ?_⟩
    · omega
    · exact (Int.toNat_of_nonneg (le_of_lt hpos)).symm

  let d : ℕ := Nat.find hS

  obtain ⟨hdpos, x, y, hxy⟩ := Nat.find_spec hS

  have hminimal (n : ℕ) (hn : 0 < n)
      (hlinear : ∃ u v : ℤ, a * u + b * v = (n : ℤ)) : d ≤ n :=
    Nat.find_min' hS ⟨hn, hlinear⟩

  have hddiv (u v : ℤ) : (d : ℤ) ∣ a * u + b * v := by
    obtain ⟨⟨q, r⟩, ⟨heq, hr⟩, _⟩ :=
      existsUnique_quotient_remainder (a * u + b * v) ⟨d, hdpos⟩

    change a * u + b * v = q * (d : ℤ) + (r : ℤ) at heq
    change r < d at hr

    have hrlinear : a * (u - q * x) + b * (v - q * y) = (r : ℤ) := by
      calc
        a * (u - q * x) + b * (v - q * y) =
            (a * u + b * v) - q * (a * x + b * y) := by ring
        _ = r := by
          rw [hxy]
          linarith [heq]

    have hrzero : r = 0 := by
      by_contra hne

      have hle := hminimal r (Nat.pos_of_ne_zero hne)
        ⟨u - q * x, v - q * y, hrlinear⟩

      omega

    refine ⟨q, ?_⟩
    rw [hrzero] at heq
    simpa only [Nat.cast_zero, add_zero, mul_comm] using heq

  have hda : (d : ℤ) ∣ a := by
    simpa only [mul_one, mul_zero, add_zero] using hddiv 1 0

  have hdb : (d : ℤ) ∣ b := by
    simpa only [mul_one, mul_zero, zero_add] using hddiv 0 1

  have hcommon (c : ℤ) (hca : c ∣ a) (hcb : c ∣ b) : c ∣ (d : ℤ) := by
    obtain ⟨u, hu⟩ := hca
    obtain ⟨v, hv⟩ := hcb

    refine ⟨u * x + v * y, ?_⟩
    rw [← hxy, hu, hv]
    ring

  exact ⟨d, hdpos, hda, hdb, ⟨x, y, hxy.symm⟩, hcommon⟩

/-- Definition: the nonnegative greatest common divisor, constructed from a
positive linear combination when the inputs are not both zero; gcd(0, 0) is zero. -/
noncomputable def gcd (a b : ℤ) : ℕ :=
  if hab : a ≠ 0 ∨ b ≠ 0 then
    Classical.choose (exists_positive_common_divisor a b hab)
  else 0

/-- Theorem: the constructed gcd is positive, divides both inputs, is a
linear combination, and is divisible by every common divisor. -/
theorem gcd_spec (a b : ℤ) (hab : a ≠ 0 ∨ b ≠ 0) :
    0 < gcd a b ∧ (gcd a b : ℤ) ∣ a ∧ (gcd a b : ℤ) ∣ b ∧
      (∃ x y : ℤ, (gcd a b : ℤ) = a * x + b * y) ∧
      (∀ c : ℤ, c ∣ a → c ∣ b → c ∣ (gcd a b : ℤ)) := by
  rw [gcd, dif_pos hab]
  exact Classical.choose_spec (exists_positive_common_divisor a b hab)

/-- Theorem: every common divisor is at most the positive gcd.
This verifies the order-theoretic meaning of "greatest" directly. -/
theorem common_divisor_le_gcd (a b c : ℤ) (hab : a ≠ 0 ∨ b ≠ 0)
    (hca : c ∣ a) (hcb : c ∣ b) : c ≤ (gcd a b : ℤ) := by
  obtain ⟨hpos, _, _, _, hcommon⟩ := gcd_spec a b hab
  have hdpos : (0 : ℤ) < gcd a b := by exact_mod_cast hpos
  obtain ⟨k, hk⟩ := hcommon c hca hcb
  by_cases hc : 0 < c
  · have hkpos : 0 < k := by nlinarith
    have hkone : 1 ≤ k := hkpos
    nlinarith
  · linarith

/-- Theorem: the total definition assigns zero to the zero pair. -/
theorem gcd_zero_zero : gcd 0 0 = 0 := by
  unfold gcd
  rw [dif_neg (by rintro (h | h); exact h rfl; exact h rfl)]

/-- Theorem: the order characterization uniquely determines the gcd. -/
theorem gcd_eq_of_greatest (a b : ℤ) (hab : a ≠ 0 ∨ b ≠ 0) (d : ℕ)
    (hda : (d : ℤ) ∣ a) (hdb : (d : ℤ) ∣ b)
    (hgreatest : ∀ c : ℤ, c ∣ a → c ∣ b → c ≤ (d : ℤ)) : gcd a b = d := by
  have hspec := gcd_spec a b hab
  have hle := hgreatest (gcd a b) hspec.2.1 hspec.2.2.1
  have hge := common_divisor_le_gcd a b d hab hda hdb
  exact_mod_cast (le_antisymm hle hge)

/-- Theorem: Bezout's identity for the gcd constructed in this book. -/
theorem exists_gcd_eq_mul_add_mul (a b : ℤ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ x y : ℤ, (gcd a b : ℤ) = a * x + b * y := by
  exact (gcd_spec a b hab).2.2.2.1

/-- Theorem: integer linear combinations are exactly the multiples of the
locally constructed gcd. -/
theorem linear_combinations_eq_gcd_multiples (a b : ℤ) (hab : a ≠ 0 ∨ b ≠ 0) :
    {z : ℤ | ∃ x y : ℤ, z = a * x + b * y} =
      {z : ℤ | ∃ n : ℤ, z = n * (gcd a b : ℤ)} := by

  obtain ⟨x₀, y₀, hbezout⟩ := exists_gcd_eq_mul_add_mul a b hab

  have hcommon := (gcd_spec a b hab).2

  obtain ⟨u, hu⟩ := hcommon.1
  obtain ⟨v, hv⟩ := hcommon.2.1

  apply Set.ext
  intro z
  constructor

  · rintro ⟨x, y, hz⟩

    refine ⟨u * x + v * y, ?_⟩
    calc
      z = a * x + b * y := hz
      _ = ((gcd a b : ℤ) * u) * x + ((gcd a b : ℤ) * v) * y := by
        rw [← hu, ← hv]
      _ = (u * x + v * y) * (gcd a b : ℤ) := by ring

  · rintro ⟨n, hz⟩

    refine ⟨n * x₀, n * y₀, ?_⟩
    rw [hz, hbezout]
    ring

/-- Theorem: Theorem 2.4, the Bezout characterization of coprimality. -/
theorem gcd_eq_one_iff_exists_mul_add_mul (a b : ℤ) (hab : a ≠ 0 ∨ b ≠ 0) :
    gcd a b = 1 ↔ ∃ x y : ℤ, 1 = a * x + b * y := by
  constructor
  · intro h
    obtain ⟨x, y, hxy⟩ := exists_gcd_eq_mul_add_mul a b hab
    exact ⟨x, y, by simpa only [h, Nat.cast_one] using hxy⟩
  · rintro ⟨x, y, hxy⟩
    apply gcd_eq_of_greatest a b hab 1
    · exact ⟨a, by ring⟩
    · exact ⟨b, by ring⟩
    · intro c hca hcb
      obtain ⟨u, hu⟩ := hca
      obtain ⟨v, hv⟩ := hcb
      have hone : 1 = c * (u * x + v * y) := by
        calc
          1 = a * x + b * y := hxy
          _ = c * (u * x + v * y) := by rw [hu, hv]; ring
      by_cases hc : 0 < c
      · have hk : 0 < u * x + v * y := by nlinarith
        have hkone : 1 ≤ u * x + v * y := hk
        norm_num only [Nat.cast_one]
        nlinarith
      · norm_num only [Nat.cast_one]
        omega

/-- Corollary: dividing a nonzero pair by its positive gcd gives
relatively prime integers (Corollary 1 to Theorem 2.4). -/
theorem gcd_div_gcd_eq_one (a b : ℤ) (hab : a ≠ 0 ∨ b ≠ 0) :
    gcd (a / (gcd a b : ℤ)) (b / (gcd a b : ℤ)) = 1 := by
  obtain ⟨hdpos, ⟨u, hu⟩, ⟨v, hv⟩, ⟨x, y, hxy⟩, _⟩ := gcd_spec a b hab
  generalize hg : gcd a b = d at *
  have hdne : (d : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hdpos)
  have ha : a / (d : ℤ) = u := by rw [hu]; exact Int.mul_ediv_cancel_left u hdne
  have hb : b / (d : ℤ) = v := by rw [hv]; exact Int.mul_ediv_cancel_left v hdne
  have hone : (1 : ℤ) = u * x + v * y := by
    apply mul_left_cancel₀ hdne
    calc
      (d : ℤ) * 1 = a * x + b * y := by simpa using hxy
      _ = (d : ℤ) * (u * x + v * y) := by rw [hu, hv]; ring
  have huv : u ≠ 0 ∨ v ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨rfl, rfl⟩ := h
    norm_num at hone
  rw [ha, hb]
  exact (gcd_eq_one_iff_exists_mul_add_mul u v huv).2 ⟨x, y, hone⟩

/-- Corollary: coprime divisors have a product dividing the same
integer (Corollary 2 to Theorem 2.4). -/
theorem mul_dvd_of_coprime (a b c : ℤ) (hab : gcd a b = 1)
    (hac : a ∣ c) (hbc : b ∣ c) : a * b ∣ c := by
  have hnz : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨rfl, rfl⟩ := h
    rw [gcd_zero_zero] at hab
    contradiction
  obtain ⟨x, y, hxy⟩ := (gcd_eq_one_iff_exists_mul_add_mul a b hnz).1 hab
  obtain ⟨r, hr⟩ := hac
  obtain ⟨s, hs⟩ := hbc
  refine ⟨s * x + r * y, ?_⟩
  calc
    c = c * (a * x + b * y) := by rw [← hxy]; ring
    _ = a * c * x + b * c * y := by ring
    _ = a * (b * s) * x + b * (a * r) * y := by nth_rw 1 [hs]; rw [hr]
    _ = (a * b) * (s * x + r * y) := by ring

/-- Theorem: Theorem 2.5, Euclid's lemma for coprime integers. -/
theorem dvd_of_dvd_mul_of_coprime (a b c : ℤ) (hab : gcd a b = 1)
    (hdiv : a ∣ b * c) : a ∣ c := by
  have hnz : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨rfl, rfl⟩ := h
    rw [gcd_zero_zero] at hab
    contradiction
  obtain ⟨x, y, hxy⟩ := (gcd_eq_one_iff_exists_mul_add_mul a b hnz).1 hab
  obtain ⟨k, hk⟩ := hdiv
  refine ⟨c * x + k * y, ?_⟩
  calc
    c = (a * x + b * y) * c := by rw [← hxy]; ring
    _ = a * (c * x) + (b * c) * y := by ring
    _ = a * (c * x + k * y) := by rw [hk]; ring

/-- Theorem: Theorem 2.6, the divisibility characterization of
 the positive gcd, with the candidate divisor an integer. -/
theorem eq_gcd_iff_common_divisor (a b d : ℤ) (hab : a ≠ 0 ∨ b ≠ 0)
    (hd : 0 < d) :
    d = (gcd a b : ℤ) ↔
      d ∣ a ∧ d ∣ b ∧ (∀ c : ℤ, c ∣ a → c ∣ b → c ∣ d) := by
  constructor
  · intro heq
    subst d
    obtain ⟨_, hda, hdb, _, hcommon⟩ := gcd_spec a b hab
    exact ⟨hda, hdb, hcommon⟩
  · rintro ⟨hda, hdb, hcommon⟩
    have hle := common_divisor_le_gcd a b d hab hda hdb
    obtain ⟨hgpos, hga, hgb, _, _⟩ := gcd_spec a b hab
    obtain ⟨k, hk⟩ := hcommon (gcd a b) hga hgb
    have hgpos' : (0 : ℤ) < gcd a b := by exact_mod_cast hgpos
    have hkpos : 0 < k := by nlinarith
    have hkone : 1 ≤ k := hkpos
    have hge : (gcd a b : ℤ) ≤ d := by nlinarith
    exact le_antisymm hle hge

end ElementaryNumberTheory.Chapter02
