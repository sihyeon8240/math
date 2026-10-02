import Textbooks.ElementaryNumberTheory.Chapter01.DiophantineEquations
import Textbooks.ElementaryNumberTheory.Chapter02.Primes
import Mathlib.Data.Int.ModEq

namespace ElementaryNumberTheory.Chapter03

/-- Theorem: congruence is divisibility of the difference, with the lecture's sign. -/
theorem modEq_iff_dvd_sub (n a b : ℤ) : a ≡ b [ZMOD n] ↔ n ∣ a - b := by
  rw [Int.modEq_iff_dvd]
  constructor

  · rintro ⟨k, hk⟩
    exact ⟨-k, by linarith⟩

  · rintro ⟨k, hk⟩
    exact ⟨-k, by linarith⟩

/-- Theorem: congruent integers have the same remainder. -/
theorem modEq_iff_emod_eq (n a b : ℤ) : a ≡ b [ZMOD n] ↔ a % n = b % n :=
  Iff.rfl

/-- Theorem: congruence is reflexive. -/
theorem modEq_refl (n a : ℤ) : a ≡ a [ZMOD n] := rfl

/-- Theorem: congruence is symmetric. -/
theorem modEq_symm {n a b : ℤ} (h : a ≡ b [ZMOD n]) : b ≡ a [ZMOD n] :=
  Eq.symm h

/-- Theorem: congruence is transitive. -/
theorem modEq_trans {n a b c : ℤ} (h : a ≡ b [ZMOD n]) (h' : b ≡ c [ZMOD n]) :
    a ≡ c [ZMOD n] := Eq.trans h h'

/-- Theorem: congruence is compatible with addition. -/
theorem modEq_add {n a b c d : ℤ} (h : a ≡ b [ZMOD n]) (h' : c ≡ d [ZMOD n]) :
    a + c ≡ b + d [ZMOD n] := by
  obtain ⟨u, hu⟩ := (modEq_iff_dvd_sub n a b).1 h
  obtain ⟨v, hv⟩ := (modEq_iff_dvd_sub n c d).1 h'

  exact (modEq_iff_dvd_sub n _ _).2 ⟨u + v, by linarith⟩

/-- Theorem: congruence is compatible with multiplication. -/
theorem modEq_mul {n a b c d : ℤ} (h : a ≡ b [ZMOD n]) (h' : c ≡ d [ZMOD n]) :
    a * c ≡ b * d [ZMOD n] := by
  obtain ⟨u, hu⟩ := (modEq_iff_dvd_sub n a b).1 h
  obtain ⟨v, hv⟩ := (modEq_iff_dvd_sub n c d).1 h'

  exact (modEq_iff_dvd_sub n _ _).2 ⟨u * c + b * v, by
    nlinarith [congrArg (fun z => z * c) hu, congrArg (fun z => z * b) hv]⟩

/-- Theorem: congruence is compatible with every nonnegative integral power. -/
theorem modEq_pow {n a b : ℤ} (h : a ≡ b [ZMOD n]) (k : ℕ) :
    a ^ k ≡ b ^ k [ZMOD n] := by
  induction k with
  | zero =>
    simp only [pow_zero]
    exact modEq_refl n 1

  | succ k ih => simpa only [pow_succ] using modEq_mul ih h

/-- Theorem: congruence to zero is divisibility. -/
theorem modEq_zero_iff (n a : ℤ) : a ≡ 0 [ZMOD n] ↔ n ∣ a := by
  simpa only [sub_zero] using modEq_iff_dvd_sub n a 0

/-- Theorem: each integer has a unique least nonnegative representative. -/
theorem existsUnique_residue (n : ℕ+) (a : ℤ) :
    ∃! r : ℕ, r < n ∧ a ≡ (r : ℤ) [ZMOD (n : ℤ)] := by
  obtain ⟨⟨q, r⟩, ⟨ha, hr⟩, hu⟩ := Chapter01.existsUnique_quotient_remainder a n

  refine ⟨r, ⟨hr, ?_⟩, ?_⟩

  · apply (modEq_iff_dvd_sub _ _ _).2
    exact ⟨q, by
        change a = q * (n : ℤ) + r at ha
        nlinarith⟩

  · intro s hs

    obtain ⟨k, hk⟩ := (modEq_iff_dvd_sub _ _ _).1 hs.2

    have hp : (k, s) = (q, r) := hu (k, s) ⟨by
        dsimp
        nlinarith, hs.1⟩

    exact congrArg Prod.snd hp

/-- Theorem: a factor coprime to the modulus can be cancelled. -/
theorem modEq_cancel {n c a b : ℤ} (hc : Chapter01.gcd n c = 1)
    (h : c * a ≡ c * b [ZMOD n]) : a ≡ b [ZMOD n] := by

  apply (modEq_iff_dvd_sub n a b).2
  apply Chapter01.dvd_of_dvd_mul_of_coprime n c (a - b) hc
  simpa only [mul_sub] using (modEq_iff_dvd_sub n _ _).1 h

/-- Theorem: cancelling a general factor divides the modulus by its gcd. -/
theorem modEq_cancel_gcd {n c a b : ℤ} (hn : n ≠ 0)
    (h : c * a ≡ c * b [ZMOD n]) :
    a ≡ b [ZMOD (n / (Chapter01.gcd n c : ℤ))] := by
  obtain ⟨hd, ⟨u, hu⟩, ⟨v, hv⟩, _, _⟩ := Chapter01.gcd_spec n c (Or.inl hn)

  have hcop := Chapter01.gcd_div_gcd_eq_one n c (Or.inl hn)
  generalize hg : Chapter01.gcd n c = g at *

  have hdne : (g : ℤ) ≠ 0 := by
    exact_mod_cast ne_of_gt hd

  have hnu : n / (g : ℤ) = u := by
    rw [hu]
    exact Int.mul_ediv_cancel_left u hdne

  have hcv : c / (g : ℤ) = v := by
    rw [hv]
    exact Int.mul_ediv_cancel_left v hdne
  rw [hnu, hcv] at hcop

  obtain ⟨k, hk⟩ := (modEq_iff_dvd_sub n _ _).1 h

  have hdiv : u ∣ v * (a - b) := by
    refine ⟨k, ?_⟩
    apply mul_left_cancel₀ hdne
    calc
      (g : ℤ) * (v * (a - b)) = c * a - c * b := by
        rw [hv]
        ring
      _ = (g : ℤ) * (u * k) := by
        rw [hk, hu]
        ring
  rw [hnu]
  exact (modEq_iff_dvd_sub _ _ _).2
    (Chapter01.dvd_of_dvd_mul_of_coprime u v (a - b) hcop hdiv)

/-- Corollary: a zero product modulo a prime has a zero factor. -/
theorem modEq_mul_zero_prime (p : ℕ) (hp : Chapter02.isPrime p) (a b : ℤ)
    (h : a * b ≡ 0 [ZMOD (p : ℤ)]) :
    a ≡ 0 [ZMOD (p : ℤ)] ∨ b ≡ 0 [ZMOD (p : ℤ)] := by
  rw [modEq_zero_iff] at h ⊢
  rw [modEq_zero_iff]
  exact Chapter02.prime_dvd_mul p hp a b h

end ElementaryNumberTheory.Chapter03
