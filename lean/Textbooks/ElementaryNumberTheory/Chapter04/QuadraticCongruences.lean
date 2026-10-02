import Textbooks.ElementaryNumberTheory.Chapter04.Wilson

namespace ElementaryNumberTheory.Chapter04

/-- Definition: a quadratic congruence has a nonzero leading coefficient modulo n. -/
structure QuadraticCongruence (n : ℤ) where
  a : ℤ
  b : ℤ
  c : ℤ
  leading_ne_zero : ¬a ≡ 0 [ZMOD n]

/-- Lemma: pairing factorial factors with their negatives gives the half-factorial identity. -/
theorem half_factorial (p m : ℕ) (hp : p = 2 * m + 1) :
    ((p - 1).factorial : ZMod p) = (-1 : ZMod p) ^ m * (m.factorial : ZMod p) ^ 2 := by
  have hprefix : (∏ k ∈ Finset.Ico 1 (m + 1), (k : ZMod p)) = (m.factorial : ZMod p) := by
    rw [← Nat.cast_prod, Finset.prod_Ico_id_eq_factorial]

  have hreflect : (∏ k ∈ Finset.Ico (m + 1) p, (k : ZMod p)) =
      ∏ k ∈ Finset.Ico 1 (m + 1), ((p - k : ℕ) : ZMod p) := by
    rw [Finset.prod_Ico_reflect _ 1 (by omega : m + 1 ≤ p + 1)]
    rw [show p + 1 - (m + 1) = m + 1 by omega, Nat.add_sub_cancel]

  have hnegative : (∏ k ∈ Finset.Ico 1 (m + 1), ((p - k : ℕ) : ZMod p)) =
      (-1 : ZMod p) ^ m * (m.factorial : ZMod p) := by
    have hterm : ∀ k ∈ Finset.Ico 1 (m + 1), ((p - k : ℕ) : ZMod p) = -1 * (k : ZMod p) := by
      intro k hk

      have hkp : k ≤ p := by
        have := Finset.mem_Ico.mp hk
        omega

      rw [Nat.cast_sub hkp, ZMod.natCast_self, zero_sub, neg_one_mul]

    rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_const,
      Nat.card_Ico, Nat.add_sub_cancel, hprefix]

  have hfull : ((p - 1).factorial : ZMod p) = ∏ k ∈ Finset.Ico 1 p, (k : ZMod p) := by
    rw [← Nat.cast_prod, ← Finset.prod_Ico_id_eq_factorial]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ p)]

  rw [hfull, ← Finset.prod_Ico_consecutive (fun k => (k : ZMod p))
    (by omega : 1 ≤ m + 1) (by omega : m + 1 ≤ p), hprefix, hreflect, hnegative]
  ring

/-- Theorem: minus one is a square modulo an odd prime exactly when p is one modulo four. -/
theorem exists_square_eq_neg_one_iff (p : ℕ) (hp : Chapter02.isPrime p) (hodd : Odd p) :
    (∃ x : ℤ, x ^ 2 ≡ -1 [ZMOD (p : ℤ)]) ↔ p % 4 = 1 := by
  have hp2 : 2 < p := by
    have hmod := Nat.odd_iff.mp hodd

    have := hp.1
    omega

  let m := (p - 1) / 2

  have hpm : p = 2 * m + 1 := by
    have hmod := Nat.odd_iff.mp hodd
    dsimp [m]
    omega

  constructor

  · rintro ⟨x, hx⟩

    have hnot : ¬(p : ℤ) ∣ x := by
      intro hd

      have hz := Chapter03.modEq_pow ((Chapter03.modEq_zero_iff _ _).2 hd) 2
      rw [zero_pow (by decide : 2 ≠ 0)] at hz

      have hh := (Chapter03.modEq_iff_dvd_sub _ _ _).1
        (Chapter03.modEq_trans (Chapter03.modEq_symm hz) hx)

      obtain ⟨k, hk⟩ := hh

      have hpz : (2 : ℤ) < p := by
        exact_mod_cast hp2

      have hkpos : 0 < k := by
        nlinarith
      nlinarith

    have hpow := Chapter03.modEq_pow hx m
    rw [← pow_mul, show 2 * m = p - 1 by omega] at hpow

    have hh := Chapter03.modEq_trans (Chapter03.modEq_symm hpow) (fermat p hp x hnot)
    by_contra hne

    have hm : Odd m := Nat.odd_iff.mpr (by omega)
    rw [hm.neg_one_pow] at hh

    obtain ⟨k, hk⟩ := (Chapter03.modEq_iff_dvd_sub _ _ _).1 hh

    have hpz : (2 : ℤ) < p := by
      exact_mod_cast hp2

    have hkneg : k < 0 := by
      nlinarith
    nlinarith

  · intro hpmod

    have hm : Even m := Nat.even_iff.mpr (by omega)

    have hhalf := half_factorial p m hpm
    rw [hm.neg_one_pow, one_mul] at hhalf

    have hw := (ZMod.intCast_eq_intCast_iff _ _ p).2 (wilson p hp)
    simp only [Int.cast_natCast, Int.cast_neg, Int.cast_one] at hw

    refine ⟨m.factorial, ?_⟩
    apply (ZMod.intCast_eq_intCast_iff _ _ p).1
    simpa only [Int.cast_pow, Int.cast_natCast, Int.cast_neg, Int.cast_one] using
      hhalf.symm.trans hw

end ElementaryNumberTheory.Chapter04
