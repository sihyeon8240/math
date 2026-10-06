import Textbooks.ElementaryNumberTheory.Chapter06.Totient
import Mathlib.Data.ZMod.Basic

namespace ElementaryNumberTheory.Chapter06

/-- Definition: a Bezout witness represents the inverse of a reduced residue class. -/
noncomputable def unitOfGcdEqOne (n : ℕ) (hn : 0 < n) (a : ℤ)
    (ha : Chapter01.gcd a n = 1) : (ZMod n)ˣ := by
  have hz : (n : ℤ) ≠ 0 := by omega
  let h := (Chapter01.gcd_eq_one_iff_exists_mul_add_mul a n (Or.inr hz)).1 ha
  let x := h.choose
  have hxy := h.choose_spec.choose_spec
  have hcast := congrArg (fun z : ℤ => (z : ZMod n)) hxy
  simp only [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    ZMod.natCast_self, zero_mul, add_zero] at hcast
  exact ⟨a, x, hcast.symm, by
    rw [mul_comm]
    exact hcast.symm⟩

/-- Lemma: the constructed unit represents the given integer. -/
theorem coe_unitOfGcdEqOne (n : ℕ) (hn : 0 < n) (a : ℤ)
    (ha : Chapter01.gcd a n = 1) :
    (unitOfGcdEqOne n hn a ha : ZMod n) = a := by
  rfl

/-- Lemma: multiplication by a coprime integer permutes the reduced residue classes. -/
theorem reduced_residue_permutation (n : ℕ) (hn : 1 < n) (a : ℤ)
    (ha : Chapter01.gcd a n = 1) :
    Function.Bijective (fun b : (ZMod n)ˣ => unitOfGcdEqOne n (by omega) a ha * b) := by
  let u := unitOfGcdEqOne n (by omega) a ha
  constructor
  · intro b c h
    exact mul_left_cancel h
  · intro b
    refine ⟨u⁻¹ * b, ?_⟩
    change u * (u⁻¹ * b) = b
    simp only [mul_inv_cancel_left]

/-- Theorem: Euler's congruence for every positive modulus and every coprime integer. -/
theorem euler (n : ℕ) (hn : 0 < n) (a : ℤ) (ha : Chapter01.gcd a n = 1) :
    a ^ Nat.totient n ≡ 1 [ZMOD (n : ℤ)] := by
  classical
  let : NeZero n := ⟨ne_of_gt hn⟩
  let u := unitOfGcdEqOne n hn a ha

  have hperm : (∏ b : (ZMod n)ˣ, u * b) = ∏ b : (ZMod n)ˣ, b := by
    apply Finset.prod_bij (fun b _ => u * b)
    · intro b hb
      exact Finset.mem_univ _
    · intro b hb c hc h
      exact mul_left_cancel h
    · intro b hb
      exact ⟨u⁻¹ * b, Finset.mem_univ _, by simp only [mul_inv_cancel_left]⟩
    · intro b hb
      rfl

  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] at hperm
  have hpow : u ^ Fintype.card (ZMod n)ˣ = 1 :=
    mul_right_cancel (hperm.trans (one_mul _).symm)
  have hval := congrArg (fun v : (ZMod n)ˣ => (v : ZMod n)) hpow
  rw [Units.val_pow_eq_pow_val, Units.val_one, ZMod.card_units_eq_totient] at hval
  change (unitOfGcdEqOne n hn a ha : ZMod n) ^ Nat.totient n = 1 at hval
  rw [coe_unitOfGcdEqOne] at hval

  apply (ZMod.intCast_eq_intCast_iff _ _ n).1
  simpa only [Int.cast_pow, Int.cast_one] using hval

/-- Corollary: Fermat's congruence follows from Euler's theorem and phi(p)=p-1. -/
theorem fermat_of_euler (p : ℕ) (hp : Chapter02.isPrime p) (a : ℤ)
    (ha : ¬(p : ℤ) ∣ a) : a ^ (p - 1) ≡ 1 [ZMOD (p : ℤ)] := by
  have hpos : 0 < p := by
    have := hp.1
    omega
  have hz : (p : ℤ) ≠ 0 := by omega
  obtain ⟨_, hda, hdp, _, _⟩ := Chapter01.gcd_spec a p (Or.inr hz)
  have hcop : Chapter01.gcd a p = 1 := by
    rcases hp.2 _ (Int.natCast_dvd_natCast.mp hdp) with h | h
    · exact h
    · rw [h] at hda
      exact (ha hda).elim

  simpa only [totient_prime p hp] using euler p hpos a hcop

end ElementaryNumberTheory.Chapter06
