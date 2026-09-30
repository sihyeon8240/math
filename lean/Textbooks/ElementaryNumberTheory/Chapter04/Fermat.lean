import Textbooks.ElementaryNumberTheory.Chapter03.ChineseRemainder
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace ElementaryNumberTheory.Chapter04

open scoped BigOperators

/-- Lemma: permutation of a finite product gives the power identity. -/
private theorem pow_card_by_permutation {G : Type*} [CommGroup G] [Fintype G]
    (a : G) : a ^ Fintype.card G = 1 := by
  classical

  have hperm : (∏ x : G, a * x) = ∏ x : G, x := by
    apply Finset.prod_bij (fun x _ => a * x)

    · intro x hx
      exact Finset.mem_univ _

    · intro x hx y hy hxy
      exact mul_left_cancel hxy

    · intro y hy
      exact ⟨a⁻¹ * y, Finset.mem_univ _, by simp only [mul_inv_cancel_left]⟩

    · intro x hx
      rfl
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] at hperm
  exact mul_right_cancel (hperm.trans (one_mul _).symm)

/-- Theorem: Fermat's little theorem for an integer not divisible by a prime. -/
theorem fermat (p : ℕ) (hp : Chapter02.isPrime p) (a : ℤ) (ha : ¬(p : ℤ) ∣ a) :
    a ^ (p - 1) ≡ 1 [ZMOD (p : ℤ)] := by
  let : Fact p.Prime := ⟨Nat.prime_def.mpr hp⟩

  have hne : (a : ZMod p) ≠ 0 := by
    intro h
    exact ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).1 h)

  have h := pow_card_by_permutation (Units.mk0 (a : ZMod p) hne)

  have hv := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h
  simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one,
    Fintype.card_units, ZMod.card] at hv

  apply (ZMod.intCast_eq_intCast_iff _ _ p).1
  simpa only [Int.cast_pow, Int.cast_one] using hv

/-- Corollary: every integer satisfies the unrestricted Fermat congruence. -/
theorem fermat_all (p : ℕ) (hp : Chapter02.isPrime p) (a : ℤ) :
    a ^ p ≡ a [ZMOD (p : ℤ)] := by
  have hpos : 0 < p := by
    have := hp.1
    omega
  by_cases hpa : (p : ℤ) ∣ a

  · have hz := Chapter03.modEq_pow ((Chapter03.modEq_zero_iff _ _).2 hpa) p
    rw [zero_pow (ne_of_gt hpos)] at hz
    exact Chapter03.modEq_trans hz
      (Chapter03.modEq_symm ((Chapter03.modEq_zero_iff _ _).2 hpa))

  · have h := Chapter03.modEq_mul (fermat p hp a hpa) (Chapter03.modEq_refl (p : ℤ) a)
    simpa only [← pow_succ, Nat.sub_add_cancel hpos, one_mul] using h

/-- Corollary: failure of Fermat's congruence certifies compositeness. -/
theorem composite_of_not_fermat (n : ℕ) (hn : 1 < n) (a : ℤ)
    (h : ¬a ^ n ≡ a [ZMOD (n : ℤ)]) : Chapter02.isComposite n :=
  ⟨hn, fun hp => h (fermat_all n hp a)⟩

/-- Lemma: distinct primes are relatively prime. -/
theorem gcd_distinct_primes (p q : ℕ) (hp : Chapter02.isPrime p)
    (hq : Chapter02.isPrime q) (hne : p ≠ q) : Chapter01.gcd p q = 1 := by
  have hnz : (p : ℤ) ≠ 0 := by
    have := hp.1
    omega

  obtain ⟨_, hdp, hdq, _, _⟩ := Chapter01.gcd_spec p q (Or.inl hnz)
  rcases hp.2 _ (Int.natCast_dvd_natCast.mp hdp) with h | h

  · exact h

  · rw [h] at hdq
    rcases hq.2 p (Int.natCast_dvd_natCast.mp hdq) with he | he

    · have := hp.1
      omega

    · exact (hne he).elim

/-- Lemma: the two-prime congruence criterion used in constructing pseudoprimes. -/
theorem fermat_two_primes (p q : ℕ) (hp : Chapter02.isPrime p)
    (hq : Chapter02.isPrime q) (hne : p ≠ q) (a : ℤ)
    (hpq : a ^ p ≡ a [ZMOD (q : ℤ)]) (hqp : a ^ q ≡ a [ZMOD (p : ℤ)]) :
    a ^ (p * q) ≡ a [ZMOD ((p * q : ℕ) : ℤ)] := by
  have h₁ := Chapter03.modEq_trans (Chapter03.modEq_pow hqp p) (fermat_all p hp a)

  have h₂ := Chapter03.modEq_trans (Chapter03.modEq_pow hpq q) (fermat_all q hq a)
  rw [← pow_mul, Nat.mul_comm q p] at h₁
  rw [← pow_mul] at h₂
  apply (Chapter03.modEq_iff_dvd_sub _ _ _).2
  rw [Nat.cast_mul]
  exact Chapter01.mul_dvd_of_coprime p q _ (gcd_distinct_primes p q hp hq hne)
    ((Chapter03.modEq_iff_dvd_sub _ _ _).1 h₁) ((Chapter03.modEq_iff_dvd_sub _ _ _).1 h₂)

end ElementaryNumberTheory.Chapter04
