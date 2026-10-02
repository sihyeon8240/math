import Textbooks.ElementaryNumberTheory.Chapter04.Pseudoprimes

namespace ElementaryNumberTheory.Chapter04

/-- Definition: the Mersenne number with exponent n. -/
def mersenne (n : ℕ) : ℕ := 2 ^ n - 1

/-- Lemma: Mersenne divisibility follows from divisibility of the exponents. -/
theorem mersenne_dvd (d n : ℕ) (h : d ∣ n) : mersenne d ∣ mersenne n := by
  obtain ⟨k, rfl⟩ := h

  have hd : (2 : ℤ) ^ d ≡ 1 [ZMOD ((mersenne d : ℕ) : ℤ)] := by
    apply (Chapter03.modEq_iff_dvd_sub _ _ _).2
    refine ⟨1, ?_⟩
    simp only [mersenne, Nat.cast_sub (by
        have := pow_pos (by decide : 0 < (2 : ℕ)) d
        omega : 1 ≤ 2 ^ d), Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_one, mul_one]

  have hh := Chapter03.modEq_pow hd k
  rw [← pow_mul, one_pow] at hh

  apply Int.natCast_dvd_natCast.mp

  have hcast : ((mersenne (d * k) : ℕ) : ℤ) = (2 : ℤ) ^ (d * k) - 1 := by
    simp only [mersenne, Nat.cast_sub (by
        have := pow_pos (by decide : 0 < (2 : ℕ)) (d * k)
        omega : 1 ≤ 2 ^ (d * k)),
      Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]

  rw [hcast]
  exact (Chapter03.modEq_iff_dvd_sub _ _ _).1 hh

/-- Lemma: Mersenne numbers grow beyond their exponents from exponent two onward. -/
theorem lt_mersenne (n : ℕ) (hn : 2 ≤ n) : n < mersenne n := by
  have hh : ∀ k : ℕ, k + 3 < 2 ^ (k + 2) := by
    intro k
    induction k with
    | zero => decide

    | succ k ih =>
      rw [show k + 1 + 2 = (k + 2) + 1 by omega, pow_succ]
      nlinarith

  have h := hh (n - 2)
  rw [Nat.sub_add_cancel hn] at h
  dsimp [mersenne]
  omega

/-- Theorem: a composite exponent produces a composite Mersenne number. -/
theorem mersenne_composite (n : ℕ) (hc : Chapter02.isComposite n) :
    Chapter02.isComposite (mersenne n) := by
  have hdiv : ∃ d : ℕ, d ∣ n ∧ d ≠ 1 ∧ d ≠ n := by
    by_contra h
    push Not at h
    apply hc.2
    exact ⟨hc.1, fun d hd => by
      by_cases h₁ : d = 1

      · exact Or.inl h₁

      · exact Or.inr (h d hd h₁)⟩

  obtain ⟨d, hd, hd1, hdn⟩ := hdiv

  have hnpos : 0 < n := by
    have := hc.1
    omega

  have hdpos : 0 < d := by
    obtain ⟨k, hk⟩ := hd
    nlinarith

  have hdlt : d < n := lt_of_le_of_ne (Nat.le_of_dvd hnpos hd) hdn

  have hd2 : 2 ≤ d := by
    omega

  have hsmall : mersenne d < mersenne n := by
    have hpow := Nat.pow_lt_pow_right (by decide : 1 < 2) hdlt

    have hpos : 0 < 2 ^ d := by
      positivity
    dsimp [mersenne]
    omega

  refine ⟨lt_trans hc.1 (lt_mersenne n (by
      have := hc.1
      omega)), ?_⟩
  intro hp
  rcases hp.2 (mersenne d) (mersenne_dvd d n hd) with h₁ | h₂

  · have := lt_mersenne d hd2
    omega

  · omega

/-- Theorem: a base-two pseudoprime yields a larger Mersenne pseudoprime. -/
theorem mersenne_pseudoprime (n : ℕ) (h : IsPseudoprime 2 n) :
    IsPseudoprime 2 (mersenne n) ∧ n < mersenne n := by
  have hn : 2 ≤ n := h.1.1

  have hlarge := lt_mersenne n hn

  have hpow : 2 ≤ 2 ^ n := by
    have hh : 1 ≤ 2 ^ (n - 1) := by
      have := pow_pos (by decide : 0 < (2 : ℕ)) (n - 1)
      omega

    have he : 2 ^ n = 2 ^ (n - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
    omega

  have hdiv : n ∣ mersenne n - 1 := by
    apply Int.natCast_dvd_natCast.mp

    have hh := (Chapter03.modEq_iff_dvd_sub _ _ _).1 h.2

    have he : ((mersenne n - 1 : ℕ) : ℤ) = (2 : ℤ) ^ n - 2 := by
      rw [mersenne, Nat.sub_sub, Nat.cast_sub hpow, Nat.cast_pow, Nat.cast_ofNat]
    rwa [he]

  obtain ⟨k, hk⟩ := hdiv

  have hbase : (2 : ℤ) ^ n ≡ 1 [ZMOD ((mersenne n : ℕ) : ℤ)] := by
    apply (Chapter03.modEq_iff_dvd_sub _ _ _).2
    refine ⟨1, ?_⟩
    simp only [mersenne, Nat.cast_sub (by omega : 1 ≤ 2 ^ n),
      Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, mul_one]

  have hpower := Chapter03.modEq_pow hbase k
  rw [← pow_mul, ← hk, one_pow] at hpower

  have hfinal := Chapter03.modEq_mul hpower
    (Chapter03.modEq_refl ((mersenne n : ℕ) : ℤ) 2)
  rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ mersenne n), one_mul] at hfinal

  exact ⟨⟨mersenne_composite n h.1, hfinal⟩, hlarge⟩

/-- Lemma: a positive exponent gives an odd Mersenne number. -/
theorem mersenne_odd (n : ℕ) (hn : 0 < n) : Odd (mersenne n) := by
  have hp : 0 < 2 ^ (n - 1) := pow_pos (by decide) _

  have he : 2 ^ n = 2 ^ (n - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel hn]

  apply Nat.odd_iff.mpr
  dsimp [mersenne]
  rw [he]
  omega

/-- Lemma: 341 is a base-two pseudoprime, used to start the unbounded construction. -/
private theorem pseudoprime_seed : IsPseudoprime 2 341 := by
  refine ⟨⟨by decide, ?_⟩, ?_⟩

  · intro hp

    have hdiv : 11 ∣ 341 := ⟨31, rfl⟩
    rcases hp.2 11 hdiv with h | h <;> omega

  · exact fermat_two_primes 11 31 (Nat.prime_def.mp (by decide))
      (Nat.prime_def.mp (by decide)) (by decide) 2 (by decide) (by decide)

/-- Corollary: odd base-two pseudoprimes exceed every bound. -/
theorem exists_odd_pseudoprime_gt (B : ℕ) :
    ∃ n : ℕ, B < n ∧ Odd n ∧ IsPseudoprime 2 n := by
  induction B with
  | zero => exact ⟨341, by decide, by decide, pseudoprime_seed⟩

  | succ B ih =>
    obtain ⟨n, hBn, hodd, hn⟩ := ih
    obtain ⟨hnext, hlarge⟩ := mersenne_pseudoprime n hn

    have hnpos : 0 < n := Nat.zero_lt_of_lt hn.1.1

    exact ⟨mersenne n, by omega, mersenne_odd n hnpos, hnext⟩

/-- Corollary: there are infinitely many odd base-two pseudoprimes. -/
theorem infinite_odd_pseudoprimes : {n : ℕ | Odd n ∧ IsPseudoprime 2 n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro B

  obtain ⟨n, hB, hodd, hn⟩ := exists_odd_pseudoprime_gt B

  exact ⟨n, ⟨hodd, hn⟩, hB⟩

end ElementaryNumberTheory.Chapter04
