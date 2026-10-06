import Textbooks.ElementaryNumberTheory.Chapter06.Euler
import Textbooks.ElementaryNumberTheory.Chapter06.TotientFormulas

namespace ElementaryNumberTheory.Chapter06

/-- Theorem: Euler powers of the complementary products solve a finite CRT system. -/
theorem chinese_remainder_euler {ι : Type*} [DecidableEq ι] (s : Finset ι) (n : ι → ℕ) (a : ι → ℤ)
    (hn : ∀ i ∈ s, 0 < n i)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Chapter01.gcd (n i) (n j) = 1) :
    ∀ i ∈ s, (∑ j ∈ s, a j * (∏ k ∈ s.erase j, (n k : ℤ)) ^ Nat.totient (n j)) ≡
      a i [ZMOD (n i : ℤ)] := by
  classical
  intro i hi
  let N (j : ι) : ℤ := ∏ k ∈ s.erase j, (n k : ℤ)
  have hz : (n i : ℤ) ≠ 0 := by
    have := hn i hi
    omega
  have hcop : Chapter01.gcd (N i) (n i) = 1 := by
    apply Chapter03.gcd_prod_eq_one _ _ _ hz
    intro j hj
    exact hpair j (Finset.mem_of_mem_erase hj) i hi (Finset.ne_of_mem_erase hj)
  have he := euler (n i) (hn i hi) (N i) hcop
  have hev := (ZMod.intCast_eq_intCast_iff _ _ (n i)).2 he
  rw [Int.cast_pow, Int.cast_one] at hev

  apply (ZMod.intCast_eq_intCast_iff _ _ (n i)).1
  rw [Int.cast_sum]
  rw [Finset.sum_eq_single i]

  · change ((a i * N i ^ Nat.totient (n i) : ℤ) : ZMod (n i)) = (a i : ZMod (n i))
    rw [Int.cast_mul, Int.cast_pow, hev, mul_one]

  · intro j hj hji
    have hd : (n i : ℤ) ∣ N j :=
      Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨Ne.symm hji, hi⟩)
    have hzero := (ZMod.intCast_zmod_eq_zero_iff_dvd (N j) (n i)).2 hd
    change ((a j * N j ^ Nat.totient (n j) : ℤ) : ZMod (n i)) = 0
    rw [Int.cast_mul, Int.cast_pow, hzero,
      zero_pow (ne_of_gt (totient_pos (n j) (hn j hj))), mul_zero]

  · exact fun h => (h hi).elim

/-- Lemma: local coprimality is symmetric, including zero inputs. -/
theorem gcd_eq_one_comm (a b : ℤ) : Chapter01.gcd a b = 1 ↔ Chapter01.gcd b a = 1 := by
  simp only [gcd_eq_one_iff_bezout]
  constructor

  · rintro ⟨x, y, h⟩
    exact ⟨y, x, by nlinarith [h]⟩

  · rintro ⟨x, y, h⟩
    exact ⟨y, x, by nlinarith [h]⟩

/-- Lemma: an integer not divisible by a prime is coprime with it. -/
theorem gcd_prime_eq_one (p : ℕ) (hp : Chapter02.isPrime p) (a : ℤ)
    (ha : ¬(p : ℤ) ∣ a) : Chapter01.gcd a p = 1 := by
  have hz : (p : ℤ) ≠ 0 := by
    have := hp.1
    omega
  obtain ⟨_, hda, hdp, _, _⟩ := Chapter01.gcd_spec a p (Or.inr hz)
  rcases hp.2 _ (Int.natCast_dvd_natCast.mp hdp) with h | h
  · exact h
  · rw [h] at hda
    exact (ha hda).elim

/-- Theorem: a positive integer coprime with ten divides a positive-length repunit. -/
theorem exists_repunit (n : ℕ) (hn : 0 < n) (hcop : Chapter01.gcd 10 n = 1) :
    ∃ m : ℕ, 0 < m ∧ (n : ℤ) ∣ ∑ j ∈ Finset.range m, (10 : ℤ) ^ j := by
  have h9 : Chapter01.gcd 10 9 = 1 :=
    (gcd_eq_one_iff_bezout 10 9).2 ⟨1, -1, by ring⟩
  have h := (gcd_mul_iff 10 9 n).2 ⟨h9, hcop⟩
  have h' : Chapter01.gcd 10 ((9 * n : ℕ) : ℤ) = 1 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
  let m := Nat.totient (9 * n)
  have he := euler (9 * n) (by omega) 10 h'
  have hd := (Chapter03.modEq_iff_dvd_sub _ _ _).1 he

  have hgeom (r : ℕ) : 9 * (∑ j ∈ Finset.range r, (10 : ℤ) ^ j) = 10 ^ r - 1 := by
    induction r with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, mul_zero, pow_zero, sub_self]
    | succ r ih =>
      rw [Finset.sum_range_succ, pow_succ]
      nlinarith [ih]

  obtain ⟨k, hk⟩ := hd
  refine ⟨m, totient_pos _ (by omega), k, ?_⟩
  have hg := hgeom m
  rw [Nat.cast_mul, Nat.cast_ofNat] at hk
  change 10 ^ m - 1 = 9 * (n : ℤ) * k at hk
  nlinarith [hk, hg]

/-- Corollary: every positive odd integer not divisible by five divides a repunit. -/
theorem exists_repunit_of_odd (n : ℕ) (hn : 0 < n) (hodd : Odd n) (hfive : ¬5 ∣ n) :
    ∃ m : ℕ, 0 < m ∧ (n : ℤ) ∣ ∑ j ∈ Finset.range m, (10 : ℤ) ^ j := by
  have h2 : ¬(2 : ℤ) ∣ (n : ℤ) := by
    intro h
    exact hodd.not_two_dvd_nat (Int.natCast_dvd_natCast.mp h)
  have h5 : ¬(5 : ℤ) ∣ (n : ℤ) := by
    intro h
    exact hfive (Int.natCast_dvd_natCast.mp h)
  have hc := (gcd_mul_iff n 2 5).2
    ⟨gcd_prime_eq_one 2 (Nat.prime_def.mp Nat.prime_two) n h2, gcd_prime_eq_one 5 (Nat.prime_def.mp (by decide : Nat.Prime 5)) n h5⟩
  norm_num only at hc
  exact exists_repunit n hn ((gcd_eq_one_comm n 10).1 hc)

end ElementaryNumberTheory.Chapter06
