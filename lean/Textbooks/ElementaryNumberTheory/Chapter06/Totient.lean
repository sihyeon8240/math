import Textbooks.ElementaryNumberTheory.Chapter05.MobiusInversion
import Mathlib.Data.Nat.Totient
import Textbooks.ElementaryNumberTheory.Chapter01.EuclideanAlgorithm

namespace ElementaryNumberTheory.Chapter06

open Chapter05

/-- Lemma: the elementary common-divisor characterization converts local coprimality. -/
theorem coprime_iff_gcd_eq_one (m n : ℕ) (hm : 0 < m) :
    m.Coprime n ↔ Chapter01.gcd m n = 1 := by
  have hz : (m : ℤ) ≠ 0 := by
    omega
  obtain ⟨_, ha, hb, _, hc⟩ := Chapter01.gcd_spec m n (Or.inl hz)
  constructor

  · intro h
    have hd := Nat.dvd_gcd (Int.natCast_dvd_natCast.mp ha)
      (Int.natCast_dvd_natCast.mp hb)
    rw [h] at hd
    exact Nat.eq_one_of_dvd_one hd

  · intro h
    apply Nat.coprime_iff_gcd_eq_one.mpr
    have hd := hc (Nat.gcd m n)
      (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left m n))
      (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right m n))
    rw [h, Nat.cast_one] at hd
    exact Nat.eq_one_of_dvd_one (Int.natCast_dvd_natCast.mp hd)

/-- Definition: the reduced nonnegative representatives modulo n. At n=1 the representative
is zero; its class is the same as the positive representative one used in the notes. -/
def reducedResidues (n : ℕ) : Finset ℕ := (Finset.range n).filter (Nat.Coprime n)

/-- Theorem: the standard phi-function also counts positive representatives up to n. -/
theorem totient_eq_card_Icc (n : ℕ) (hn : 0 < n) :
    Nat.totient n = ((Finset.Icc 1 n).filter (Nat.Coprime n)).card := by
  by_cases he : n = 1

  · subst n
    decide

  · have hset : reducedResidues n = (Finset.Icc 1 n).filter (Nat.Coprime n) := by
      ext a
      simp only [reducedResidues, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      constructor

      · rintro ⟨hlt, hc⟩
        have hne : a ≠ 0 := by
          intro h
          subst a
          simp only [Nat.coprime_zero_right] at hc
          exact he hc
        exact ⟨⟨by omega, le_of_lt hlt⟩, hc⟩

      · rintro ⟨⟨hpos, hle⟩, hc⟩
        have hne : a ≠ n := by
          intro h
          subst a
          simp only [Nat.coprime_self] at hc
          exact he hc
        exact ⟨lt_of_le_of_ne hle hne, hc⟩

    change (reducedResidues n).card = _
    rw [hset]

/-- Lemma: every positive modulus has a reduced class. -/
theorem totient_pos (n : ℕ) (hn : 0 < n) : 0 < Nat.totient n := by
  by_cases h : n = 1
  · subst n
    exact Nat.zero_lt_one
  · apply Finset.card_pos.mpr
    refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
    exact Nat.coprime_one_right n

/-- Lemma: scaling natural inputs reuses the locally proved integer gcd scaling law. -/
theorem gcd_nat_mul (d a b : ℕ) (hd : 0 < d) :
    Chapter01.gcd (d * a : ℕ) (d * b : ℕ) = d * Chapter01.gcd a b := by
  have h := Chapter01.gcd_mul_of_pos a b d (by exact_mod_cast hd)
  simpa only [← Nat.cast_mul, Int.natCast_inj] using h

/-- Lemma: scaling coprime representatives counts each gcd fiber. -/
theorem card_gcd_fiber (n d : ℕ) (hn : 0 < n) (hd : d ∣ n) :
    ((Finset.range n).filter (fun k : ℕ => Chapter01.gcd n k = d)).card =
      Nat.totient (n / d) := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hn
  obtain ⟨q, rfl⟩ := hd
  have hqpos : 0 < q := by nlinarith [hn]
  rw [Nat.mul_div_cancel_left q hdpos, Nat.totient]
  symm
  apply Finset.card_bij (fun k _ => d * k)

  · intro k hk
    obtain ⟨hk, hc⟩ := Finset.mem_filter.mp hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · exact Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp hk) hdpos
    · rw [gcd_nat_mul d q k hdpos, (coprime_iff_gcd_eq_one q k hqpos).1 hc, mul_one]

  · intro k hk l hl he
    exact Nat.eq_of_mul_eq_mul_left hdpos he

  · intro k hk
    obtain ⟨hk, hg⟩ := Finset.mem_filter.mp hk
    have hdk : d ∣ k := by
      have h := (Chapter01.gcd_spec (d * q : ℕ) k (Or.inl (by omega))).2.2.1
      rw [hg] at h
      exact Int.natCast_dvd_natCast.mp h
    obtain ⟨r, rfl⟩ := hdk
    refine ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩, rfl⟩
    · exact (Nat.mul_lt_mul_left hdpos).mp (Finset.mem_range.mp hk)
    · apply (coprime_iff_gcd_eq_one q r hqpos).2
      rw [gcd_nat_mul d q r hdpos] at hg
      exact Nat.eq_of_mul_eq_mul_left hdpos (hg.trans (mul_one d).symm)

/-- Theorem: partitioning residues by their gcd gives Gauss's divisor sum. -/
theorem sum_totient (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, Nat.totient d) = n := by
  have hpartition : n = ∑ d ∈ n.divisors,
      ((Finset.range n).filter (fun k : ℕ => Chapter01.gcd n k = d)).card := by
    nth_rw 1 [← Finset.card_range n]
    apply Finset.card_eq_sum_card_fiberwise
    intro k hk
    exact Nat.mem_divisors.mpr
      ⟨Int.natCast_dvd_natCast.mp
        (Chapter01.gcd_spec n k (Or.inl (by omega))).2.1, ne_of_gt hn⟩

  rw [← Nat.sum_div_divisors]
  calc
    (∑ d ∈ n.divisors, Nat.totient (n / d)) =
        ∑ d ∈ n.divisors, ((Finset.range n).filter (fun k : ℕ => Chapter01.gcd n k = d)).card := by
      apply Finset.sum_congr rfl
      intro d hd
      exact (card_gcd_fiber n d hn (Nat.dvd_of_mem_divisors hd)).symm
    _ = n := hpartition.symm

/-- Theorem: Euler's phi-function is multiplicative. -/
theorem totient_multiplicative : IsMultiplicative (fun n => (Nat.totient n : ℤ)) := by
  apply multiplicative_of_divisorSum
  intro m n hm hn hcop
  have hsum (k : ℕ) (hk : 0 < k) :
      divisorSum (fun d => (Nat.totient d : ℤ)) k = k := by
    simpa only [divisorSum, ← Nat.cast_sum] using
    congrArg (fun z : ℕ => (z : ℤ)) (sum_totient k hk)

  rw [hsum (m * n) (mul_pos hm hn), hsum m hm, hsum n hn, Nat.cast_mul]

/-- Theorem: phi of a coprime product is the product of the phi-values. -/
theorem totient_mul (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hcop : Chapter01.gcd m n = 1) :
    Nat.totient (m * n) = Nat.totient m * Nat.totient n := by
  have h := totient_multiplicative m n hm hn hcop
  dsimp only at h
  exact_mod_cast h

/-- Theorem: phi of a positive prime power counts the nonmultiples of the prime. -/
theorem totient_prime_pow_succ (p k : ℕ) (hp : Chapter02.isPrime p) :
    Nat.totient (p ^ (k + 1)) = p ^ k * (p - 1) := by
  have hpos : 0 < p := by
    have := hp.1
    omega
  have hinj : Function.Injective (fun j : ℕ => p ^ j) :=
    pow_right_injective₀ hpos (by
      have := hp.1
      omega)
  have hsum (r : ℕ) : (∑ j ∈ Finset.range (r + 1), Nat.totient (p ^ j)) = p ^ r := by
    have h := sum_totient (p ^ r) (pow_pos hpos r)
    rw [divisors_prime_pow p r hp, Finset.sum_image] at h
    · exact h
    · intro i hi j hj he
      exact hinj he

  have h := hsum (k + 1)
  rw [Finset.sum_range_succ, hsum k] at h
  rw [pow_succ] at h ⊢
  have hp1 : p - 1 + 1 = p := by
    have := hp.1
    omega
  nlinarith [congrArg (fun z => p ^ k * z) hp1]

/-- Corollary: phi of a prime power is the difference of two successive powers. -/
theorem totient_prime_pow (p k : ℕ) (hp : Chapter02.isPrime p) (hk : 0 < k) :
    Nat.totient (p ^ k) = p ^ k - p ^ (k - 1) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
  rw [totient_prime_pow_succ p r hp, Nat.succ_sub_one, pow_succ]
  rw [Nat.mul_sub_left_distrib, mul_one]

/-- Corollary: phi of a prime is one less than the prime. -/
theorem totient_prime (p : ℕ) (hp : Chapter02.isPrime p) : Nat.totient p = p - 1 := by
  simpa only [Nat.zero_add, pow_one, pow_zero, one_mul] using totient_prime_pow_succ p 0 hp

/-- Theorem: the prime-power product formula for phi. -/
theorem totient_eq_prod (n : ℕ) (hn : 1 < n) :
    (Nat.totient n : ℤ) = ∏ p ∈ (primeExponents n).support,
      ((p ^ primeExponents n p - p ^ (primeExponents n p - 1) : ℕ) : ℤ) := by
  rw [multiplicative_prime_powers _ totient_multiplicative n hn]
  apply Finset.prod_congr rfl
  intro p hp
  rw [totient_prime_pow p _ ((primeExponents_spec n (by omega)).1 p hp)
    (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp))]

/-- Theorem: Möbius inversion expresses phi as a weighted complementary-divisor sum. -/
theorem totient_eq_sum_mobius (n : ℕ) (hn : 0 < n) :
    (Nat.totient n : ℤ) = ∑ d ∈ n.divisors, mobius d * (n / d : ℕ) := by
  apply mobius_inversion (fun d => (Nat.totient d : ℤ)) (fun k => (k : ℤ)) _ n hn
  intro k hk
  symm
  simpa only [divisorSum, ← Nat.cast_sum] using
    congrArg (fun z : ℕ => (z : ℤ)) (sum_totient k hk)

end ElementaryNumberTheory.Chapter06
