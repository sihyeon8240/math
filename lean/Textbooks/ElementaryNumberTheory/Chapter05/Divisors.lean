import Textbooks.ElementaryNumberTheory.Chapter02.PrimeFactorization
import Textbooks.ElementaryNumberTheory.Chapter03.ChineseRemainder
import Mathlib.NumberTheory.Divisors

namespace ElementaryNumberTheory.Chapter05

/-- Definition: the number of positive divisors. The value at zero follows Mathlib's
empty-divisor convention; the lecture statements assume n positive. -/
def tau (n : ℕ) : ℕ := n.divisors.card

/-- Definition: the sum of positive divisors. -/
def sigma (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- Definition: Burton multiplicativity permits the zero function. Only positive arguments are
constrained, and f(1)=1 is not part of the definition. -/
def IsMultiplicative (f : ℕ → ℤ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → Chapter01.gcd m n = 1 → f (m * n) = f m * f n

/-- Definition: the divisor sum of an arithmetic function. -/
def divisorSum (f : ℕ → ℤ) (n : ℕ) : ℤ := ∑ d ∈ n.divisors, f d

/-- Lemma: coprimality is inherited by divisors. -/
theorem gcd_divisors_eq_one (m n a b : ℕ) (hm : 0 < m) (_hn : 0 < n)
    (hcop : Chapter01.gcd m n = 1) (ha : a ∣ m) (hb : b ∣ n) :
    Chapter01.gcd a b = 1 := by
  have hmz : (m : ℤ) ≠ 0 := by omega

  obtain ⟨u, v, huv⟩ :=
    (Chapter01.gcd_eq_one_iff_exists_mul_add_mul m n (Or.inl hmz)).1 hcop

  obtain ⟨r, hr⟩ := ha
  obtain ⟨s, hs⟩ := hb

  have haz : (a : ℤ) ≠ 0 := by
    have : 0 < a := by nlinarith
    omega

  apply (Chapter01.gcd_eq_one_iff_exists_mul_add_mul a b (Or.inl haz)).2
  refine ⟨(r : ℤ) * u, (s : ℤ) * v, ?_⟩
  rw [hr, hs, Nat.cast_mul, Nat.cast_mul] at huv
  nlinarith [huv]

/-- Lemma: a divisor of a product splits into divisors of the factors. Existence follows by
allocating the locally constructed prime factors. -/
theorem exists_divisor_split (m n d : ℕ) (hd : 0 < d) (h : d ∣ m * n) :
    ∃ a b : ℕ, a ∣ m ∧ b ∣ n ∧ a * b = d := by
  obtain ⟨l, hl, hprod⟩ := Chapter02.exists_prime_factors d hd
  rw [← hprod] at h ⊢
  clear hprod hd d
  induction l generalizing m n with
  | nil => exact ⟨1, 1, ⟨m, by ring⟩, ⟨n, by ring⟩, rfl⟩

  | cons p l ih =>
    have hp := hl p List.mem_cons_self

    have hpl : p * l.prod ∣ m * n := h

    have hpdiv : p ∣ m * n := by
      obtain ⟨k, hk⟩ := hpl

      exact ⟨l.prod * k, by
          rw [hk]
          ring⟩

    have hpne : p ≠ 0 := by
      have := hp.1
      omega

    have htail := fun q hq => hl q (List.mem_cons_of_mem p hq)
    rcases Chapter02.prime_dvd_mul_nat p m n hp hpdiv with hpm | hpn

    · obtain ⟨t, ht⟩ := hpm

      have hrest : l.prod ∣ t * n := by
        obtain ⟨k, hk⟩ := hpl

        refine ⟨k, ?_⟩
        apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpne)
        rw [ht] at hk
        nlinarith [hk]

      obtain ⟨a, b, ⟨r, hr⟩, hb, hab⟩ := ih t n hrest htail

      exact ⟨p * a, b, ⟨r, by rw [ht, hr]; ring⟩, hb, by
        change p * a * b = p * l.prod
        rw [← hab]
        ring⟩

    · obtain ⟨t, ht⟩ := hpn

      have hrest : l.prod ∣ m * t := by
        obtain ⟨k, hk⟩ := hpl

        refine ⟨k, ?_⟩
        apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpne)
        rw [ht] at hk
        nlinarith [hk]

      obtain ⟨a, b, ha, ⟨r, hr⟩, hab⟩ := ih m t hrest htail

      exact ⟨a, p * b, ha, ⟨r, by rw [ht, hr]; ring⟩, by
        change a * (p * b) = p * l.prod
        rw [← hab]
        ring⟩

/-- Lemma: divisors of coprime factors determine their product uniquely. -/
theorem divisor_pair_injective (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hcop : Chapter01.gcd m n = 1) (a b c d : ℕ)
    (ha : a ∣ m) (hb : b ∣ n) (hc : c ∣ m) (hd : d ∣ n)
    (heq : a * b = c * d) : a = c ∧ b = d := by
  have hac : a ∣ c := by
    apply Int.natCast_dvd_natCast.mp
    apply Chapter01.dvd_of_dvd_mul_of_coprime a d c
      (gcd_divisors_eq_one m n a d hm hn hcop ha hd)

    refine ⟨b, ?_⟩
    exact_mod_cast (show d * c = a * b by nlinarith [heq])

  have hca : c ∣ a := by
    apply Int.natCast_dvd_natCast.mp
    apply Chapter01.dvd_of_dvd_mul_of_coprime c b a
      (gcd_divisors_eq_one m n c b hm hn hcop hc hb)

    refine ⟨d, ?_⟩
    exact_mod_cast (show b * a = c * d by nlinarith [heq])

  have hac' : a = c := Nat.dvd_antisymm hac hca

  refine ⟨hac', ?_⟩

  have hapos : 0 < a := by
    obtain ⟨k, hk⟩ := ha
    nlinarith
  rw [← hac'] at heq
  exact Nat.eq_of_mul_eq_mul_left hapos heq

/-- Theorem: every divisor of a coprime product has a unique factor split. -/
theorem existsUnique_divisor_split (m n d : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hcop : Chapter01.gcd m n = 1) (hd : d ∈ (m * n).divisors) :
    ∃! ab : ℕ × ℕ, ab.1 ∣ m ∧ ab.2 ∣ n ∧ ab.1 * ab.2 = d := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_divisor_split m n d
    (Nat.pos_of_mem_divisors hd) (Nat.dvd_of_mem_divisors hd)

  refine ⟨(a, b), ⟨ha, hb, hab⟩, ?_⟩
  rintro ⟨c, e⟩ ⟨hc, he, hce⟩

  obtain ⟨hca, heb⟩ := divisor_pair_injective m n hm hn hcop c e a b hc he ha hb
    (hce.trans hab.symm)

  exact Prod.ext hca heb

/-- Theorem: a nonzero multiplicative function takes the value one at one. -/
theorem multiplicative_one (f : ℕ → ℤ) (hf : IsMultiplicative f)
    (hne : ∃ n : ℕ, 0 < n ∧ f n ≠ 0) : f 1 = 1 := by
  obtain ⟨n, hn, hfn⟩ := hne

  have hcop : Chapter01.gcd 1 n = 1 :=
    (Chapter01.gcd_eq_one_iff_exists_mul_add_mul 1 n (Or.inl (by decide))).2
      ⟨1, 0, by ring⟩

  have h := hf 1 n (by decide) hn hcop
  rw [one_mul] at h
  exact mul_right_cancel₀ hfn ((one_mul (f n)).trans h).symm

/-- Lemma: sums over divisors of a coprime product split into a double sum. -/
theorem sum_divisors_mul (f : ℕ → ℤ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hcop : Chapter01.gcd m n = 1) :
    divisorSum f (m * n) = ∑ a ∈ m.divisors, ∑ b ∈ n.divisors, f (a * b) := by
  classical
  rw [divisorSum, ← Finset.sum_product' ]
  symm
  apply Finset.sum_bij (fun ab _ => ab.1 * ab.2)

  · intro ab hab

    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab

    exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul (Nat.dvd_of_mem_divisors ha)
      (Nat.dvd_of_mem_divisors hb), ne_of_gt (mul_pos hm hn)⟩

  · intro ab hab cd hcd heq

    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hc, hd⟩ := Finset.mem_product.mp hcd
    obtain ⟨h₁, h₂⟩ := divisor_pair_injective m n hm hn hcop ab.1 ab.2 cd.1 cd.2
      (Nat.dvd_of_mem_divisors ha) (Nat.dvd_of_mem_divisors hb)
      (Nat.dvd_of_mem_divisors hc) (Nat.dvd_of_mem_divisors hd) heq

    exact Prod.ext h₁ h₂

  · intro d hd

    obtain ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, _⟩ := existsUnique_divisor_split m n d hm hn hcop hd

    exact ⟨(a, b), Finset.mem_product.mpr
      ⟨Nat.mem_divisors.mpr ⟨ha, ne_of_gt hm⟩, Nat.mem_divisors.mpr ⟨hb, ne_of_gt hn⟩⟩, hab⟩

  · intro ab hab
    rfl

/-- Theorem: taking divisor sums preserves multiplicativity. -/
theorem divisorSum_multiplicative (f : ℕ → ℤ) (hf : IsMultiplicative f) :
    IsMultiplicative (divisorSum f) := by
  intro m n hm hn hcop
  rw [sum_divisors_mul f m n hm hn hcop, divisorSum, divisorSum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact hf a b (Nat.pos_of_mem_divisors ha) (Nat.pos_of_mem_divisors hb)
    (gcd_divisors_eq_one m n a b hm hn hcop (Nat.dvd_of_mem_divisors ha)
      (Nat.dvd_of_mem_divisors hb))

/-- Theorem: the number-of-divisors function is multiplicative. -/
theorem tau_multiplicative : IsMultiplicative (fun n => (tau n : ℤ)) := by
  have hh := divisorSum_multiplicative (fun _ => 1) (by
    intro m n hm hn hcop
    ring)
  simpa only [IsMultiplicative, divisorSum, Finset.sum_const, nsmul_eq_mul, mul_one, tau] using hh

/-- Theorem: the sum-of-divisors function is multiplicative. -/
theorem sigma_multiplicative : IsMultiplicative (fun n => (sigma n : ℤ)) := by
  have hh := divisorSum_multiplicative (fun n => (n : ℤ)) (by
    intro m n hm hn hcop
    exact Nat.cast_mul m n)
  simpa only [IsMultiplicative, divisorSum, sigma, Nat.cast_sum] using hh

/-- Theorem: the divisor functions both take value one at one. -/
theorem tau_sigma_one : tau 1 = 1 ∧ sigma 1 = 1 := by
  simp only [tau, sigma, Nat.divisors_one, Finset.card_singleton, Finset.sum_singleton, and_self]

end ElementaryNumberTheory.Chapter05
