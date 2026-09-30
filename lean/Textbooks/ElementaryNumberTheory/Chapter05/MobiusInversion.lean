import Textbooks.ElementaryNumberTheory.Chapter05.Mobius
import Mathlib.NumberTheory.ArithmeticFunction.Zeta

namespace ElementaryNumberTheory.Chapter05

/-- Definition: extend a function on positive integers by zero. -/
def arithmeticFunction (f : ℕ → ℤ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 0 then 0 else f n, by rfl⟩

/-- Lemma: extension preserves positive arguments. -/
theorem arithmeticFunction_apply (f : ℕ → ℤ) (n : ℕ) (hn : 0 < n) :
    arithmeticFunction f n = f n := by

  exact ite_eq_right (ne_of_gt hn)

/-- Lemma: convolution with zeta is the divisor sum. -/
theorem arithmeticFunction_divisorSum (f : ℕ → ℤ) :
    arithmeticFunction (divisorSum f) = arithmeticFunction f * ArithmeticFunction.zeta := by
  ext n
  by_cases hn : n = 0

  · subst n
    exact (arithmeticFunction (divisorSum f)).map_zero.trans
      (arithmeticFunction f * ArithmeticFunction.zeta).map_zero.symm

  · rw [arithmeticFunction_apply _ n (Nat.pos_of_ne_zero hn), divisorSum,
      ArithmeticFunction.coe_mul_zeta_apply]

    apply Finset.sum_congr rfl
    intro d hd
    exact (arithmeticFunction_apply f d (Nat.pos_of_mem_divisors hd)).symm

/-- Lemma: the proved cancellation identity makes Möbius the convolution inverse of zeta. -/
theorem mobius_mul_zeta :
    arithmeticFunction mobius * ArithmeticFunction.zeta = 1 := by
  rw [← arithmeticFunction_divisorSum]
  ext n
  by_cases hn : n = 0

  · subst n
    simp only [ArithmeticFunction.map_zero]

  · rw [arithmeticFunction_apply _ n (Nat.pos_of_ne_zero hn),
      sum_mobius n (Nat.pos_of_ne_zero hn), ArithmeticFunction.one_apply]

/-- Lemma: convolution expands as a sum indexed by divisors. -/
theorem convolution_apply (f g : ℕ → ℤ) (n : ℕ) (hn : 0 < n) :
    (arithmeticFunction f * arithmeticFunction g) n =
      ∑ d ∈ n.divisors, f d * g (n / d) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y => arithmeticFunction f x * arithmeticFunction g y)]

  apply Finset.sum_congr rfl
  intro d hd

  have hdpos := Nat.pos_of_mem_divisors hd

  have hdiv := Nat.dvd_of_mem_divisors hd

  have hquot : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdiv) hdpos

  rw [arithmeticFunction_apply f d hdpos, arithmeticFunction_apply g (n / d) hquot]

/-- Theorem: Möbius inversion recovers a function from its divisor sums. -/
theorem mobius_inversion (f F : ℕ → ℤ)
    (hF : ∀ n : ℕ, 0 < n → F n = divisorSum f n) (n : ℕ) (hn : 0 < n) :
    f n = ∑ d ∈ n.divisors, mobius d * F (n / d) := by
  have hF' : arithmeticFunction F = arithmeticFunction (divisorSum f) := by
    ext k
    by_cases hk : k = 0

    · subst k
      rfl

    · rw [arithmeticFunction_apply _ k (Nat.pos_of_ne_zero hk),
        arithmeticFunction_apply _ k (Nat.pos_of_ne_zero hk), hF k (Nat.pos_of_ne_zero hk)]

  have hconv : arithmeticFunction mobius * arithmeticFunction F = arithmeticFunction f := by
    rw [hF', arithmeticFunction_divisorSum, mul_left_comm, mobius_mul_zeta, mul_one]

  have h := congrArg (fun g : ArithmeticFunction ℤ => g n) hconv
  rw [convolution_apply _ _ n hn, arithmeticFunction_apply f n hn] at h

  exact h.symm

/-- Theorem: the equivalent inversion formula puts Möbius on the complementary divisor. -/
theorem mobius_inversion' (f F : ℕ → ℤ)
    (hF : ∀ n : ℕ, 0 < n → F n = divisorSum f n) (n : ℕ) (hn : 0 < n) :
    f n = ∑ d ∈ n.divisors, mobius (n / d) * F d := by
  rw [mobius_inversion f F hF n hn, ← convolution_apply _ _ n hn, mul_comm,
    convolution_apply _ _ n hn]

  apply Finset.sum_congr rfl
  intro d hd
  exact mul_comm _ _

/-- Lemma: convolution preserves Burton multiplicativity. -/
theorem convolution_multiplicative (f g : ℕ → ℤ)
    (hf : IsMultiplicative f) (hg : IsMultiplicative g) :
    IsMultiplicative (fun n => ∑ d ∈ n.divisors, f d * g (n / d)) := by
  intro m n hm hn hcop

  have hsum := sum_divisors_mul (fun d => f d * g (m * n / d)) m n hm hn hcop
  change (∑ d ∈ (m * n).divisors, f d * g (m * n / d)) = _ at hsum
  dsimp only
  rw [hsum, Finset.sum_mul_sum]

  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb

  have had := Nat.dvd_of_mem_divisors ha

  have hbd := Nat.dvd_of_mem_divisors hb

  have hap := Nat.pos_of_mem_divisors ha

  have hbp := Nat.pos_of_mem_divisors hb

  have hmap : 0 < m / a := Nat.div_pos (Nat.le_of_dvd hm had) hap

  have hnbp : 0 < n / b := Nat.div_pos (Nat.le_of_dvd hn hbd) hbp

  have hquot : m * n / (a * b) = (m / a) * (n / b) := by
    obtain ⟨u, hu⟩ := had
    obtain ⟨v, hv⟩ := hbd
    rw [hu, hv, Nat.mul_div_cancel_left _ hap, Nat.mul_div_cancel_left _ hbp]
    rw [show a * u * (b * v) = a * b * (u * v) by ring,
      Nat.mul_div_cancel_left _ (mul_pos hap hbp)]

  rw [hf a b hap hbp (gcd_divisors_eq_one m n a b hm hn hcop had hbd), hquot,
    hg (m / a) (n / b) hmap hnbp (gcd_divisors_eq_one m n _ _ hm hn hcop
      (Nat.div_dvd_of_dvd had) (Nat.div_dvd_of_dvd hbd))]
  ring

/-- Theorem: multiplicativity of a divisor sum implies multiplicativity of its source. -/
theorem multiplicative_of_divisorSum (f : ℕ → ℤ)
    (hf : IsMultiplicative (divisorSum f)) : IsMultiplicative f := by
  have hconv := convolution_multiplicative mobius (divisorSum f) mobius_multiplicative hf

  intro m n hm hn hcop

  have hh := hconv m n hm hn hcop
  dsimp only at hh

  rw [mobius_inversion f (divisorSum f) (fun _ _ => rfl) (m * n) (mul_pos hm hn),
    hh,
    ← mobius_inversion f (divisorSum f) (fun _ _ => rfl) m hm,
    ← mobius_inversion f (divisorSum f) (fun _ _ => rfl) n hn]

/-- Corollary: divisor summation preserves and reflects multiplicativity. -/
theorem multiplicative_iff_divisorSum (f : ℕ → ℤ) :
    IsMultiplicative f ↔ IsMultiplicative (divisorSum f) :=
  ⟨divisorSum_multiplicative f, multiplicative_of_divisorSum f⟩

end ElementaryNumberTheory.Chapter05
