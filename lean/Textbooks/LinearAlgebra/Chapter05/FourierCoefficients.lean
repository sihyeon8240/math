import Textbooks.LinearAlgebra.Chapter05.IntegralProducts

namespace LinearAlgebra.Chapter05

open Real

/-- Lemma: the integral of an integer-frequency cosine on a full period. -/
theorem integral_cos_int (k : ℤ) :
    (∫ x in -π..π, cos (k * x)) = if k = 0 then 2 * π else 0 := by
  by_cases hk : k = 0

  · subst k
    simp only [Int.cast_zero, zero_mul, cos_zero, intervalIntegral.integral_const,
      sub_neg_eq_add, smul_eq_mul, mul_one, ↓reduceIte]
    ring

  · rw [ite_eq_right hk, intervalIntegral.integral_comp_mul_left (fun x => cos x)
      (Int.cast_ne_zero.mpr hk), integral_cos]
    simp only [mul_neg, sin_neg, sin_int_mul_pi, sub_zero, neg_zero, smul_zero]

/-- Lemma: every integer-frequency sine has integral zero on a full period. -/
theorem integral_sin_int (k : ℤ) : (∫ x in -π..π, sin (k * x)) = 0 := by
  by_cases hk : k = 0

  · subst k
    simp only [Int.cast_zero, zero_mul, sin_zero, intervalIntegral.integral_zero]

  · rw [intervalIntegral.integral_comp_mul_left (fun x => sin x)
      (Int.cast_ne_zero.mpr hk), integral_sin]
    simp only [mul_neg, cos_neg, sub_self, smul_zero]

/-- Proposition: distinct positive cosine frequencies are perpendicular, with square integral `π`.
-/
theorem integral_cos_cos (k l : ℤ) (hk : 0 < k) (hl : 0 < l) :
    (∫ x in -π..π, cos (k * x) * cos (l * x)) = if k = l then π else 0 := by
  have he : 2 * (∫ x in -π..π, cos (k * x) * cos (l * x)) =
      (∫ x in -π..π, cos (((k - l : ℤ) : ℝ) * x)) + ∫ x in -π..π, cos (((k + l : ℤ) : ℝ) * x) := by
    rw [← intervalIntegral.integral_const_mul]
    have h (x : ℝ) : 2 * (cos (k * x) * cos (l * x)) =
        cos (((k - l : ℤ) : ℝ) * x) + cos (((k + l : ℤ) : ℝ) * x) := by
      rw [← mul_assoc, two_mul_cos_mul_cos, Int.cast_sub, Int.cast_add, sub_mul, add_mul]
    simp_rw [h]
    apply intervalIntegral.integral_add <;>
      apply Continuous.intervalIntegrable <;>
      fun_prop

  rw [integral_cos_int, integral_cos_int] at he
  have hsum : k + l ≠ 0 := by
    omega
  rw [ite_eq_right hsum] at he
  by_cases hkl : k = l

  · simp only [hkl, sub_self, ↓reduceIte, add_zero] at he ⊢
    linarith

  · simp only [sub_eq_zero, ite_eq_right hkl, add_zero] at he ⊢
    linarith

/-- Proposition: distinct positive sine frequencies are perpendicular, with square integral `π`. -/
theorem integral_sin_sin (k l : ℤ) (hk : 0 < k) (hl : 0 < l) :
    (∫ x in -π..π, sin (k * x) * sin (l * x)) = if k = l then π else 0 := by
  have he : 2 * (∫ x in -π..π, sin (k * x) * sin (l * x)) =
      (∫ x in -π..π, cos (((k - l : ℤ) : ℝ) * x)) - ∫ x in -π..π, cos (((k + l : ℤ) : ℝ) * x) := by
    rw [← intervalIntegral.integral_const_mul]
    have h (x : ℝ) : 2 * (sin (k * x) * sin (l * x)) =
        cos (((k - l : ℤ) : ℝ) * x) - cos (((k + l : ℤ) : ℝ) * x) := by
      rw [← mul_assoc, two_mul_sin_mul_sin, Int.cast_sub, Int.cast_add, sub_mul, add_mul]
    simp_rw [h]
    apply intervalIntegral.integral_sub <;>
      apply Continuous.intervalIntegrable <;>
      fun_prop

  rw [integral_cos_int, integral_cos_int] at he
  have hsum : k + l ≠ 0 := by
    omega
  rw [ite_eq_right hsum] at he
  by_cases hkl : k = l

  · simp only [hkl, sub_self, ↓reduceIte, sub_zero] at he ⊢
    linarith

  · simp only [sub_eq_zero, ite_eq_right hkl, sub_zero] at he ⊢
    linarith

/-- Proposition: sine and cosine frequencies are perpendicular. -/
theorem integral_sin_cos (k l : ℤ) :
    (∫ x in -π..π, sin (k * x) * cos (l * x)) = 0 := by
  have he : 2 * (∫ x in -π..π, sin (k * x) * cos (l * x)) =
      (∫ x in -π..π, sin (((k - l : ℤ) : ℝ) * x)) + ∫ x in -π..π, sin (((k + l : ℤ) : ℝ) * x) := by
    rw [← intervalIntegral.integral_const_mul]
    have h (x : ℝ) : 2 * (sin (k * x) * cos (l * x)) =
        sin (((k - l : ℤ) : ℝ) * x) + sin (((k + l : ℤ) : ℝ) * x) := by
      rw [← mul_assoc, two_mul_sin_mul_cos, Int.cast_sub, Int.cast_add, sub_mul, add_mul]
    simp_rw [h]
    apply intervalIntegral.integral_add <;>
      apply Continuous.intervalIntegrable <;>
      fun_prop

  rw [integral_sin_int, integral_sin_int] at he
  linarith

/-- Proposition: the constant function `1/2` has squared integral `π/2`. -/
theorem integral_half_square : (∫ _ in -π..π, (1 / 2 : ℝ) * (1 / 2)) = π / 2 := by
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- Lemma: the integer-frequency complex exponential has integral zero except at zero frequency. -/
theorem integral_exp_int (k : ℤ) :
    (∫ x in -π..π, Complex.exp (((k * x : ℝ) : ℂ) * Complex.I)) =
      if k = 0 then (2 * π : ℂ) else 0 := by
  have he (x : ℝ) : Complex.exp (((k * x : ℝ) : ℂ) * Complex.I) =
      (cos (k * x) : ℂ) + Complex.I * (sin (k * x) : ℂ) := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
    integral_cos_int, integral_sin_int]

  · split_ifs <;> simp only [Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_zero, mul_zero, add_zero]
  all_goals
    apply Continuous.intervalIntegrable
    fun_prop

/-- Proposition: the complex exponentials are perpendicular, with squared integral `2π`. -/
theorem integral_exp_inner (k l : ℤ) :
    (∫ x in -π..π,
      star (Complex.exp (((k * x : ℝ) : ℂ) * Complex.I)) *
        Complex.exp (((l * x : ℝ) : ℂ) * Complex.I)) =
      if k = l then (2 * π : ℂ) else 0 := by
  have he (x : ℝ) :
      star (Complex.exp (((k * x : ℝ) : ℂ) * Complex.I)) *
        Complex.exp (((l * x : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((((l - k : ℤ) : ℝ) * x : ℝ) * Complex.I) := by
    rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
      Complex.conj_I, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [he]
  rw [integral_exp_int]
  simp only [sub_eq_zero, eq_comm]

/-- Definition: the real cosine coefficient, with the constant term represented by `a₀/2`. -/
noncomputable def fourierCosCoefficient (g : C(ℝ, ℝ)) (k : ℕ) : ℝ :=
  (∫ x in -π..π, g x * cos (k * x)) / π

/-- Definition: the real sine coefficient. -/
noncomputable def fourierSinCoefficient (g : C(ℝ, ℝ)) (k : ℕ) : ℝ :=
  (∫ x in -π..π, g x * sin (k * x)) / π

/-- Definition: the complex coefficient of the exponential with integer frequency. -/
noncomputable def fourierComplexCoefficient (g : C(ℝ, ℂ)) (k : ℤ) : ℂ :=
  (∫ x in -π..π, g x * Complex.exp (-(k * x) * Complex.I)) / (2 * π)

/-- Proposition: the cosine coefficient is the component along its positive-frequency cosine. -/
theorem cosine_component (g : C(ℝ, ℝ)) (k : ℕ) (hk : 0 < k) :
    (∫ x in -π..π, g x * cos (k * x)) /
      (∫ x in -π..π, cos (k * x) * cos (k * x)) = fourierCosCoefficient g k := by
  rw [← Int.cast_natCast k, integral_cos_cos (k : ℤ) k (by omega) (by omega), ite_eq_left rfl]
  rfl

/-- Proposition: the sine coefficient is the component along its positive-frequency sine. -/
theorem sine_component (g : C(ℝ, ℝ)) (k : ℕ) (hk : 0 < k) :
    (∫ x in -π..π, g x * sin (k * x)) /
      (∫ x in -π..π, sin (k * x) * sin (k * x)) = fourierSinCoefficient g k := by
  rw [← Int.cast_natCast k, integral_sin_sin (k : ℤ) k (by omega) (by omega), ite_eq_left rfl]
  rfl

/-- Lemma: Euler's identity in the real-frequency convention used by the coefficients. -/
theorem exp_neg_mul_I (t : ℝ) :
    Complex.exp (-(t : ℂ) * Complex.I) = (cos t : ℂ) - Complex.I * (sin t : ℂ) := by
  rw [Complex.exp_mul_I]
  simp only [Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos, Complex.ofReal_sin]
  ring

/-- Definition: view a continuous real function as a continuous complex function. -/
def complexify (g : C(ℝ, ℝ)) : C(ℝ, ℂ) :=
  ⟨fun x => (g x : ℂ), Complex.continuous_ofReal.comp g.continuous⟩

/-- Lemma: separate the real and imaginary parts of the Fourier integral. -/
theorem integral_fourier_kernel (g : C(ℝ, ℝ)) (t : ℝ) :
    (∫ x in -π..π, (g x : ℂ) * Complex.exp (-((t * x : ℝ) : ℂ) * Complex.I)) =
      ((∫ x in -π..π, g x * cos (t * x) : ℝ) : ℂ) -
        Complex.I * ((∫ x in -π..π, g x * sin (t * x) : ℝ) : ℂ) := by
  have he (x : ℝ) : (g x : ℂ) * Complex.exp (-((t * x : ℝ) : ℂ) * Complex.I) =
      ((g x * cos (t * x) : ℝ) : ℂ) -
        Complex.I * ((g x * sin (t * x) : ℝ) : ℂ) := by
    rw [exp_neg_mul_I]
    push_cast
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  all_goals
    apply Continuous.intervalIntegrable
    fun_prop

/-- Proposition: the complex coefficient of a real function is `(aₖ - i bₖ)/2`. -/
theorem fourierComplexCoefficient_of_real (g : C(ℝ, ℝ)) (k : ℕ) :
    fourierComplexCoefficient (complexify g) k =
      ((fourierCosCoefficient g k : ℂ) - Complex.I * (fourierSinCoefficient g k : ℂ)) / 2 := by
  unfold fourierComplexCoefficient fourierCosCoefficient fourierSinCoefficient
  change (∫ x in -π..π, (g x : ℂ) *
      Complex.exp (-((k : ℂ) * (x : ℂ)) * Complex.I)) / (2 * π) = _
  simp only [← Complex.ofReal_natCast k, ← Complex.ofReal_mul]
  rw [integral_fourier_kernel]
  push_cast
  field_simp

/-- Proposition: the coefficient at the negative frequency is `(aₖ + i bₖ)/2`. -/
theorem fourierComplexCoefficient_neg_of_real (g : C(ℝ, ℝ)) (k : ℕ) :
    fourierComplexCoefficient (complexify g) (-(k : ℤ)) =
      ((fourierCosCoefficient g k : ℂ) + Complex.I * (fourierSinCoefficient g k : ℂ)) / 2 := by
  unfold fourierComplexCoefficient fourierCosCoefficient fourierSinCoefficient
  simp only [Int.cast_neg, Int.cast_natCast]
  change (∫ x in -π..π, (g x : ℂ) *
      Complex.exp (-((-(k : ℂ)) * (x : ℂ)) * Complex.I)) / (2 * π) = _
  simp only [← Complex.ofReal_natCast k, ← Complex.ofReal_neg, ← Complex.ofReal_mul]
  have he := integral_fourier_kernel g (-(k : ℝ))
  simp only [neg_mul, neg_neg, Complex.ofReal_neg] at he ⊢
  rw [he]
  simp only [cos_neg, sin_neg, mul_neg, intervalIntegral.integral_neg,
    Complex.ofReal_neg, sub_neg_eq_add]
  push_cast
  field_simp

/-- Proposition: the complex coefficient is the component along its exponential. -/
theorem exponential_component (g : C(ℝ, ℂ)) (k : ℤ) :
    (∫ x in -π..π, star (Complex.exp (((k * x : ℝ) : ℂ) * Complex.I)) * g x) /
      (∫ x in -π..π, star (Complex.exp (((k * x : ℝ) : ℂ) * Complex.I)) *
        Complex.exp (((k * x : ℝ) : ℂ) * Complex.I)) = fourierComplexCoefficient g k := by
  rw [integral_exp_inner, ite_eq_left rfl]
  have he (x : ℝ) : star (Complex.exp (((k * x : ℝ) : ℂ) * Complex.I)) * g x =
      g x * Complex.exp (-((k : ℂ) * (x : ℂ)) * Complex.I) := by
    rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
      Complex.conj_I, mul_comm _ (g x)]
    congr 2
    push_cast
    ring
  simp_rw [he]
  rfl

/-- Proposition: the sine coefficient at zero is zero. -/
theorem fourierSinCoefficient_zero (g : C(ℝ, ℝ)) : fourierSinCoefficient g 0 = 0 := by
  simp only [fourierSinCoefficient, Nat.cast_zero, zero_mul, sin_zero, mul_zero,
    intervalIntegral.integral_zero, zero_div]

/-- Proposition: the component along `1/2` is the constant coefficient. -/
theorem constant_component (g : C(ℝ, ℝ)) :
    (∫ x in -π..π, g x * (1 / 2)) / (∫ _ in -π..π, (1 / 2 : ℝ) * (1 / 2)) =
      fourierCosCoefficient g 0 := by
  rw [integral_half_square, intervalIntegral.integral_mul_const]
  simp only [fourierCosCoefficient, Nat.cast_zero, zero_mul, cos_zero, mul_one]
  ring

end LinearAlgebra.Chapter05
