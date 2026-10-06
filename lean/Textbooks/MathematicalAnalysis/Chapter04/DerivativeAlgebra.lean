import Textbooks.MathematicalAnalysis.Chapter04.DerivativeLimits
import Mathlib.Algebra.Polynomial.Derivative

namespace MathematicalAnalysis.Chapter04

open Filter
open scoped Topology
open MathematicalAnalysis.Chapter02 MathematicalAnalysis.Chapter03

/-- Lemma: a constant real function has derivative zero. -/
theorem hasDerivAt_constant (c a : ℝ) : HasDerivAt (fun _ : ℝ => c) 0 a := by
  apply (hasDerivAt_iff_epsilon _ _ _).mpr
  intro ε hε
  refine ⟨1, zero_lt_one, ?_⟩
  intro _ _ _
  simpa only [sub_self, zero_div, sub_zero, abs_zero] using hε

/-- Lemma: the product rule follows by splitting the difference quotient into two terms. -/
theorem hasDerivAt_product (f g : ℝ → ℝ) (df dg a : ℝ)
    (hf : HasDerivAt f df a) (hg : HasDerivAt g dg a) :
    HasDerivAt (fun x => f x * g x) (df * g a + f a * dg) a := by
  apply (hasDerivAt_iff_limit _ _ a).mpr
  apply (punctured_limit_iff_sequences _ a _).mpr
  intro u hu hlim
  have hfl := (punctured_limit_iff_sequences _ a df).mp
    ((hasDerivAt_iff_limit f df a).mp hf) u hu hlim
  have hgl := (punctured_limit_iff_sequences _ a dg).mp
    ((hasDerivAt_iff_limit g dg a).mp hg) u hu hlim
  have hfc := (continuousAt_iff_sequences f a).mp
    (continuousAt_of_hasDerivAt f df a hf) u hlim
  have hsum := real_tendsto_add _ _ _ _
    (real_tendsto_const_mul _ df (g a) hfl) (real_tendsto_mul _ _ _ _ hfc hgl)
  have hvalue : g a * df + f a * dg = df * g a + f a * dg := by ring
  rw [hvalue] at hsum
  convert hsum using 1
  funext n
  dsimp only [Function.comp_def]
  ring

/-- Lemma: the natural-power derivative is proved by induction and the product rule. -/
private theorem hasDerivAt_power (n : ℕ) (a : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ n) ((n : ℝ) * a ^ (n - 1)) a := by
  induction n with
  | zero => simpa only [pow_zero, Nat.cast_zero, zero_mul] using hasDerivAt_constant 1 a
  | succ n ih =>
    have h := hasDerivAt_product (fun x : ℝ => x ^ n) (fun x => x)
      ((n : ℝ) * a ^ (n - 1)) 1 a ih (hasDerivAt_identity a)
    have heq : (n : ℝ) * a ^ (n - 1) * a + a ^ n * 1 =
        ((n + 1 : ℕ) : ℝ) * a ^ ((n + 1) - 1) := by
      cases n with
      | zero => simp only [Nat.cast_zero, zero_mul, zero_add, pow_zero, one_mul,
          Nat.cast_one, Nat.sub_self]
      | succ n =>
        simp only [Nat.add_sub_cancel, Nat.cast_succ, pow_succ]
        ring
    rw [heq] at h
    simpa only [pow_succ] using h

/-- Lemma: evaluation of a real polynomial has the derivative given by its
formal algebraic derivative. -/
theorem hasDerivAt_polynomial (P : Polynomial ℝ) (a : ℝ) :
    HasDerivAt (fun x => P.eval x) (P.derivative.eval a) a := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simpa only [Polynomial.eval_add, Polynomial.derivative_add, one_mul] using
      hasDerivAt_linear_combination (fun x => P.eval x) (fun x => Q.eval x)
        (P.derivative.eval a) (Q.derivative.eval a) 1 1 a hP hQ
  | monomial n c =>
    have h := hasDerivAt_product (fun _ : ℝ => c) (fun x => x ^ n)
      0 ((n : ℝ) * a ^ (n - 1)) a (hasDerivAt_constant c a) (hasDerivAt_power n a)
    simpa only [Polynomial.eval_monomial, Polynomial.derivative_monomial,
      zero_mul, zero_add, mul_assoc] using h

end MathematicalAnalysis.Chapter04
