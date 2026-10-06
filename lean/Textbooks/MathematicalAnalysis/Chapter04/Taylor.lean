import Textbooks.MathematicalAnalysis.Chapter04.DerivativeAlgebra
import Textbooks.MathematicalAnalysis.Chapter04.MeanValue
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

namespace MathematicalAnalysis.Chapter04

open Set Polynomial
open scoped Topology

private theorem repeated_rolle (F : ℕ → ℝ → ℝ) (n : ℕ) (hn : 0 < n)
    (a b : ℝ) (hab : a < b)
    (hc : ∀ k < n, ContinuousOn (F k) (Icc a b))
    (hd : ∀ k < n, ∀ x ∈ Ioo a b, HasDerivAt (F k) (F (k + 1) x) x)
    (ha : F 0 a = 0) (hb : F 0 b = 0)
    (hz : (∀ k < n, F k a = 0) ∨ (∀ k < n, F k b = 0)) :
    ∃ c ∈ Ioo a b, F n c = 0 := by
  induction n generalizing a b F with
  | zero => omega
  | succ n ih =>
    obtain ⟨c, hci, hzero⟩ := rolle (F 0) (F 1) a b hab (hc 0 (by omega))
      (hd 0 (by omega)) (ha.trans hb.symm)

    cases n with
    | zero => exact ⟨c, hci, hzero⟩
    | succ n =>
      rcases hz with hz | hz
      · have hsub : Icc a c ⊆ Icc a b := fun x hx => ⟨hx.1, hx.2.trans hci.2.le⟩
        obtain ⟨d, hdi, hdz⟩ := ih (fun k => F (k + 1)) (by omega) a c hci.1
          (fun k hk => (hc (k + 1) (by omega)).mono hsub)
          (fun k hk x hx => hd (k + 1) (by omega) x ⟨hx.1, hx.2.trans hci.2⟩)
          (hz 1 (by omega)) hzero (Or.inl (fun k hk => hz (k + 1) (by omega)))

        exact ⟨d, ⟨hdi.1, hdi.2.trans hci.2⟩, hdz⟩

      · have hsub : Icc c b ⊆ Icc a b := fun x hx => ⟨hci.1.le.trans hx.1, hx.2⟩
        obtain ⟨d, hdi, hdz⟩ := ih (fun k => F (k + 1)) (by omega) c b hci.2
          (fun k hk => (hc (k + 1) (by omega)).mono hsub)
          (fun k hk x hx => hd (k + 1) (by omega) x ⟨hci.1.trans hx.1, hx.2⟩)
          hzero (hz 1 (by omega)) (Or.inr (fun k hk => hz (k + 1) (by omega)))

        exact ⟨d, ⟨hci.1.trans hdi.1, hdi.2⟩, hdz⟩

private theorem polynomial_shift_derivative (P : Polynomial ℝ) (x t : ℝ) :
    HasDerivAt (fun t => P.eval (t - x)) (P.derivative.eval (t - x)) t := by
  have hshift : HasDerivAt (fun t : ℝ => t - x) 1 t := by
    simpa only [one_mul, neg_one_mul, neg_zero, add_zero, sub_eq_add_neg] using
      hasDerivAt_linear_combination (fun t => t) (fun _ => x) 1 0 1 (-1) t
        (hasDerivAt_identity t) (hasDerivAt_constant x t)

  simpa only [Function.comp_def, mul_one] using
    hasDerivAt_comp (fun t => t - x) (fun t => P.eval t) 1
      (P.derivative.eval (t - x)) t hshift (hasDerivAt_polynomial P (t - x))

private theorem polynomial_iterate_monomial (k n : ℕ) (c t : ℝ) :
    ((derivative^[k]) (monomial n c)).eval t =
      c * (n.descFactorial k : ℝ) * t ^ (n - k) := by
  rw [← C_mul_X_pow_eq_monomial, iterate_derivative_C_mul,
    iterate_derivative_X_pow_eq_C_mul]
  simp only [eval_mul, eval_C, eval_pow, eval_X, mul_assoc]

/-- Theorem: Taylor's formula with the Lagrange remainder, expressed by a finite
derivative chain. Lower derivatives are continuous on the closed interval,
and their derivatives exist in its interior. Each coefficient uses its own factorial. -/
private theorem taylor_lagrange_chain (F : ℕ → ℝ → ℝ) (n : ℕ) (hn : 0 < n)
    (x y : ℝ) (hxy : x ≠ y)
    (hc : ∀ k < n, ContinuousOn (F k) (Icc (min x y) (max x y)))
    (hd : ∀ k < n, ∀ t ∈ Ioo (min x y) (max x y),
      HasDerivAt (F k) (F (k + 1) t) t) :
    ∃ c ∈ Ioo (min x y) (max x y),
      F 0 y = (∑ k ∈ Finset.range n, F k x / (k.factorial : ℝ) * (y - x) ^ k) +
        F n c / (n.factorial : ℝ) * (y - x) ^ n := by
  let S : Polynomial ℝ := ∑ k ∈ Finset.range n, monomial k (F k x / (k.factorial : ℝ))
  let K := (F 0 y - S.eval (y - x)) / (y - x) ^ n
  let P := S + monomial n K
  let H := fun k t => F k t - ((derivative^[k]) P).eval (t - x)
  have hfact : ∀ k : ℕ, (k.factorial : ℝ) ≠ 0 := fun k =>
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hPbase : ∀ k < n, ((derivative^[k]) P).eval 0 = F k x := by
    intro k hk
    rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative]
    simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul]

    have hcoeff : P.coeff k = F k x / (k.factorial : ℝ) := by
      dsimp only [P, S]
      rw [coeff_add, finsetSum_coeff]

      have hsum : (∑ j ∈ Finset.range n,
          (monomial j (F j x / (j.factorial : ℝ))).coeff k) =
          F k x / (k.factorial : ℝ) := by
        rw [Finset.sum_eq_single k]
        · exact coeff_monomial_same _ _
        · intro j _ hj
          exact coeff_monomial_of_ne _ (Ne.symm hj)
        · intro hn
          exact False.elim (hn (Finset.mem_range.mpr hk))
      rw [hsum, coeff_monomial_of_ne K (ne_of_lt hk)]
      exact add_zero _
    rw [hcoeff]
    field_simp

  have hPtop : ∀ t, ((derivative^[n]) P).eval t = (n.factorial : ℝ) * K := by
    intro t
    have hadd : (derivative^[n]) P = (derivative^[n]) S +
        (derivative^[n]) (monomial n K) := by
      change (derivative^[n]) (S + monomial n K) = _
      simp only [← Module.End.pow_apply, map_add]
    rw [hadd, eval_add]

    have hz : ((derivative^[n]) S).eval t = 0 := by
      dsimp only [S]
      rw [iterate_derivative_sum, eval_finsetSum]
      apply Finset.sum_eq_zero
      intro k hk
      rw [polynomial_iterate_monomial, Nat.descFactorial_of_lt (Finset.mem_range.mp hk),
        Nat.cast_zero, mul_zero, zero_mul]
    rw [hz, zero_add, polynomial_iterate_monomial, Nat.descFactorial_self,
      Nat.sub_self, pow_zero, mul_one, mul_comm]

  have hHz : ∀ k < n, H k x = 0 := by
    intro k hk
    dsimp only [H]
    rw [sub_self, hPbase k hk, sub_self]

  have hHy : H 0 y = 0 := by
    dsimp only [H, P]
    rw [Function.iterate_zero_apply, eval_add, eval_monomial]

    have hneq : (y - x) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hxy))
    dsimp only [K]
    rw [div_mul_cancel₀ _ hneq]
    ring

  have hHC : ∀ k < n, ContinuousOn (H k) (Icc (min x y) (max x y)) := by
    intro k hk
    apply (MathematicalAnalysis.Chapter03.continuousOn_iff_restrict _ _).mpr

    have hpoly : Continuous (fun t => ((derivative^[k]) P).eval (t - x)) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact continuousAt_of_hasDerivAt _ _ t
        (polynomial_shift_derivative ((derivative^[k]) P) x t)

    exact MathematicalAnalysis.Chapter03.continuous_sub _ _
      ((MathematicalAnalysis.Chapter03.continuousOn_iff_restrict _ _).mp (hc k hk))
      ((MathematicalAnalysis.Chapter03.continuousOn_iff_restrict _ _).mp hpoly.continuousOn)

  have hHD : ∀ k < n, ∀ t ∈ Ioo (min x y) (max x y), HasDerivAt (H k) (H (k + 1) t) t := by
    intro k hk t ht
    have hp := polynomial_shift_derivative ((derivative^[k]) P) x t
    have hcomb := hasDerivAt_linear_combination (F k)
      (fun t => ((derivative^[k]) P).eval (t - x)) (F (k + 1) t)
      (((derivative^[k]) P).derivative.eval (t - x)) 1 (-1) t (hd k hk t ht) hp
    simpa only [H, one_mul, neg_one_mul, sub_eq_add_neg, Function.iterate_succ_apply']
      using hcomb

  have hab : min x y < max x y := min_lt_max.mpr hxy
  have hend : H 0 (min x y) = 0 ∧ H 0 (max x y) = 0 ∧
      ((∀ k < n, H k (min x y) = 0) ∨ (∀ k < n, H k (max x y) = 0)) := by
    rcases le_total x y with h | h
    · rw [min_eq_left h, max_eq_right h]
      exact ⟨hHz 0 hn, hHy, Or.inl hHz⟩
    · rw [min_eq_right h, max_eq_left h]
      exact ⟨hHy, hHz 0 hn, Or.inr hHz⟩

  obtain ⟨c, hcI, hzero⟩ := repeated_rolle H n hn _ _ hab hHC hHD
    hend.1 hend.2.1 hend.2.2
  have hFn : F n c = (n.factorial : ℝ) * K := by
    have h := sub_eq_zero.mp hzero
    exact h.trans (hPtop (c - x))

  have hK : F n c / (n.factorial : ℝ) = K := by
    rw [hFn]
    field_simp

  refine ⟨c, hcI, ?_⟩
  rw [hK]

  have heval : S.eval (y - x) = ∑ k ∈ Finset.range n,
      F k x / (k.factorial : ℝ) * (y - x) ^ k := by
    simp only [S, eval_finsetSum, eval_monomial]
  rw [← heval]
  dsimp only [K]
  rw [div_mul_cancel₀ _ (pow_ne_zero n (sub_ne_zero.mpr (Ne.symm hxy)))]
  ring

/-- Theorem: Taylor's formula with the Lagrange remainder, using standard
iterated derivatives. All lower derivatives are continuous on the closed interval
and differentiable in its interior; the expansion works in either direction. -/
theorem taylor_lagrange (f : ℝ → ℝ) (n : ℕ) (hn : 0 < n) (x y : ℝ) (hxy : x ≠ y)
    (hc : ∀ k < n, ContinuousOn (iteratedDeriv k f) (Icc (min x y) (max x y)))
    (hd : ∀ k < n, ∀ t ∈ Ioo (min x y) (max x y),
      DifferentiableAt ℝ (iteratedDeriv k f) t) :
    ∃ c ∈ Ioo (min x y) (max x y),
      f y = (∑ k ∈ Finset.range n,
        iteratedDeriv k f x / (k.factorial : ℝ) * (y - x) ^ k) +
        iteratedDeriv n f c / (n.factorial : ℝ) * (y - x) ^ n := by
  have hchain : ∀ k < n, ∀ t ∈ Ioo (min x y) (max x y),
      HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f t) t := by
    intro k hk t ht
    rw [iteratedDeriv_succ]
    exact (hd k hk t ht).hasDerivAt

  simpa only [iteratedDeriv_zero] using
    taylor_lagrange_chain (fun k => iteratedDeriv k f) n hn x y hxy hc hchain

end MathematicalAnalysis.Chapter04
