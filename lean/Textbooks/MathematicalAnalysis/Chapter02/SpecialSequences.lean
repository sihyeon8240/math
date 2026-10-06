import Textbooks.MathematicalAnalysis.Chapter02.UpperLowerLimits
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace MathematicalAnalysis.Chapter02

open Set Metric Filter
open scoped Topology

/-- Theorem: powers of a real number of absolute value less than one tend to zero. -/
theorem geometric_tendsto_zero (x : ℝ) (hx : |x| < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hx
  refine ⟨N, ?_⟩
  intro n hn
  rw [Real.dist_eq, sub_zero, abs_pow]
  exact (pow_le_pow_of_le_one (abs_nonneg x) hx.le hn).trans_lt hN

/-- Lemma: reciprocal positive-integer terms tend to zero by Archimedean arithmetic. -/
theorem reciprocal_tendsto_zero :
    Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨N, ?_⟩
  intro n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  exact (one_div_le_one_div_of_le (by positivity)
    (by exact_mod_cast Nat.succ_le_succ hn)).trans_lt hN

/-- Theorem: the reciprocal of a positive real power of the index tends to zero. -/
theorem reciprocal_rpow_tendsto_zero (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ) ^ a) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((1 / ε) ^ a⁻¹)
  refine ⟨N, ?_⟩
  intro n hn
  have hbase : (1 / ε) ^ a⁻¹ < n + 1 := by
    have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith

  have hpow := (Real.rpow_lt_rpow_iff (Real.rpow_nonneg (by positivity) _)
    (by positivity : 0 ≤ (n + 1 : ℝ)) ha).mpr hbase
  rw [Real.rpow_inv_rpow (by positivity) ha.ne'] at hpow

  have hp : 0 < (n + 1 : ℝ) ^ a := Real.rpow_pos_of_pos (by positivity) _
  rw [Real.dist_eq, sub_zero, abs_of_pos (div_pos zero_lt_one hp), div_lt_iff₀ hp]

  have he := (div_lt_iff₀ hε).mp hpow
  nlinarith

/-- Lemma: powers of convergent real sequences converge, by induction and multiplication. -/
theorem real_tendsto_pow (u : ℕ → ℝ) (a : ℝ) (hu : Tendsto u atTop (𝓝 a)) (k : ℕ) :
    Tendsto (fun n => u n ^ k) atTop (𝓝 (a ^ k)) := by
  induction k with
  | zero => simpa only [pow_zero] using real_tendsto_const 1
  | succ k ih =>
    simpa only [pow_succ] using real_tendsto_mul _ _ _ _ ih hu

/-- Lemma: an eventual geometric contraction of absolute values forces convergence to zero. -/
theorem geometric_contraction_tendsto_zero (u : ℕ → ℝ) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hu : ∀ᶠ n in atTop, |u (n + 1)| ≤ q * |u n|) :
    Tendsto u atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hu
  have hiter : ∀ k : ℕ, |u (N + k)| ≤ |u N| * q ^ k := by
    intro k
    induction k with
    | zero => simp only [Nat.add_zero, pow_zero, mul_one, le_refl]
    | succ k ih =>
      have hs := hN (N + k) (Nat.le_add_right N k)
      have hm := mul_le_mul_of_nonneg_left ih hq0
      rw [Nat.add_assoc] at hs
      rw [pow_succ]
      nlinarith

  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one
    (div_pos hε (by linarith [abs_nonneg (u N)] : 0 < |u N| + 1)) hq1
  refine ⟨N + M, ?_⟩
  intro n hn
  have hsub : N + (n - N) = n := by omega
  have hMN : M ≤ n - N := by omega
  have hbound := hiter (n - N)
  rw [hsub] at hbound

  have hpower := pow_le_pow_of_le_one hq0 hq1.le hMN
  have hsmall := (lt_div_iff₀ (by linarith [abs_nonneg (u N)] : 0 < |u N| + 1)).mp hM
  rw [Real.dist_eq, sub_zero]

  have hmul := mul_le_mul_of_nonneg_left hpower (abs_nonneg (u N))
  have hpos := pow_nonneg hq0 M
  nlinarith

/-- Lemma: a natural power of the index divided by an exponential tends to zero. -/
theorem nat_pow_div_exponential_tendsto_zero (k : ℕ) (b : ℝ) (hb : 1 < b) :
    Tendsto (fun n : ℕ => (n + 1 : ℝ) ^ k / b ^ (n + 1)) atTop (𝓝 0) := by
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  let u : ℕ → ℝ := fun n => (n + 1 : ℝ) ^ k / b ^ (n + 1)
  let r : ℕ → ℝ := fun n => (1 + 1 / (n + 1 : ℝ)) ^ k * (1 / b)
  have hr : Tendsto r atTop (𝓝 (1 / b)) := by
    have hadd := real_tendsto_add _ _ 1 0 (real_tendsto_const 1) reciprocal_tendsto_zero
    have hpow := real_tendsto_pow _ _ hadd k
    simpa only [add_zero, one_pow, one_mul] using
      real_tendsto_mul _ _ _ _ hpow (real_tendsto_const (1 / b))

  have hstep : ∀ n, u (n + 1) = r n * u n := by
    intro n
    have hcoord : (1 + 1 / (n + 1 : ℝ)) * (n + 1) = n + 2 := by
      field_simp
      ring

    have hcoordpow := congrArg (fun x : ℝ => x ^ k) hcoord
    rw [mul_pow] at hcoordpow
    dsimp [u, r]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show (n : ℝ) + 1 + 1 = n + 2 by ring, pow_succ b (n + 1)]
    rw [← hcoordpow]
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
    ring

  let q := (1 / b + 1) / 2
  have hinv : 1 / b < 1 := (div_lt_one hb0).mpr hb
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity

  have hq1 : q < 1 := by
    dsimp [q]
    linarith

  have hgap : 0 < q - 1 / b := by
    dsimp [q]
    linarith

  apply geometric_contraction_tendsto_zero u q hq0 hq1

  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hr (q - 1 / b) hgap
  apply eventually_atTop.mpr
  refine ⟨N, ?_⟩
  intro n hn
  have hnear : |r n - 1 / b| < q - 1 / b := hN n hn
  have hrq : r n ≤ q := by linarith [(abs_lt.mp hnear).2]
  have hu0 : 0 ≤ u n := by
    dsimp [u]
    positivity

  have hr0 : 0 ≤ r n := by
    dsimp [r]
    positivity
  rw [hstep, abs_of_nonneg (mul_nonneg hr0 hu0), abs_of_nonneg hu0]
  exact mul_le_mul_of_nonneg_right hrq hu0

/-- Theorem: every real power of the index is dominated by an exponential
of base greater than one. -/
theorem rpow_div_exponential_tendsto_zero (a γ : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ => (n + 1 : ℝ) ^ γ / (1 + a) ^ (n + 1)) atTop (𝓝 0) := by
  obtain ⟨k, hk⟩ := exists_nat_gt γ
  have hnat := nat_pow_div_exponential_tendsto_zero k (1 + a) (by linarith)
  apply real_tendsto_squeeze (fun _ => 0) _ _ 0 _ _ (real_tendsto_const 0) hnat

  · intro n
    positivity

  · intro n
    apply div_le_div_of_nonneg_right _ (by positivity)

    have hbase : 1 ≤ (n + 1 : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) n]
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hbase hk.le

/-- Theorem: the positive-integer roots of a fixed positive real number tend to one. -/
theorem nth_root_tendsto_one (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ => a ^ ((n + 1 : ℝ)⁻¹)) atTop (𝓝 1) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt a (by linarith : 1 < 1 + ε)
  have hupper : ∀ n ≥ M, a ^ ((n + 1 : ℝ)⁻¹) < 1 + ε := by
    intro n hn
    have hp := pow_le_pow_right₀ (by linarith : 1 ≤ 1 + ε) (hn.trans (Nat.le_succ n))
    have hsmall : a < (1 + ε) ^ (n + 1) := hM.trans_le hp
    have hroot := (Real.rpow_lt_rpow_iff ha.le
      (pow_nonneg (by linarith) _) (by positivity : 0 < (n + 1 : ℝ)⁻¹)).mpr hsmall
    rw [← Nat.cast_succ] at hroot
    rw [Real.pow_rpow_inv_natCast (by linarith : 0 ≤ 1 + ε) (Nat.succ_ne_zero n)] at hroot
    simpa only [Nat.cast_succ] using hroot

  by_cases hε1 : 1 ≤ ε

  · refine ⟨M, ?_⟩
    intro n hn
    have hrootpos := Real.rpow_pos_of_pos ha ((n + 1 : ℝ)⁻¹)
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hupper n hn]

  · have hq0 : 0 < 1 - ε := by linarith
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one ha (by linarith : 1 - ε < 1)
    refine ⟨max M N, ?_⟩
    intro n hn
    have hp := pow_le_pow_of_le_one hq0.le (by linarith : 1 - ε ≤ 1)
      (((le_max_right M N).trans hn).trans (Nat.le_succ n))
    have hsmall : (1 - ε) ^ (n + 1) < a := hp.trans_lt hN
    have hroot := (Real.rpow_lt_rpow_iff (pow_nonneg hq0.le _) ha.le
      (by positivity : 0 < (n + 1 : ℝ)⁻¹)).mpr hsmall
    rw [← Nat.cast_succ] at hroot
    rw [Real.pow_rpow_inv_natCast hq0.le (Nat.succ_ne_zero n)] at hroot
    simp only [Nat.cast_succ] at hroot
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hupper n ((le_max_left _ _).trans hn)]

/-- Theorem: the positive-integer roots of their indices tend to one. -/
theorem index_nth_root_tendsto_one :
    Tendsto (fun n : ℕ => (n + 1 : ℝ) ^ ((n + 1 : ℝ)⁻¹)) atTop (𝓝 1) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hlim := nat_pow_div_exponential_tendsto_zero 1 (1 + ε) (by linarith)

  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim 1 zero_lt_one
  refine ⟨N, ?_⟩
  intro n hn
  have hnear := hN n hn
  rw [Real.dist_eq, sub_zero, pow_one, abs_of_nonneg (by positivity)] at hnear

  have hsmall := (div_lt_one (by positivity : 0 < (1 + ε) ^ (n + 1))).mp hnear
  have hroot := (Real.rpow_lt_rpow_iff (by positivity : 0 ≤ (n + 1 : ℝ))
    (pow_nonneg (by linarith) _) (by positivity : 0 < (n + 1 : ℝ)⁻¹)).mpr hsmall
  rw [← Nat.cast_succ] at hroot
  rw [Real.pow_rpow_inv_natCast (by linarith : 0 ≤ 1 + ε) (Nat.succ_ne_zero n)] at hroot
  simp only [Nat.cast_succ] at hroot

  have hlower : 1 ≤ (n + 1 : ℝ) ^ ((n + 1 : ℝ)⁻¹) := by
    exact Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by positivity)
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlower)]
  linarith

end MathematicalAnalysis.Chapter02
