import Textbooks.MathematicalAnalysis.Chapter02.Series
import Mathlib.Algebra.Order.Archimedean.Basic

namespace MathematicalAnalysis.Chapter02

open Filter Finset
open scoped Topology

private theorem dyadic_block_bounds (u : ℕ → ℝ) (hu : Antitone u) (k : ℕ) :
    (2 : ℝ) ^ k * u (2 ^ (k + 1)) ≤ ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), u n ∧
    (∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), u n) ≤ (2 : ℝ) ^ k * u (2 ^ k) := by
  have hcard : (Ico (2 ^ k) (2 ^ (k + 1))).card = 2 ^ k := by
    rw [Nat.card_Ico, pow_succ]
    omega

  constructor

  · calc
      (2 : ℝ) ^ k * u (2 ^ (k + 1)) =
          ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), u (2 ^ (k + 1)) := by
        simp only [sum_const, hcard, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      _ ≤ ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), u n := by
        apply sum_le_sum
        intro n hn
        exact hu (mem_Ico.mp hn).2.le

  · calc
      (∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), u n) ≤
          ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), u (2 ^ k) := by
        apply sum_le_sum
        intro n hn
        exact hu (mem_Ico.mp hn).1
      _ = (2 : ℝ) ^ k * u (2 ^ k) := by
        simp only [sum_const, hcard, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

private theorem dyadic_partial_sum_bounds (u : ℕ → ℝ) (hpos : ∀ n, 0 ≤ u n)
    (hu : Antitone u) (k : ℕ) :
    partialSums u (2 ^ k) ≤ u 0 + partialSums (fun j => (2 : ℝ) ^ j * u (2 ^ j)) k ∧
    partialSums (fun j => (2 : ℝ) ^ j * u (2 ^ j)) (k + 1) ≤
      u 1 + 2 * partialSums u (2 ^ k) := by
  induction k with
  | zero =>
    simp only [pow_zero, partialSums, sum_range_zero, sum_range_one, one_mul,
      zero_add, add_zero]
    constructor
    · exact le_rfl
    · linarith [hpos 0]

  | succ k ih =>
    have hk : 2 ^ k ≤ (2 : ℕ) ^ (k + 1) := by
      rw [pow_succ]
      omega
    have hblock := dyadic_block_bounds u hu k
    rw [sum_Ico_eq_partialSums_sub u _ _ hk] at hblock
    rw [partialSums_succ, partialSums_succ]
    constructor
    · linarith [ih.1, hblock.2]
    · rw [pow_succ (2 : ℝ) k]
      linarith [ih.2, hblock.1]

private theorem condensation_nonneg (u : ℕ → ℝ) (hpos : ∀ n, 0 ≤ u n) (hu : Antitone u) :
    SeriesConverges u ↔ SeriesConverges (fun k => (2 : ℝ) ^ k * u (2 ^ k)) := by
  have hcpos : ∀ k, 0 ≤ (2 : ℝ) ^ k * u (2 ^ k) := fun k =>
    mul_nonneg (pow_nonneg (by norm_num) k) (hpos _)
  rw [nonneg_seriesConverges_iff u hpos, nonneg_seriesConverges_iff _ hcpos]
  constructor

  · rintro ⟨B, hB⟩
    refine ⟨max 0 (u 1 + 2 * B), ?_⟩
    rintro x ⟨k, rfl⟩
    cases k with
    | zero =>
      change 0 ≤ max 0 (u 1 + 2 * B)
      exact le_max_left _ _
    | succ k =>
      have hbound := (dyadic_partial_sum_bounds u hpos hu k).2
      have hpartial := hB (Set.mem_range_self (2 ^ k))
      exact (hbound.trans (by linarith)).trans (le_max_right _ _)

  · rintro ⟨B, hB⟩
    refine ⟨u 0 + B, ?_⟩
    rintro x ⟨n, rfl⟩
    have hn : n ≤ 2 ^ n := (show n < 2 ^ n from Nat.lt_two_pow_self).le
    have hmono := partialSums_monotone u hpos hn
    have hbound := (dyadic_partial_sum_bounds u hpos hu n).1
    have hc := hB (Set.mem_range_self n)
    linarith

/-- Theorem: a nonnegative nonincreasing series from index one converges exactly when
its dyadic condensation does; the zeroth term is unrestricted. -/
theorem condensation_test (u : ℕ → ℝ) (hpos : ∀ n, 0 < n → 0 ≤ u n)
    (hu : ∀ m n, 0 < m → m ≤ n → u n ≤ u m) :
    SeriesConverges u ↔ SeriesConverges (fun k => (2 : ℝ) ^ k * u (2 ^ k)) := by
  let w : ℕ → ℝ := fun n => u (max n 1)
  have hwpos : ∀ n, 0 ≤ w n := fun n =>
    hpos _ (Nat.zero_lt_one.trans_le (le_max_right n 1))
  have hwmono : Antitone w := by
    intro m n hmn
    exact hu _ _ (Nat.zero_lt_one.trans_le (le_max_right m 1)) (max_le_max hmn le_rfl)
  have heq : u =ᶠ[atTop] w := eventually_atTop.mpr ⟨1, fun n hn => by
    dsimp [w]
    rw [max_eq_left hn]⟩
  rw [seriesConverges_congr_eventually u w heq, condensation_nonneg w hwpos hwmono]
  have hcond : (fun k => (2 : ℝ) ^ k * w (2 ^ k)) =
      (fun k => (2 : ℝ) ^ k * u (2 ^ k)) := by
    funext k
    dsimp [w]
    rw [max_eq_left (Nat.one_le_pow k 2 (by norm_num))]
  rw [hcond]

end MathematicalAnalysis.Chapter02
