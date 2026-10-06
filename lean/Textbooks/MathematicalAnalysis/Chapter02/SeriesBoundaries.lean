import Textbooks.MathematicalAnalysis.Chapter02.RootRatioTests
import Textbooks.MathematicalAnalysis.Chapter02.CondensationTest

namespace MathematicalAnalysis.Chapter02

open Filter
open scoped Topology

/-- Definition: reciprocal powers provide witnesses for the limitations of convergence tests. -/
private noncomputable def reciprocalTerms (k n : ℕ) : ℝ := 1 / (max n 1 : ℕ) ^ k

private theorem reciprocalTerms_pos (k n : ℕ) : 0 < reciprocalTerms k n := by
  dsimp [reciprocalTerms]
  positivity

private theorem reciprocalTerms_antitone (k : ℕ) : Antitone (reciprocalTerms k) := by
  intro m n hmn
  apply one_div_le_one_div_of_le
  · exact pow_pos (by positivity) k
  · apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast max_le_max hmn le_rfl

private theorem constant_one_series_diverges : ¬ SeriesConverges (fun _ : ℕ => (1 : ℝ)) := by
  intro h
  have heq := limit_unique (fun _ : ℕ => (1 : ℝ)) 1 0 (real_tendsto_const 1)
    (seriesConverges_tendsto_zero _ h)
  norm_num at heq

/-- Theorem: tending to zero does not suffice for convergence of a real series. -/
theorem tendsto_zero_not_sufficient :
    ∃ u : ℕ → ℝ, Tendsto u atTop (𝓝 0) ∧ ¬ SeriesConverges u := by
  refine ⟨reciprocalTerms 1, ?_, ?_⟩

  · apply (tendsto_iff_succ _ _).mpr
    have heq : (fun n => reciprocalTerms 1 (n + 1)) =
        (fun n : ℕ => 1 / (n + 1 : ℝ)) := by
      funext n
      dsimp [reciprocalTerms]
      rw [max_eq_left (by omega : 1 ≤ n + 1)]
      simp only [Nat.cast_add, Nat.cast_one, pow_one]
    rw [heq]
    exact reciprocal_tendsto_zero

  · intro h
    have hc := (condensation_test (reciprocalTerms 1)
      (fun n _ => (reciprocalTerms_pos 1 n).le)
      (fun _ _ _ hmn => reciprocalTerms_antitone 1 hmn)).mp h
    have heq : (fun j => (2 : ℝ) ^ j * reciprocalTerms 1 (2 ^ j)) =
        (fun _ : ℕ => (1 : ℝ)) := by
      funext j
      dsimp [reciprocalTerms]
      rw [max_eq_left (Nat.one_le_pow j 2 (by norm_num))]
      simp only [Nat.cast_pow, Nat.cast_ofNat, pow_one]
      field_simp
    rw [heq] at hc
    exact constant_one_series_diverges hc

private theorem square_reciprocal_series : SeriesConverges (reciprocalTerms 2) := by
  apply (condensation_test (reciprocalTerms 2)
    (fun n _ => (reciprocalTerms_pos 2 n).le)
    (fun _ _ _ hmn => reciprocalTerms_antitone 2 hmn)).mpr
  have heq : (fun j => (2 : ℝ) ^ j * reciprocalTerms 2 (2 ^ j)) =
      (fun j : ℕ => 1 * (1 / 2 : ℝ) ^ j) := by
    funext j
    dsimp [reciprocalTerms]
    rw [max_eq_left (Nat.one_le_pow j 2 (by norm_num))]
    simp only [Nat.cast_pow, Nat.cast_ofNat, div_pow, one_pow, one_mul]
    field_simp
  rw [heq]
  exact geometric_series_converges 1 (1 / 2) zero_le_one (by norm_num) (by norm_num)

private theorem square_reciprocal_root_limit :
    Tendsto (rootTerms (reciprocalTerms 2)) atTop (𝓝 1) := by
  have hpos : ∀ n : ℕ, (n + 1 : ℝ) ^ ((n + 1 : ℝ)⁻¹) ≠ 0 := fun n =>
    (Real.rpow_pos_of_pos (by positivity) _).ne'
  have hinv := real_tendsto_inv _ 1 index_nth_root_tendsto_one hpos one_ne_zero
  have hsq := real_tendsto_pow _ _ hinv 2
  have heq : rootTerms (reciprocalTerms 2) =
      (fun n : ℕ => (1 / ((n + 1 : ℝ) ^ ((n + 1 : ℝ)⁻¹))) ^ 2) := by
    funext n
    dsimp [rootTerms, reciprocalTerms]
    rw [max_eq_left (by omega : 1 ≤ n + 1)]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [abs_of_pos (by positivity), one_div, Real.inv_rpow (by positivity),
      ← Real.rpow_pow_comm (by positivity)]
    simp only [one_div, inv_pow]
  rw [heq]
  simpa only [div_one, one_pow] using hsq

private theorem square_reciprocal_ratio_limit :
    Tendsto (ratioTerms (reciprocalTerms 2)) atTop (𝓝 1) := by
  have hbase := real_tendsto_add _ _ 1 ((-1) * 0) (real_tendsto_const 1)
    (real_tendsto_const_mul _ 0 (-1) reciprocal_tendsto_zero)
  have hlim := real_tendsto_pow _ _ hbase 2
  have heq : (fun n : ℕ => (1 + (-1) * (1 / (n + 1 : ℝ))) ^ 2) =ᶠ[atTop]
      ratioTerms (reciprocalTerms 2) := by
    apply eventually_atTop.mpr
    refine ⟨1, ?_⟩
    intro n hn
    dsimp [ratioTerms, reciprocalTerms]
    rw [max_eq_left (by omega : 1 ≤ n + 1), max_eq_left hn]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [abs_of_pos (by positivity)]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    field_simp [hn0]
    ring
  simpa only [mul_zero, add_zero, one_pow] using hlim.congr' heq

/-- Theorem: upper root and ratio limits equal to one admit both convergence and divergence. -/
theorem root_ratio_tests_inconclusive_at_one :
    ∃ u v : ℕ → ℝ,
      SeriesConverges u ∧ ¬ SeriesConverges v ∧
      (∀ n, u n ≠ 0 ∧ v n ≠ 0) ∧
      limsup (fun n => (rootTerms u n : EReal)) atTop = 1 ∧
      Tendsto (ratioTerms u) atTop (𝓝 1) ∧
      limsup (fun n => (rootTerms v n : EReal)) atTop = 1 ∧
      Tendsto (ratioTerms v) atTop (𝓝 1) := by
  refine ⟨reciprocalTerms 2, fun _ => 1, square_reciprocal_series,
    constant_one_series_diverges, fun n => ⟨(reciprocalTerms_pos 2 n).ne', one_ne_zero⟩,
    (liminf_limsup_of_tendsto _ 1 square_reciprocal_root_limit).2,
    square_reciprocal_ratio_limit, ?_, ?_⟩
  · simpa only [rootTerms, abs_one, Real.one_rpow, EReal.coe_one] using
      (liminf_limsup_of_tendsto _ 1 (real_tendsto_const 1)).2
  · change Tendsto (fun _ : ℕ => |(1 : ℝ) / 1|) atTop (𝓝 1)
    simpa only [div_one, abs_one] using
      real_tendsto_const 1

end MathematicalAnalysis.Chapter02
