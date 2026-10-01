import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace LinearAlgebra.Chapter05

open scoped BigOperators

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- Definition: projection coefficient with Mathlib's conjugate-linear first argument. -/
noncomputable def innerComponent (v w : E) : 𝕜 := ⟪w, v⟫ / ⟪w, w⟫

/-- Proposition: the norm is the nonnegative square root of the square of a vector. -/
theorem norm_eq_sqrt (v : E) : ‖v‖ = Real.sqrt (RCLike.re ⟪v, v⟫) :=
  norm_eq_sqrt_re_inner (𝕜 := 𝕜) v

/-- Proposition: scalar multiplication scales length by the scalar's modulus. -/
theorem norm_smul (a : 𝕜) (v : E) : ‖a • v‖ = ‖a‖ * ‖v‖ := by
  rw [norm_eq_sqrt (𝕜 := 𝕜), inner_smul_left, inner_smul_right]
  rw [← mul_assoc, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.re_ofReal_mul]
  rw [Real.sqrt_mul (sq_nonneg ‖a‖), Real.sqrt_sq (norm_nonneg a)]
  rw [← norm_eq_sqrt (𝕜 := 𝕜)]

/-- Theorem: perpendicular vectors satisfy the Pythagorean identity. -/
theorem pythagoras {v w : E} (h : ⟪v, w⟫ = 0) :
    ‖v + w‖ ^ 2 = ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), inner_add_left, inner_add_right,
    inner_add_right, h, (inner_eq_zero_symm.mp h)]
  simp only [map_add, add_zero, zero_add, inner_self_eq_norm_sq]

/-- Proposition: the projection remainder is orthogonal to its direction. -/
theorem inner_sub_projection (v w : E) : ⟪w, v - innerComponent (𝕜 := 𝕜) v w • w⟫ = 0 := by
  by_cases hw : w = 0

  · subst w
    exact inner_zero_left _

  · rw [inner_sub_right, inner_smul_right, innerComponent,
      div_mul_cancel₀ _ (inner_self_ne_zero.mpr hw), sub_self]

/-- Proposition: the component along a unit vector is its inner product with the vector. -/
theorem innerComponent_unit (v w : E) (hw : ‖w‖ = 1) :
    innerComponent (𝕜 := 𝕜) v w = ⟪w, v⟫ := by
  rw [innerComponent, inner_self_eq_norm_sq_to_K, hw]
  simp only [RCLike.ofReal_one, one_pow, div_one]

/-- Theorem: a nonzero direction has exactly one projection coefficient. -/
theorem exists_unique_innerComponent (v w : E) (hw : w ≠ 0) :
    ∃! c : 𝕜, ⟪w, v - c • w⟫ = 0 := by
  refine ⟨innerComponent (𝕜 := 𝕜) v w, inner_sub_projection v w, ?_⟩

  intro c hc
  rw [inner_sub_right, inner_smul_right] at hc
  exact (eq_div_iff (inner_self_ne_zero.mpr hw)).mpr (sub_eq_zero.mp hc).symm

/-- Theorem: Schwarz's inequality follows from the nonnegative projection remainder. -/
theorem norm_inner_le_norm (v w : E) : ‖⟪v, w⟫‖ ≤ ‖v‖ * ‖w‖ := by
  by_cases hw : w = 0

  · subst w
    simp only [inner_zero_right, norm_zero, mul_zero, le_refl]

  have hp : ⟪innerComponent (𝕜 := 𝕜) v w • w, v - innerComponent (𝕜 := 𝕜) v w • w⟫ = 0 := by
    rw [inner_smul_left, inner_sub_projection, mul_zero]

  have he := pythagoras hp
  rw [add_sub_cancel] at he

  have hs : ‖innerComponent (𝕜 := 𝕜) v w • w‖ = ‖⟪v, w⟫‖ / ‖w‖ := by
    rw [norm_smul, innerComponent, norm_div, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
      RCLike.norm_ofReal, abs_of_nonneg (sq_nonneg _), norm_inner_symm]

    have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    field_simp

  rw [hs] at he
  have hb : ‖⟪v, w⟫‖ / ‖w‖ ≤ ‖v‖ := by
    have hq := sq_nonneg ‖v - innerComponent (𝕜 := 𝕜) v w • w‖
    have hd := div_nonneg (norm_nonneg ⟪v, w⟫) (norm_nonneg w)
    nlinarith [norm_nonneg v]

  exact (div_le_iff₀ (norm_pos_iff.mpr hw)).mp hb

include 𝕜 in
/-- Theorem: the triangle inequality follows by expanding the square and applying Schwarz. -/
theorem norm_add_le (v w : E) : ‖v + w‖ ≤ ‖v‖ + ‖w‖ := by
  have hs := norm_inner_le_norm (𝕜 := 𝕜) v w
  have hr := RCLike.re_le_norm ⟪v, w⟫

  have he : ‖v + w‖ ^ 2 = ‖v‖ ^ 2 + 2 * RCLike.re ⟪v, w⟫ + ‖w‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), inner_add_left,
      inner_add_right, inner_add_right]
    simp only [map_add, inner_self_eq_norm_sq, inner_re_symm w v]
    ring

  nlinarith [norm_nonneg (v + w), norm_nonneg v, norm_nonneg w]

/-- Lemma: the inner product of an orthogonal combination with one member isolates its
coefficient. -/
theorem inner_sum_orthogonal {ι : Type*} [Fintype ι] (u : ι → E)
    (hu : Pairwise fun i j => ⟪u i, u j⟫ = 0) (a : ι → 𝕜) (j : ι) :
    ⟪u j, ∑ i, a i • u i⟫ = a j * ⟪u j, u j⟫ := by
  classical
  rw [inner_sum]
  simp only [inner_smul_right]
  apply Finset.sum_eq_single j

  · intro i _ hij
    rw [hu hij.symm, mul_zero]

  · intro h
    exact (h (Finset.mem_univ j)).elim

/-- Theorem: nonzero perpendicular vectors are linearly independent. -/
theorem orthogonal_linearIndependent {ι : Type*} [Fintype ι] (u : ι → E)
    (hu : Pairwise fun i j => ⟪u i, u j⟫ = 0) (hn : ∀ i, u i ≠ 0) :
    LinearIndependent 𝕜 u := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha j
  have he := inner_sum_orthogonal u hu a j
  rw [ha, inner_zero_right] at he
  exact (mul_eq_zero.mp he.symm).resolve_right (inner_self_ne_zero.mpr (hn j))

/-- Definition: the sum of the components in a finite perpendicular family. -/
noncomputable def orthogonalProjection {ι : Type*} [Fintype ι] (u : ι → E) (v : E) : E :=
  ∑ i, innerComponent (𝕜 := 𝕜) v (u i) • u i

/-- Theorem: subtracting all components gives a perpendicular remainder. -/
theorem inner_sub_orthogonalProjection {ι : Type*} [Fintype ι] (u : ι → E)
    (hu : Pairwise fun i j => ⟪u i, u j⟫ = 0) (v : E) (j : ι) :
    ⟪u j, v - orthogonalProjection (𝕜 := 𝕜) u v⟫ = 0 := by
  by_cases hj : u j = 0

  · rw [hj, inner_zero_left]

  · rw [inner_sub_right, orthogonalProjection, inner_sum_orthogonal u hu,
      innerComponent, div_mul_cancel₀ _ (inner_self_ne_zero.mpr hj), sub_self]

/-- Theorem: projection onto a finite orthogonal family gives the best approximation. -/
theorem orthogonalProjection_minimizes {ι : Type*} [Fintype ι] (u : ι → E)
    (hu : Pairwise fun i j => ⟪u i, u j⟫ = 0) (v : E) (a : ι → 𝕜) :
    ‖v - orthogonalProjection (𝕜 := 𝕜) u v‖ ≤ ‖v - ∑ i, a i • u i‖ := by
  let r := v - orthogonalProjection (𝕜 := 𝕜) u v
  let d := orthogonalProjection (𝕜 := 𝕜) u v - ∑ i, a i • u i

  have hp : ⟪d, r⟫ = 0 := by
    simp only [d, orthogonalProjection, inner_sub_left, sum_inner, inner_smul_left]
    have hz : ∀ i, ⟪u i, r⟫ = 0 := inner_sub_orthogonalProjection (𝕜 := 𝕜) u hu v
    simp only [hz, mul_zero, Finset.sum_const_zero, sub_self]

  have he := pythagoras hp
  have hd : d + r = v - ∑ i, a i • u i := by
    dsimp [d, r]
    abel

  rw [hd] at he
  change ‖r‖ ≤ ‖v - ∑ i, a i • u i‖
  nlinarith [sq_nonneg ‖d‖, norm_nonneg r, norm_nonneg (v - ∑ i, a i • u i)]

/-- Lemma: the square of an orthogonal sum is the sum of the squares. -/
theorem norm_sum_sq {ι : Type*} [Fintype ι] (u : ι → E)
    (hu : Pairwise fun i j => ⟪u i, u j⟫ = 0) (a : ι → 𝕜) :
    ‖∑ i, a i • u i‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 * ‖u i‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), sum_inner, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [inner_smul_left, inner_sum_orthogonal u hu, ← mul_assoc,
    RCLike.conj_mul, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
    ← RCLike.ofReal_pow, ← RCLike.ofReal_mul,
    RCLike.ofReal_re]

/-- Theorem: the sum of the squared coefficients in a finite orthonormal family is bounded by
length squared. -/
theorem bessel {ι : Type*} [Fintype ι] (u : ι → E) (hu : Orthonormal 𝕜 u) (v : E) :
    ∑ i, ‖⟪u i, v⟫‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  have hp : ⟪orthogonalProjection (𝕜 := 𝕜) u v, v - orthogonalProjection (𝕜 := 𝕜) u v⟫ = 0 := by
    change ⟪∑ i, innerComponent (𝕜 := 𝕜) v (u i) • u i,
      v - orthogonalProjection (𝕜 := 𝕜) u v⟫ = 0
    rw [sum_inner]
    simp only [inner_smul_left, inner_sub_orthogonalProjection (𝕜 := 𝕜) u hu.2,
      mul_zero, Finset.sum_const_zero]

  have he := pythagoras hp
  rw [add_sub_cancel, orthogonalProjection, norm_sum_sq u hu.2] at he

  have hc : ∀ i, innerComponent (𝕜 := 𝕜) v (u i) = ⟪u i, v⟫ := by
    intro i
    rw [innerComponent, inner_self_eq_norm_sq_to_K, hu.1 i]
    simp only [RCLike.ofReal_one, one_pow, div_one]

  simp only [hc, hu.1, one_pow, mul_one] at he
  nlinarith [sq_nonneg ‖v - orthogonalProjection (𝕜 := 𝕜) u v‖]

/-- Corollary: Bessel's inequality in the real squared-coefficient formulation. -/
theorem bessel_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] (u : ι → E) (hu : Orthonormal ℝ u) (v : E) :
    ∑ i, (inner ℝ (u i) v) ^ 2 ≤ ‖v‖ ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using bessel u hu v

end LinearAlgebra.Chapter05
