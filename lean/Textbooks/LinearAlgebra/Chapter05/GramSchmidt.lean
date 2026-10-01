import Textbooks.LinearAlgebra.Chapter05.PositiveDefinite
import Textbooks.LinearAlgebra.Chapter01.DirectSums
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

namespace LinearAlgebra.Chapter05

open Module Submodule Set
open scoped BigOperators

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]

attribute [local instance] IsWellOrder.toHasWellFounded

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- Proposition: Gram–Schmidt subtracts precisely the earlier components. -/
theorem gramSchmidt_step (f : ι → E) (j : ι) :
    InnerProductSpace.gramSchmidt 𝕜 f j = f j -
      ∑ i ∈ Finset.Iio j,
        innerComponent (𝕜 := 𝕜) (f j) (InnerProductSpace.gramSchmidt 𝕜 f i) •
          InnerProductSpace.gramSchmidt 𝕜 f i := by
  rw [InnerProductSpace.gramSchmidt_def]
  simp only [Submodule.starProjection_singleton, innerComponent,
    inner_self_eq_norm_sq_to_K, RCLike.ofReal_pow]

/-- Theorem: the Gram–Schmidt vectors are mutually perpendicular. -/
theorem gramSchmidt_orthogonal (f : ι → E) :
    Pairwise fun i j =>
      ⟪InnerProductSpace.gramSchmidt 𝕜 f i, InnerProductSpace.gramSchmidt 𝕜 f j⟫ = 0 := by
  let g := InnerProductSpace.gramSchmidt 𝕜 f

  have hlt : ∀ j i, i < j → ⟪g i, g j⟫ = 0 := by
    intro j
    induction j using (wellFounded_lt : WellFounded ((· < ·) : ι → ι → Prop)).induction with
    | h j ih =>
      intro i hij
      have hg : g j = f j - ∑ k ∈ Finset.Iio j,
          innerComponent (𝕜 := 𝕜) (f j) (g k) • g k := gramSchmidt_step (𝕜 := 𝕜) f j

      rw [hg, inner_sub_right, inner_sum]
      simp only [inner_smul_right]
      rw [Finset.sum_eq_single i]

      · by_cases hi : g i = 0

        · rw [hi, inner_zero_left, inner_zero_left, mul_zero, sub_zero]

        · rw [innerComponent, div_mul_cancel₀ _ (inner_self_ne_zero.mpr hi), sub_self]

      · intro k hk hki
        have hk' := Finset.mem_Iio.mp hk
        have hz : ⟪g i, g k⟫ = 0 := by
          rcases lt_or_gt_of_ne hki with hki | hik

          · exact inner_eq_zero_symm.mp (ih i hij k hki)

          · exact ih k hk' i hik
        rw [hz, mul_zero]

      · intro hn
        exact (hn (Finset.mem_Iio.mpr hij)).elim

  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji

  · exact hlt j i hij

  · exact inner_eq_zero_symm.mp (hlt i j hji)

/-- Lemma: Gram–Schmidt preserves every initial span, including the strict initial span. -/
theorem gramSchmidt_span_initial (f : ι → E) (j : ι) :
    span 𝕜 (InnerProductSpace.gramSchmidt 𝕜 f '' Iic j) = span 𝕜 (f '' Iic j) ∧
    span 𝕜 (InnerProductSpace.gramSchmidt 𝕜 f '' Iio j) = span 𝕜 (f '' Iio j) := by
  let g := InnerProductSpace.gramSchmidt 𝕜 f

  induction j using (wellFounded_lt : WellFounded ((· < ·) : ι → ι → Prop)).induction with
  | h j ih =>
    have hlo : span 𝕜 (g '' Iio j) = span 𝕜 (f '' Iio j) := by
      apply span_eq_span

      · rintro _ ⟨i, hi, rfl⟩
        have hm : g i ∈ span 𝕜 (g '' Iic i) := subset_span ⟨i, le_rfl, rfl⟩
        rw [(ih i (mem_Iio.mp hi)).1] at hm

        exact span_mono (image_mono (Iic_subset_Iio.mpr hi)) hm

      · rintro _ ⟨i, hi, rfl⟩
        have hm : f i ∈ span 𝕜 (f '' Iic i) := subset_span ⟨i, le_rfl, rfl⟩
        rw [← (ih i (mem_Iio.mp hi)).1] at hm

        exact span_mono (image_mono (Iic_subset_Iio.mpr hi)) hm

    have hs : (∑ i ∈ Finset.Iio j, innerComponent (𝕜 := 𝕜) (f j) (g i) • g i) ∈
        span 𝕜 (g '' Iio j) := by
      apply Submodule.sum_mem
      intro i hi
      exact smul_mem _ _ (subset_span ⟨i, Finset.mem_Iio.mp hi, rfl⟩)

    have hgj : g j ∈ span 𝕜 (f '' Iic j) := by
      dsimp only [g]
      rw [gramSchmidt_step (𝕜 := 𝕜)]
      exact (span 𝕜 (f '' Iic j)).sub_mem (subset_span ⟨j, le_rfl, rfl⟩)
        (span_mono (image_mono Iio_subset_Iic_self) (hlo ▸ hs))

    have hfj : f j ∈ span 𝕜 (g '' Iic j) := by
      have he : f j = g j + ∑ i ∈ Finset.Iio j,
          innerComponent (𝕜 := 𝕜) (f j) (g i) • g i := by
        dsimp only [g]
        rw [gramSchmidt_step (𝕜 := 𝕜), sub_add_cancel]

      rw [he]
      exact (span 𝕜 (g '' Iic j)).add_mem (subset_span ⟨j, le_rfl, rfl⟩)
        (span_mono (image_mono Iio_subset_Iic_self) hs)

    refine ⟨span_eq_span ?_ ?_, hlo⟩

    · rintro _ ⟨i, hi, rfl⟩
      rcases hi.eq_or_lt with rfl | hi

      · exact hgj

      · exact span_mono (image_mono Iio_subset_Iic_self)
          (hlo ▸ subset_span ⟨i, hi, rfl⟩)

    · rintro _ ⟨i, hi, rfl⟩
      rcases hi.eq_or_lt with rfl | hi

      · exact hfj

      · exact span_mono (image_mono Iio_subset_Iic_self)
          (hlo.symm ▸ subset_span ⟨i, hi, rfl⟩)

/-- Theorem: Gram–Schmidt preserves the span of the entire family. -/
theorem gramSchmidt_span (f : ι → E) :
    span 𝕜 (range (InnerProductSpace.gramSchmidt 𝕜 f)) = span 𝕜 (range f) := by
  apply span_eq_span

  · rintro _ ⟨i, rfl⟩
    have hi : InnerProductSpace.gramSchmidt 𝕜 f i ∈
        span 𝕜 (InnerProductSpace.gramSchmidt 𝕜 f '' Iic i) :=
      subset_span ⟨i, le_rfl, rfl⟩
    rw [(gramSchmidt_span_initial (𝕜 := 𝕜) f i).1] at hi
    exact span_mono (image_subset_range f (Iic i)) hi

  · rintro _ ⟨i, rfl⟩
    have hi : f i ∈ span 𝕜 (f '' Iic i) := subset_span ⟨i, le_rfl, rfl⟩
    rw [← (gramSchmidt_span_initial (𝕜 := 𝕜) f i).1] at hi
    exact span_mono (image_subset_range _ (Iic i)) hi

/-- Theorem: independent input vectors give nonzero Gram–Schmidt vectors. -/
theorem gramSchmidt_ne_zero (f : ι → E) (hf : LinearIndependent 𝕜 f) (j : ι) :
    InnerProductSpace.gramSchmidt 𝕜 f j ≠ 0 := by
  intro hz

  have hm : f j ∈ span 𝕜 (f '' Iio j) := by
    have he : f j = ∑ i ∈ Finset.Iio j,
        innerComponent (𝕜 := 𝕜) (f j) (InnerProductSpace.gramSchmidt 𝕜 f i) •
          InnerProductSpace.gramSchmidt 𝕜 f i := by
      have hs := gramSchmidt_step (𝕜 := 𝕜) f j
      rw [hz] at hs
      exact sub_eq_zero.mp hs.symm

    rw [he, ← (gramSchmidt_span_initial (𝕜 := 𝕜) f j).2]
    apply Submodule.sum_mem
    intro i hi
    exact smul_mem _ _ (subset_span ⟨i, Finset.mem_Iio.mp hi, rfl⟩)

  exact hf.notMem_span_image (by simp only [mem_Iio, lt_self_iff_false, not_false_eq_true]) hm

/-- Definition: the orthogonal basis obtained by Gram–Schmidt. -/
noncomputable def orthogonalizedBasis (b : Basis ι 𝕜 E) : Basis ι 𝕜 E :=
  Basis.mk (orthogonal_linearIndependent _ (gramSchmidt_orthogonal (𝕜 := 𝕜) b)
    (gramSchmidt_ne_zero (𝕜 := 𝕜) b b.linearIndependent))
    ((gramSchmidt_span (𝕜 := 𝕜) b).trans b.span_eq).ge

/-- Theorem: the constructed basis is perpendicular. -/
theorem orthogonalizedBasis_orthogonal (b : Basis ι 𝕜 E) :
    Pairwise fun i j => ⟪orthogonalizedBasis b i, orthogonalizedBasis b j⟫ = 0 := by
  rw [orthogonalizedBasis, Basis.coe_mk]
  exact gramSchmidt_orthogonal (𝕜 := 𝕜) b

/-- Definition: normalize each vector of the constructed orthogonal basis. -/
noncomputable def normalizedBasis (b : Basis ι 𝕜 E) : Basis ι 𝕜 E :=
  (orthogonalizedBasis b).unitsSMul fun i =>
    Units.mk0 ((‖orthogonalizedBasis b i‖ : 𝕜)⁻¹)
      (inv_ne_zero (RCLike.ofReal_ne_zero.mpr
        (norm_ne_zero_iff.mpr ((orthogonalizedBasis b).ne_zero i))))

/-- Theorem: normalization produces an orthonormal basis. -/
theorem normalizedBasis_orthonormal (b : Basis ι 𝕜 E) :
    Orthonormal 𝕜 (normalizedBasis b) := by
  constructor

  · intro i
    rw [normalizedBasis, Basis.unitsSMul_apply]
    change ‖(‖orthogonalizedBasis b i‖ : 𝕜)⁻¹ • orthogonalizedBasis b i‖ = 1
    rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr ((orthogonalizedBasis b).ne_zero i))]

  · intro i j hij
    rw [normalizedBasis, Basis.unitsSMul_apply, Basis.unitsSMul_apply]
    change ⟪(‖orthogonalizedBasis b i‖ : 𝕜)⁻¹ • orthogonalizedBasis b i,
      (‖orthogonalizedBasis b j‖ : 𝕜)⁻¹ • orthogonalizedBasis b j⟫ = 0
    rw [inner_smul_left, inner_smul_right, orthogonalizedBasis_orthogonal b hij,
      mul_zero, mul_zero]

/-- Corollary: every finite-dimensional real or complex inner-product space has an orthonormal
basis. -/
theorem exists_orthonormal_basis [Module.Finite 𝕜 E] :
    ∃ b : Basis (Fin (finrank 𝕜 E)) 𝕜 E, Orthonormal 𝕜 b :=
  ⟨normalizedBasis (Chapter01.finiteBasis), normalizedBasis_orthonormal _⟩

end LinearAlgebra.Chapter05
