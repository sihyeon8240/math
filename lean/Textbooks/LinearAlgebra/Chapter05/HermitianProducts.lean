import Textbooks.LinearAlgebra.Chapter05.ScalarProducts
import Textbooks.LinearAlgebra.Chapter05.PositiveDefinite

namespace LinearAlgebra.Chapter05

/-- Definition: a Hermitian product uses Mathlib's conjugate-linear first variable. -/
abbrev HermitianProduct (V : Type*) [AddCommGroup V] [Module ℂ V] :=
  {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ // H.IsSymm}

/-- Definition: the real diagonal of a Hermitian form is positive on nonzero vectors. -/
def HermitianPosDef {V : Type*} [AddCommGroup V] [Module ℂ V]
    (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) : Prop :=
  ∀ v, v ≠ 0 → 0 < (H v v).re

/-- Proposition: the diagonal of a Hermitian product is real. -/
theorem hermitian_self_im {V : Type*} [AddCommGroup V] [Module ℂ V]
    (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hH : H.IsSymm) (v : V) : (H v v).im = 0 := by
  have he := congrArg Complex.im (hH.eq v v)
  change -(H v v).im = (H v v).im at he

  linarith

/-- Definition: a positive real scalar product supplies the standard inner-product core. -/
@[instance_reducible]
def realInnerCore {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm) (hp : B.toQuadraticMap.PosDef) :
    InnerProductSpace.Core ℝ V where
  inner := fun v w => B v w
  conj_inner_symm := fun v w => hB.eq w v
  re_inner_nonneg := by
    intro v
    by_cases hv : v = 0

    · subst v
      simp only [map_zero, le_refl]

    · exact (hp v hv).le
  add_left := fun v w u => by rw [map_add, LinearMap.add_apply]
  smul_left := fun v w c => by
    rw [map_smul, LinearMap.smul_apply]
    rfl
  definite := by
    intro v hv
    by_contra hn

    have hh := hp v hn
    change 0 < B v v at hh
    rw [hv] at hh

    exact lt_irrefl _ hh

/-- Definition: a positive Hermitian product supplies the standard complex inner-product core. -/
@[instance_reducible]
def hermitianInnerCore {V : Type*} [AddCommGroup V] [Module ℂ V]
    (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hH : H.IsSymm) (hp : HermitianPosDef H) :
    InnerProductSpace.Core ℂ V where
  inner := fun v w => H v w
  conj_inner_symm := fun v w => hH.eq w v
  re_inner_nonneg := by
    intro v
    by_cases hv : v = 0

    · subst v
      simp only [map_zero, le_refl]

    · exact (hp v hv).le
  add_left := fun v w u => by rw [map_add, LinearMap.add_apply]
  smul_left := fun v w c => by
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  definite := by
    intro v hv
    by_contra hn

    have hh := hp v hn
    rw [hv, Complex.zero_re] at hh

    exact lt_irrefl _ hh

/-- Proposition: a nontrivial complex space admits no positive complex bilinear scalar product. -/
theorem not_complex_bilinear_posDef {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Nontrivial V] (B : LinearMap.BilinForm ℂ V) :
    ¬(∀ v, v ≠ 0 → 0 < (B v v).re) := by
  intro hp
  obtain ⟨v, hv⟩ := exists_ne (0 : V)

  have h1 := hp v hv
  have h2 := hp (Complex.I • v) (smul_ne_zero Complex.I_ne_zero hv)
  rw [complex_bilinear_self_I, Complex.neg_re] at h2

  linarith

/-- Proposition: a complex form linear and conjugate-linear in the same argument is zero. -/
theorem bilinear_and_conjugate_linear_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : LinearMap.BilinForm ℂ V)
    (h : ∀ v w a, B v (a • w) = star a * B v w) : B = 0 := by
  ext v w
  have he := h v w Complex.I
  rw [map_smul, smul_eq_mul, Complex.star_def, Complex.conj_I] at he

  have hz : (2 * Complex.I) * B v w = 0 := by
    linear_combination he

  exact (mul_eq_zero.mp hz).resolve_left
    (mul_ne_zero (by norm_num) Complex.I_ne_zero)

end LinearAlgebra.Chapter05
