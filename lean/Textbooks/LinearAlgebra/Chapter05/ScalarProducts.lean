import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.QuadraticForm.Basic

namespace LinearAlgebra.Chapter05

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Definition: a scalar product is a symmetric bilinear form. -/
abbrev ScalarProduct (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :=
  {B : LinearMap.BilinForm K V // B.IsSymm}

/-- Definition: vectors perpendicular to every member of a set. -/
def orthogonalSpace (B : LinearMap.BilinForm K V) (S : Set V) : Submodule K V where
  carrier := {w | ∀ v ∈ S, B v w = 0}
  zero_mem' := by
    intro v _
    exact map_zero (B v)
  add_mem' := by
    intro x y hx hy v hv
    rw [map_add, hx v hv, hy v hv, add_zero]
  smul_mem' := by
    intro c x hx v hv
    rw [map_smul, hx v hv, smul_zero]

/-- Proposition: orthogonality to a set is orthogonality to its span. -/
theorem orthogonalSpace_span (B : LinearMap.BilinForm K V) (S : Set V) :
    orthogonalSpace B (Submodule.span K S : Set V) = orthogonalSpace B S := by
  ext w
  constructor

  · intro h v hv
    exact h v (Submodule.subset_span hv)

  · intro h v hv
    refine Submodule.span_induction (fun x hx => h x hx) ?_ ?_ ?_ hv

    · rw [map_zero, LinearMap.zero_apply]

    · intro x y _ _ hx hy
      rw [map_add, LinearMap.add_apply, hx, hy, add_zero]

    · intro c x _ hx
      rw [map_smul, LinearMap.smul_apply, hx, smul_zero]

/-- Proposition: positive definiteness implies nondegeneracy. -/
theorem separatingLeft_of_posDef {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : B.toQuadraticMap.PosDef) : B.SeparatingLeft := by
  intro v hv
  by_contra hn

  have hp := hB v hn
  have hz := hv v
  change 0 < B v v at hp

  linarith

/-- Definition: the component along a vector, with Lean's division convention at zero. -/
def component (B : LinearMap.BilinForm K V) (v w : V) : K := B v w / B w w

/-- Definition: projection onto the line through a vector. -/
def lineProjection (B : LinearMap.BilinForm K V) (v w : V) : V :=
  component B v w • w

/-- Proposition: subtracting the component gives a perpendicular remainder. -/
theorem sub_lineProjection_orthogonal (B : LinearMap.BilinForm K V) (v w : V)
    (hw : B w w ≠ 0) : B (v - lineProjection B v w) w = 0 := by
  simp only [lineProjection, component, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [div_mul_cancel₀ _ hw, sub_self]

/-- Theorem: the perpendicular remainder determines the component uniquely. -/
theorem exists_unique_component (B : LinearMap.BilinForm K V) (v w : V)
    (hw : B w w ≠ 0) : ∃! c : K, B (v - c • w) w = 0 := by
  refine ⟨component B v w, sub_lineProjection_orthogonal B v w hw, ?_⟩

  intro c hc
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul] at hc
  exact (eq_div_iff hw).mpr (sub_eq_zero.mp hc).symm

/-- Proposition: the diagonal of a symmetric form determines its mixed values. -/
theorem polarization (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (h2 : (2 : K) ≠ 0) (v w : V) :
    B v w = (B (v + w) (v + w) - B v v - B w w) / 2 := by
  rw [eq_div_iff h2]
  simp only [map_add, LinearMap.add_apply]
  rw [hB.eq w v]
  ring

/-- Lemma: a nonzero symmetric form has a vector of nonzero square in characteristic not two. -/
theorem exists_self_ne_zero (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (h2 : (2 : K) ≠ 0) (hn : B ≠ 0) : ∃ v, B v v ≠ 0 := by
  by_contra h
  have hz : ∀ v, B v v = 0 := by
    simpa only [not_exists, not_not] using h

  apply hn
  ext v w
  rw [polarization B hB h2, hz, hz, hz]
  simp only [sub_zero, zero_div, LinearMap.zero_apply]

/-- Proposition: multiplication by `i` negates the square of a complex bilinear form. -/
theorem complex_bilinear_self_I {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : LinearMap.BilinForm ℂ V) (v : V) :
    B (Complex.I • v) (Complex.I • v) = -B v v := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]

end LinearAlgebra.Chapter05
