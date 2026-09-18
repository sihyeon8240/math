import Textbooks.LinearAlgebra.Chapter03.KernelImage

namespace LinearAlgebra.Chapter03

open Chapter01

variable {K U V W X : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup X] [Module K X]

/-- Proposition: standard composition evaluates by successive application. -/
theorem comp_apply (g : V →ₗ[K] W) (f : U →ₗ[K] V) (x : U) :
    (g.comp f) x = g (f x) := rfl

/-- Proposition: composition of linear maps is associative. -/
theorem comp_assoc (h : W →ₗ[K] X) (g : V →ₗ[K] W) (f : U →ₗ[K] V) :
    h.comp (g.comp f) = (h.comp g).comp f := rfl

/-- Proposition: composition distributes over addition of inner maps. -/
theorem comp_add (h : V →ₗ[K] W) (f g : U →ₗ[K] V) :
    h.comp (f + g) = h.comp f + h.comp g := by
  ext x
  exact h.map_add (f x) (g x)

/-- Proposition: composition distributes over addition of outer maps. -/
theorem add_comp (g h : V →ₗ[K] W) (f : U →ₗ[K] V) :
    (g + h).comp f = g.comp f + h.comp f := rfl

/-- Theorem: composing standard powers adds their exponents.
Multiplication in `Module.End K V` is composition. -/
theorem pow_add (f : V →ₗ[K] V) (r s : ℕ) :
    f ^ (r + s) = f ^ r * f ^ s := by
  induction r with
  | zero =>
    simp only [Nat.zero_add, pow_zero, one_mul]

  | succ r ih =>
    rw [Nat.succ_add, pow_succ', ih, pow_succ', mul_assoc]

/-- Proposition: any two powers of the same operator commute. -/
theorem pow_mul_comm (f : V →ₗ[K] V) (r s : ℕ) :
    f ^ r * f ^ s = f ^ s * f ^ r := by
  rw [← pow_add, ← pow_add, Nat.add_comm]

/-- Definition: a two-sided inverse of a linear map, with its linearity proof. -/
def inverseLinear (f : U →ₗ[K] V) (g : V → U)
    (hgf : Function.LeftInverse g f) (hfg : Function.RightInverse g f) : V →ₗ[K] U := by
  have hi : Function.Injective f := ((hasInverse_iff_bijective f).mp ⟨g, hgf, hfg⟩).1

  apply linearMapOf g

  · intro x y
    apply hi
    rw [hfg, f.map_add, hfg, hfg]

  · intro c x
    apply hi
    rw [hfg, f.map_smul, hfg]

/-- Theorem: a surjective linear map with zero kernel has an inverse linear map. -/
theorem exists_inverse_linear (f : U →ₗ[K] V) (hk : LinearMap.ker f = ⊥)
    (hs : Function.Surjective f) :
    ∃ g : V →ₗ[K] U, Function.LeftInverse g f ∧ Function.RightInverse g f := by
  obtain ⟨g, hgf, hfg⟩ := (hasInverse_iff_bijective f).mpr
    ⟨(ker_eq_bot_iff_injective f).mp hk, hs⟩

  exact ⟨inverseLinear f g hgf hfg, hgf, hfg⟩

/-- Definition: a linear isomorphism from a linear map and its two-sided inverse. -/
def isomorphismOfInverse (f : U →ₗ[K] V) (g : V → U)
    (hgf : Function.LeftInverse g f) (hfg : Function.RightInverse g f) : U ≃ₗ[K] V where
  toFun := f
  invFun := g
  left_inv := hgf
  right_inv := hfg
  map_add' := f.map_add
  map_smul' := f.map_smul

/-- Definition: a finite basis gives an isomorphism from its coordinate space. -/
noncomputable def combinationEquiv {ι : Type*} [Fintype ι] {v : ι → V}
    (h : IsFiniteBasis (K := K) v) : (ι → K) ≃ₗ[K] V where
  toFun := linearCombination v
  invFun := coordinates h
  left_inv a := coefficients_unique h.1 (combination_coordinates h (linearCombination v a))
  right_inv := combination_coordinates h
  map_add' := combination_add v
  map_smul' := combination_smul v

end LinearAlgebra.Chapter03
