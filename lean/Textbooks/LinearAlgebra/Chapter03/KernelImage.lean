import Textbooks.LinearAlgebra.Chapter03.LinearMappings

namespace LinearAlgebra.Chapter03

open Chapter01

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Proposition: linear maps preserve subtraction. -/
theorem map_sub (f : V →ₗ[K] W) (x y : V) : f (x - y) = f x - f y := by
  apply add_right_cancel (b := f y)
  rw [← f.map_add, sub_add_cancel, sub_add_cancel]

/-- Definition: the kernel as a subspace, with its closure proof. -/
def kernelSubspace (f : V →ₗ[K] W) : Submodule K V :=
  subspaceOfClosed {x | f x = 0} (map_zero f)
    (fun x hx y hy => by change f (x + y) = 0; rw [f.map_add, hx, hy, add_zero])
    (fun c x hx => by change f (c • x) = 0; rw [f.map_smul, hx, scalar_smul_zero])

/-- Proposition: the constructed kernel is the standard kernel. -/
theorem kernelSubspace_eq_ker (f : V →ₗ[K] W) : kernelSubspace f = LinearMap.ker f := rfl

/-- Definition: the image as a subspace, with its closure proof. -/
def imageSubspace (f : V →ₗ[K] W) : Submodule K W :=
  subspaceOfClosed (Set.range f) ⟨0, map_zero f⟩
    (fun _ ⟨x, hx⟩ _ ⟨y, hy⟩ => ⟨x + y, by rw [f.map_add, hx, hy]⟩)
    (fun c _ ⟨x, hx⟩ => ⟨c • x, by rw [f.map_smul, hx]⟩)

/-- Proposition: the constructed image is the standard range. -/
theorem imageSubspace_eq_range (f : V →ₗ[K] W) : imageSubspace f = LinearMap.range f := rfl

/-- Theorem: a linear map is injective exactly when its kernel is zero. -/
theorem ker_eq_bot_iff_injective (f : V →ₗ[K] W) :
    LinearMap.ker f = ⊥ ↔ Function.Injective f := by
  constructor
  · intro h x y he
    have hm : x - y ∈ LinearMap.ker f := by
      change f (x - y) = 0
      rw [map_sub, he, sub_self]
    rw [h, Submodule.mem_bot] at hm
    exact sub_eq_zero.mp hm
  · intro h
    apply bot_unique
    intro x hx
    exact h (hx.trans (map_zero f).symm)

/-- Theorem: an injective linear map preserves linear independence. -/
theorem independent_map {ι : Type*} [Fintype ι] (f : V →ₗ[K] W) (hf : Function.Injective f)
    {v : ι → V} (hv : LinearIndependent K v) : LinearIndependent K (fun i => f (v i)) := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  apply Fintype.linearIndependent_iff.mp hv a _ i
  change linearCombination v a = 0
  apply hf
  rw [map_zero, map_combination]
  exact ha

/-- Proposition: a linear map is surjective exactly when its image is the target. -/
theorem range_eq_top_iff_surjective (f : V →ₗ[K] W) :
    LinearMap.range f = ⊤ ↔ Function.Surjective f := by
  constructor
  · intro h y
    have hy : y ∈ LinearMap.range f := by rw [h]; trivial
    exact hy
  · intro h
    apply top_unique
    intro y _
    exact h y

/-- Theorem: a bijective linear map sends a finite basis to a finite basis. -/
theorem basis_map {ι : Type*} [Fintype ι] (f : V →ₗ[K] W) (hf : Function.Bijective f)
    {v : ι → V} (hv : IsFiniteBasis (K := K) v) : IsFiniteBasis (K := K) (fun i => f (v i)) := by
  refine ⟨independent_map f hf.1 hv.1, ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := hf.2 y
  obtain ⟨a, ha⟩ := hv.2 x
  exact ⟨a, (map_combination f v a).symm.trans (congrArg f ha)⟩

/-- Theorem: bijective linear maps preserve finite dimension. -/
theorem finrank_eq_of_bijective [Module.Finite K V] (f : V →ₗ[K] W)
    (hf : Function.Bijective f) : Module.finrank K V = Module.finrank K W := by
  obtain ⟨s, hs⟩ := hasFiniteBasis_iff_finite.mpr (inferInstance : Module.Finite K V)
  have hb : IsFiniteBasis (K := K) (fun x : s => (x : V)) :=
    isFiniteBasis_coe_of_isBasisOf hs
  obtain ⟨b, _⟩ := (finiteBasis_iff _).mp (basis_map f hf hb)
  rw [← dimension_eq_finrank ⟨s, hs⟩, dimension_eq_card ⟨s, hs⟩ hs,
    Module.finrank_eq_card_basis b, Fintype.card_coe]

/-- Lemma: a subspace has a finite generating structure from its constructed basis. -/
theorem finite_subspace [Module.Finite K V] (S : Submodule K V) : Module.Finite K S := by
  obtain ⟨t, ht⟩ := hasFiniteBasis_iff_finite.mpr (inferInstance : Module.Finite K V)
  obtain ⟨s, hs, _⟩ := subspace_has_basis t ht.2 S
  exact Module.Finite.of_basis (subspaceBasis hs)

end LinearAlgebra.Chapter03
