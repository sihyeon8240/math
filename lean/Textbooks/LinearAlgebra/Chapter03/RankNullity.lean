import Textbooks.LinearAlgebra.Chapter03.KernelImage
import Textbooks.LinearAlgebra.Chapter01.DirectSums

namespace LinearAlgebra.Chapter03

open Chapter01

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Definition: restrict a map to a subspace and regard its values as elements of its image. -/
def restrictedRangeMap (f : V →ₗ[K] W) (S : Submodule K V) : S →ₗ[K] LinearMap.range f :=
  linearMapOf (fun x => ⟨f x, ⟨x, rfl⟩⟩)
    (fun x y => Subtype.ext (f.map_add x y))
    (fun c x => Subtype.ext (f.map_smul c x))

/-- Theorem: the restriction to a complement of the kernel is bijective onto the image. -/
theorem complement_bijective (f : V →ₗ[K] W) {S : Submodule K V}
    (h : IsDirectSum (LinearMap.ker f) S) : Function.Bijective (restrictedRangeMap f S) := by
  obtain ⟨_, hinter⟩ := directSum_sup_inf h

  constructor

  · intro x y he
    apply Subtype.ext

    have hxy : f (x : V) = f (y : V) := congrArg Subtype.val he

    have hk : (x : V) - (y : V) ∈ LinearMap.ker f := by
      change f ((x : V) - (y : V)) = 0
      rw [map_sub, hxy, sub_self]

    have hm : (x : V) - (y : V) ∈ LinearMap.ker f ⊓ S := ⟨hk, S.sub_mem x.property y.property⟩

    rw [hinter, Submodule.mem_bot] at hm
    exact sub_eq_zero.mp hm

  · rintro ⟨y, x, rfl⟩

    obtain ⟨p, hp, _⟩ := h x

    refine ⟨p.2, Subtype.ext ?_⟩
    change f (p.2 : V) = f x
    rw [← hp, f.map_add, show f (p.1 : V) = 0 from p.1.property, zero_add]

/-- Theorem: the domain dimension is the sum of kernel and image dimensions. -/
theorem rank_nullity [Module.Finite K V] (f : V →ₗ[K] W) :
    Module.finrank K V =
      Module.finrank K (LinearMap.ker f) + Module.finrank K (LinearMap.range f) := by
  obtain ⟨S, hS⟩ := exists_complement (LinearMap.ker f)

  let : Module.Finite K S := finite_subspace S

  have he := finrank_eq_of_bijective (restrictedRangeMap f S) (complement_bijective f hS)

  exact (finrank_directSum hS).trans (congrArg (Module.finrank K (LinearMap.ker f) + ·) he)

/-- Lemma: the whole subspace and its ambient space have equal dimension. -/
theorem finrank_top [Module.Finite K V] :
    Module.finrank K (⊤ : Submodule K V) = Module.finrank K V := by
  obtain ⟨s, hs⟩ := hasFiniteBasis_iff_finite.mpr (inferInstance : Module.Finite K V)

  rw [finrank_eq_card_of_basisOf hs, ← dimension_eq_finrank ⟨s, hs⟩, dimension_eq_card ⟨s, hs⟩ hs]

/-- Lemma: every vector in a finite-dimensional space of dimension zero is zero. -/
theorem eq_zero_of_finrank_zero [Module.Finite K V]
    (h : Module.finrank K V = 0) (x : V) : x = 0 := by
  obtain ⟨s, hs⟩ := hasFiniteBasis_iff_finite.mpr (inferInstance : Module.Finite K V)

  have hc : s.card = 0 := by
    exact (dimension_eq_card ⟨s, hs⟩ hs).symm.trans ((dimension_eq_finrank ⟨s, hs⟩).trans h)

  have he : s = ∅ := Finset.card_eq_zero.mp hc

  have hx : x ∈ Submodule.span K (s : Set V) := by
    rw [hs.2]
    trivial

  simpa only [he, Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] using hx

/-- Lemma: a subspace containing only zero has dimension zero. -/
theorem finrank_bot : Module.finrank K (⊥ : Submodule K V) = 0 := by
  obtain ⟨s, hs, hc⟩ := zero_space_dimension (K := K) (V := (⊥ : Submodule K V))

  rw [← dimension_eq_finrank ⟨s, hs⟩, dimension_eq_card ⟨s, hs⟩ hs, hc]

/-- Theorem: between spaces of equal finite dimension, injectivity implies bijectivity. -/
theorem bijective_of_injective_of_finrank_eq [Module.Finite K V] [Module.Finite K W]
    (f : V →ₗ[K] W) (hd : Module.finrank K V = Module.finrank K W)
    (hi : Function.Injective f) : Function.Bijective f := by
  refine ⟨hi, (range_eq_top_iff_surjective f).mp ?_⟩
  apply subspace_eq_top_of_finrank_eq

  have hk := (ker_eq_bot_iff_injective f).mpr hi

  have he := rank_nullity f

  rw [hk, finrank_bot, zero_add, hd] at he
  exact he.symm

/-- Theorem: between spaces of equal finite dimension, surjectivity implies bijectivity. -/
theorem bijective_of_surjective_of_finrank_eq [Module.Finite K V] [Module.Finite K W]
    (f : V →ₗ[K] W) (hd : Module.finrank K V = Module.finrank K W)
    (hs : Function.Surjective f) : Function.Bijective f := by
  refine ⟨(ker_eq_bot_iff_injective f).mp ?_, hs⟩

  have hr := (range_eq_top_iff_surjective f).mpr hs

  have he := rank_nullity f

  rw [hr, finrank_top, hd] at he

  have hk : Module.finrank K (LinearMap.ker f) = 0 := by
    omega

  let : Module.Finite K (LinearMap.ker f) := finite_subspace (LinearMap.ker f)

  apply bot_unique
  intro x hx

  have hz := eq_zero_of_finrank_zero hk (⟨x, hx⟩ : LinearMap.ker f)

  exact congrArg Subtype.val hz

end LinearAlgebra.Chapter03
