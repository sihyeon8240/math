import Textbooks.LinearAlgebra.Chapter03.Composition
import Textbooks.LinearAlgebra.Chapter03.RankNullity

/-!
Isomorphic vector spaces: mathematical results from the Chapter III supplement.
Isomorphisms use `LinearEquiv`, and isomorphic spaces use `Nonempty (U ≃ₗ[K] V)`.
Dimension results use the book's finite basis and rank-nullity proofs, without
assuming arbitrary-dimensional basis existence.
-/

set_option autoImplicit false

namespace LinearAlgebra.Chapter03

open Chapter01

variable {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Proposition: every vector space is isomorphic to itself. -/
theorem isomorphic_refl : Nonempty (U ≃ₗ[K] U) := ⟨LinearEquiv.refl K U⟩

/-- Proposition: being isomorphic is symmetric. -/
theorem isomorphic_symm (h : Nonempty (U ≃ₗ[K] V)) : Nonempty (V ≃ₗ[K] U) := by
  obtain ⟨e⟩ := h
  exact ⟨e.symm⟩

/-- Proposition: being isomorphic is transitive. -/
theorem isomorphic_trans (h : Nonempty (U ≃ₗ[K] V)) (h' : Nonempty (V ≃ₗ[K] W)) :
    Nonempty (U ≃ₗ[K] W) := by
  obtain ⟨e⟩ := h
  obtain ⟨f⟩ := h'
  exact ⟨e.trans f⟩

/-- Proposition: the inverse of a composite reverses the order. -/
theorem trans_symm (e : U ≃ₗ[K] V) (f : V ≃ₗ[K] W) :
    (e.trans f).symm = f.symm.trans e.symm := rfl

/-- Theorem: a finite-dimensional space is isomorphic to its
coordinate space, using a locally constructed finite basis. -/
theorem nonempty_coordinate_equiv [Module.Finite K V] :
    Nonempty ((Fin (Module.finrank K V) → K) ≃ₗ[K] V) := by
  classical
  obtain ⟨s, hs⟩ := hasFiniteBasis_iff_finite.mpr (inferInstance : Module.Finite K V)
  have hc : Fintype.card s = Module.finrank K V := by
    rw [Fintype.card_coe, ← dimension_eq_finrank ⟨s, hs⟩, dimension_eq_card ⟨s, hs⟩ hs]
  let b := (basisOfSet hs).reindex (Fintype.equivFinOfCardEq hc)
  exact ⟨combinationEquiv ((finiteBasis_iff b).mpr ⟨b, rfl⟩)⟩

/-- Proposition: finite-dimensional spaces are isomorphic exactly
when their dimensions agree. This is the field specialization of
`FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq`, proved here from local bases. -/
theorem isomorphic_iff_finrank_eq [Module.Finite K U] [Module.Finite K V] :
    Nonempty (U ≃ₗ[K] V) ↔ Module.finrank K U = Module.finrank K V := by
  constructor
  · rintro ⟨e⟩
    exact finrank_eq_of_bijective e.toLinearMap e.bijective
  · intro h
    obtain ⟨e⟩ := nonempty_coordinate_equiv (K := K) (V := U)
    obtain ⟨f⟩ := nonempty_coordinate_equiv (K := K) (V := V)
    rw [← h] at f
    exact ⟨e.symm.trans f⟩

/-- Proposition: a given linear map underlies an isomorphism
exactly when it is bijective. -/
theorem exists_linearEquiv_iff_bijective (f : U →ₗ[K] V) :
    (∃ e : U ≃ₗ[K] V, e.toLinearMap = f) ↔ Function.Bijective f := by
  constructor
  · rintro ⟨e, rfl⟩
    exact e.bijective
  · intro h
    obtain ⟨g, hgf, hfg⟩ := (hasInverse_iff_bijective f).mpr h
    exact ⟨isomorphismOfInverse f g hgf hfg, rfl⟩

/-- Proposition: in equal finite dimensions, a zero kernel is
necessary and sufficient for a given map to be an isomorphism. -/
theorem exists_linearEquiv_iff_ker_eq_bot [Module.Finite K U] [Module.Finite K V]
    (f : U →ₗ[K] V) (h : Module.finrank K U = Module.finrank K V) :
    (∃ e : U ≃ₗ[K] V, e.toLinearMap = f) ↔ LinearMap.ker f = ⊥ := by
  rw [exists_linearEquiv_iff_bijective, ker_eq_bot_iff_injective]
  exact ⟨fun hb => hb.1, bijective_of_injective_of_finrank_eq f h⟩

/-- Proposition: in equal finite dimensions, full image is
necessary and sufficient for a given map to be an isomorphism. -/
theorem exists_linearEquiv_iff_range_eq_top [Module.Finite K U] [Module.Finite K V]
    (f : U →ₗ[K] V) (h : Module.finrank K U = Module.finrank K V) :
    (∃ e : U ≃ₗ[K] V, e.toLinearMap = f) ↔ LinearMap.range f = ⊤ := by
  rw [exists_linearEquiv_iff_bijective, range_eq_top_iff_surjective]
  exact ⟨fun hb => hb.2, bijective_of_surjective_of_finrank_eq f h⟩

/-- Proposition: an isomorphism preserves and reflects the
linear independence of a finite family. -/
theorem independent_equiv_iff {ι : Type*} [Fintype ι] (e : U ≃ₗ[K] V) (v : ι → U) :
    LinearIndependent K (fun i => e (v i)) ↔ LinearIndependent K v := by
  constructor
  · intro h
    simpa only [LinearEquiv.coe_coe, e.symm_apply_apply] using independent_map e.symm.toLinearMap e.symm.injective h
  · exact independent_map e.toLinearMap e.injective

/-- Lemma: linear maps send spans into spans of images,
by induction on the construction of the span. -/
theorem apply_mem_span_image (f : U →ₗ[K] V) (S : Set U) {x : U}
    (hx : x ∈ Submodule.span K S) : f x ∈ Submodule.span K (f '' S) := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [f.map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [f.map_smul]; exact Submodule.smul_mem _ c hx

/-- Proposition: an isomorphism takes the span of a set onto
the span of its image, including empty and infinite generating sets. This is
the set-image form of `Submodule.map_span` for a linear equivalence. -/
theorem image_span_equiv (e : U ≃ₗ[K] V) (S : Set U) :
    e '' (Submodule.span K S : Set U) = (Submodule.span K (e '' S) : Set V) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact apply_mem_span_image e.toLinearMap S hx
  · intro y hy
    have hS : e.symm '' (e '' S) = S := by
      ext x
      constructor
      · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        simpa only [LinearEquiv.coe_coe, e.symm_apply_apply] using hz
      · intro hx
        exact ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩
    have hx := apply_mem_span_image e.symm.toLinearMap (e '' S) hy
    change e.symm y ∈ Submodule.span K (e.symm '' (e '' S)) at hx
    rw [hS] at hx
    exact ⟨e.symm y, hx, e.apply_symm_apply y⟩

/-- Proposition: a set spans the domain exactly when its image
under an isomorphism spans the codomain. -/
theorem span_image_eq_top_iff (e : U ≃ₗ[K] V) (S : Set U) :
    Submodule.span K (e '' S) = ⊤ ↔ Submodule.span K S = ⊤ := by
  constructor
  · intro h
    apply top_unique
    intro x _
    have hx : e x ∈ (Submodule.span K (e '' S) : Set V) := by rw [h]; trivial
    rw [← image_span_equiv] at hx
    obtain ⟨z, hz, he⟩ := hx
    exact e.injective he ▸ hz
  · intro h
    apply top_unique
    intro y _
    change y ∈ (Submodule.span K (e '' S) : Set V)
    rw [← image_span_equiv]
    exact ⟨e.symm y, by rw [h]; trivial, e.apply_symm_apply y⟩

/-- Proposition: an isomorphism preserves and reflects finite bases. -/
theorem basis_equiv_iff {ι : Type*} [Fintype ι] (e : U ≃ₗ[K] V) (v : ι → U) :
    IsFiniteBasis (K := K) (fun i => e (v i)) ↔ IsFiniteBasis (K := K) v := by
  constructor
  · intro h
    simpa only [LinearEquiv.coe_coe, e.symm_apply_apply] using basis_map e.symm.toLinearMap e.symm.bijective h
  · exact basis_map e.toLinearMap e.bijective

/-- Definition: an isomorphism restricts to an isomorphism of a subspace onto
its image. `Submodule.map` includes the image's subspace structure. -/
def subspaceImageEquiv (e : U ≃ₗ[K] V) (S : Submodule K U) :
    S ≃ₗ[K] S.map e.toLinearMap where
  toFun x := ⟨e x, ⟨x, x.property, rfl⟩⟩
  invFun y := ⟨e.symm y, by
    obtain ⟨x, hx, he⟩ := y.property
    change e x = (y : V) at he
    rw [← he, e.symm_apply_apply]
    exact hx⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_add' x y := Subtype.ext (e.map_add x y)
  map_smul' c x := Subtype.ext (e.map_smul c x)

/-- Proposition: taking subspace images and then inverse images
recovers the original subspace. -/
theorem map_symm_map (e : U ≃ₗ[K] V) (S : Submodule K U) :
    (S.map e.toLinearMap).map e.symm.toLinearMap = S := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, he⟩
    change e.symm (e z) = x at he
    rw [e.symm_apply_apply] at he
    exact he ▸ hz
  · intro hx
    exact ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩

/-- Proposition: an isomorphism preserves the dimension of any
finite-dimensional subspace, even in an infinite-dimensional ambient space. -/
theorem finrank_map_equiv (e : U ≃ₗ[K] V) (S : Submodule K U) [Module.Finite K S] :
    Module.finrank K (S.map e.toLinearMap) = Module.finrank K S :=
  (finrank_eq_of_bijective (subspaceImageEquiv e S).toLinearMap
    (subspaceImageEquiv e S).bijective).symm

/-- Proposition: precomposition pulls back the kernel. -/
theorem ker_comp_equiv (e : U ≃ₗ[K] V) (L : V →ₗ[K] W) :
    LinearMap.ker (L.comp e.toLinearMap) = (LinearMap.ker L).comap e.toLinearMap := rfl

/-- Proposition: precomposition by an isomorphism preserves the image. -/
theorem range_comp_equiv (e : U ≃ₗ[K] V) (L : V →ₗ[K] W) :
    LinearMap.range (L.comp e.toLinearMap) = LinearMap.range L := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e x, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨e.symm v, by change L (e (e.symm v)) = L v; rw [e.apply_symm_apply]⟩

/-- Proposition: postcomposition by an isomorphism preserves the kernel. -/
theorem ker_equiv_comp (e : U ≃ₗ[K] V) (M : W →ₗ[K] U) :
    LinearMap.ker (e.toLinearMap.comp M) = LinearMap.ker M := by
  ext x
  change e (M x) = 0 ↔ M x = 0
  constructor
  · intro h
    exact e.injective (h.trans e.map_zero.symm)
  · intro h
    rw [h, e.map_zero]

/-- Proposition: postcomposition takes the image to its isomorphic image. -/
theorem range_equiv_comp (e : U ≃ₗ[K] V) (M : W →ₗ[K] U) :
    LinearMap.range (e.toLinearMap.comp M) = (LinearMap.range M).map e.toLinearMap := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨M x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩

/-- Lemma: the pulled-back kernel is the image under the inverse. -/
theorem ker_comp_equiv_eq_map_symm (e : U ≃ₗ[K] V) (L : V →ₗ[K] W) :
    LinearMap.ker (L.comp e.toLinearMap) = (LinearMap.ker L).map e.symm.toLinearMap := by
  ext x
  constructor
  · intro hx
    exact ⟨e x, hx, e.symm_apply_apply x⟩
  · rintro ⟨v, hv, rfl⟩
    change L (e (e.symm v)) = 0
    rw [e.apply_symm_apply]
    exact hv

/-- Corollary: precomposition preserves finite kernel dimension. -/
theorem finrank_ker_comp_equiv (e : U ≃ₗ[K] V) (L : V →ₗ[K] W)
    [Module.Finite K (LinearMap.ker L)] :
    Module.finrank K (LinearMap.ker (L.comp e.toLinearMap)) =
      Module.finrank K (LinearMap.ker L) := by
  rw [ker_comp_equiv_eq_map_symm]
  exact finrank_map_equiv e.symm _

/-- Corollary: precomposition preserves image dimension. -/
theorem finrank_range_comp_equiv (e : U ≃ₗ[K] V) (L : V →ₗ[K] W) :
    Module.finrank K (LinearMap.range (L.comp e.toLinearMap)) =
      Module.finrank K (LinearMap.range L) := by rw [range_comp_equiv]

/-- Corollary: postcomposition preserves kernel dimension. -/
theorem finrank_ker_equiv_comp (e : U ≃ₗ[K] V) (M : W →ₗ[K] U) :
    Module.finrank K (LinearMap.ker (e.toLinearMap.comp M)) =
      Module.finrank K (LinearMap.ker M) := by rw [ker_equiv_comp]

/-- Corollary: postcomposition preserves finite image dimension. -/
theorem finrank_range_equiv_comp (e : U ≃ₗ[K] V) (M : W →ₗ[K] U)
    [Module.Finite K (LinearMap.range M)] :
    Module.finrank K (LinearMap.range (e.toLinearMap.comp M)) =
      Module.finrank K (LinearMap.range M) := by
  rw [range_equiv_comp]
  exact finrank_map_equiv e _

end LinearAlgebra.Chapter03
