import Textbooks.LinearAlgebra.Chapter01.Dimension

namespace LinearAlgebra.Chapter01

open Submodule Set
open scoped BigOperators

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Definition: the sum of subspaces, with its closure proof. -/
def sumSubspace (U W : Submodule K V) : Submodule K V :=
  subspaceOfClosed {x | ∃ u ∈ U, ∃ w ∈ W, u + w = x}
    ⟨0, U.zero_mem, 0, W.zero_mem, add_zero _⟩
    (by
      rintro _ ⟨u, hu, w, hw, rfl⟩ _ ⟨u', hu', w', hw', rfl⟩
      exact ⟨u + u', U.add_mem hu hu', w + w', W.add_mem hw hw', by abel⟩)
    (by
      rintro c _ ⟨u, hu, w, hw, rfl⟩
      exact ⟨c • u, U.smul_mem c hu, c • w, W.smul_mem c hw, (smul_add c u w).symm⟩)

/-- Theorem: the sum is the smallest subspace containing both summands. -/
theorem sum_eq_sup (U W : Submodule K V) : sumSubspace U W = U ⊔ W := by
  apply le_antisymm

  · rintro x ⟨u, hu, w, hw, rfl⟩
    exact (U ⊔ W).add_mem
      ((show U ≤ U ⊔ W from le_sup_left) hu)
      ((show W ≤ U ⊔ W from le_sup_right) hw)

  · apply sup_le
    · intro u hu
      exact ⟨u, hu, 0, W.zero_mem, add_zero _⟩

    · intro w hw
      exact ⟨0, U.zero_mem, w, hw, zero_add _⟩

/-- Definition: every vector has a unique decomposition into the two subspaces. -/
def IsDirectSum (U W : Submodule K V) : Prop :=
  ∀ x : V, ∃! p : U × W, (p.1 : V) + (p.2 : V) = x

/-- Theorem: a spanning sum with zero intersection is direct. -/
theorem directSum_of_sup_inf (U W : Submodule K V) (hspan : U ⊔ W = ⊤)
    (hzero : U ⊓ W = ⊥) : IsDirectSum U W := by
  intro x

  have hx : x ∈ U ⊔ W := by
    rw [hspan]
    trivial

  obtain ⟨u, hu, w, hw, he⟩ := mem_sup.mp hx

  refine ⟨(⟨u, hu⟩, ⟨w, hw⟩), he, ?_⟩
  rintro ⟨u', w'⟩ he'

  have hd : (u' : V) - u = w - (w' : V) := by
    have : (u' : V) + (w' : V) = u + w := he'.trans he.symm

    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [add_comm] using this

  have hm : (u' : V) - u ∈ U ⊓ W :=
    ⟨U.sub_mem u'.property hu, hd ▸ W.sub_mem hw w'.property⟩

  rw [hzero, mem_bot] at hm

  have hu' : (u' : V) = u := sub_eq_zero.mp hm

  have hw' : (w' : V) = w := by
    apply add_left_cancel (a := u)
    simpa only [hu'] using he'.trans he.symm

  exact Prod.ext (Subtype.ext hu') (Subtype.ext hw')

/-- Theorem: a direct decomposition spans and has zero intersection. -/
theorem directSum_sup_inf {U W : Submodule K V} (h : IsDirectSum U W) :
    U ⊔ W = ⊤ ∧ U ⊓ W = ⊥ := by
  constructor

  · apply top_unique
    intro x _

    obtain ⟨p, hp, _⟩ := h x

    exact mem_sup.mpr ⟨p.1, p.1.property, p.2, p.2.property, hp⟩

  · apply bot_unique
    intro x hx

    obtain ⟨p, _, hp⟩ := h x

    have h1 := hp (⟨x, hx.1⟩, 0) (by simp only [Submodule.coe_zero, add_zero])

    have h2 := hp (0, ⟨x, hx.2⟩) (by simp only [Submodule.coe_zero, zero_add])

    have he := congrArg (fun q : U × W => (q.1 : V)) (h1.trans h2.symm)

    exact he

/-- Theorem: the direct-sum criterion in both directions. -/
theorem directSum_iff (U W : Submodule K V) :
    IsDirectSum U W ↔ U ⊔ W = ⊤ ∧ U ⊓ W = ⊥ :=
  ⟨directSum_sup_inf, fun h => directSum_of_sup_inf U W h.1 h.2⟩

/-- Lemma: spans of disjoint parts of an independent set have zero intersection. -/
theorem independent_disjoint_spans {s t : Set V} (hi : LinearIndepOn K id (s ∪ t))
    (hd : Disjoint s t) : span K s ⊓ span K t = ⊥ := by
  classical

  apply bot_unique
  intro x hx

  have hs : x ∈ span K (id '' s) := by
    simpa only [image_id, SetLike.mem_coe] using hx.1

  have ht : x ∈ span K (id '' t) := by
    simpa only [image_id, SetLike.mem_coe] using hx.2

  obtain ⟨a, ha, hea⟩ := (Finsupp.mem_span_image_iff_linearCombination K).mp hs
  obtain ⟨b, hb, heb⟩ := (Finsupp.mem_span_image_iff_linearCombination K).mp ht

  have has : a ∈ Finsupp.supported K K (s ∪ t) :=
    (Finsupp.mem_supported K a).mpr ((Finsupp.mem_supported K a).mp ha |>.trans subset_union_left)

  have hbt : b ∈ Finsupp.supported K K (s ∪ t) :=
    (Finsupp.mem_supported K b).mpr ((Finsupp.mem_supported K b).mp hb |>.trans subset_union_right)

  have he := linearIndepOn_iffₛ.mp hi a has b hbt (hea.trans heb.symm)

  have haz : a = 0 := by
    ext y
    by_cases hy : y ∈ s

    · rw [he]
      exact (Finsupp.mem_supported' K b).mp hb y (fun hyt => Set.disjoint_left.mp hd hy hyt)

    · exact (Finsupp.mem_supported' K a).mp ha y hy

  rw [haz, map_zero] at hea
  exact hea.symm

/-- Theorem: every subspace of a finite-dimensional space has a complement. -/
theorem exists_complement [Module.Finite K V] (W : Submodule K V) :
    ∃ U : Submodule K V, IsDirectSum W U := by
  classical

  obtain ⟨b, hb⟩ := hasFiniteBasis_iff_finite.mpr (inferInstance : Module.Finite K V)
  obtain ⟨s, hs, _⟩ := subspace_has_basis b hb.2 W

  obtain ⟨t, hst, ht, _⟩ := extend_to_basis s hs.1

  refine ⟨span K (↑(t \ s) : Set V), directSum_of_sup_inf _ _ ?_ ?_⟩

  · rw [← hs.2, ← span_union, ← Finset.coe_union, Finset.union_sdiff_of_subset hst, ht.2]
  · rw [← hs.2]
    apply independent_disjoint_spans

    · simpa only [← Finset.coe_union, Finset.union_sdiff_of_subset hst] using ht.1
    · exact Set.disjoint_left.mpr fun x hx hxt => (Finset.mem_sdiff.mp hxt).2 hx

/-- Lemma: an independent set contains no zero vector. -/
theorem independent_zero_not_mem {s : Set V} (hs : LinearIndepOn K id s) : (0 : V) ∉ s := by
  intro h
  exact independent_not_mem_span hs (empty_subset s) h (notMem_empty _) (zero_mem _)

/-- Lemma: bases of subspaces with zero intersection are disjoint. -/
private theorem disjoint_basis_sets {s t : Finset V} {U W : Submodule K V}
    (hs : IsBasisOf s U) (ht : IsBasisOf t W) (hz : U ⊓ W = ⊥) : Disjoint s t := by
  apply Finset.disjoint_left.mpr
  intro x hxs hxt

  have hx : x ∈ U ⊓ W := ⟨hs.2 ▸ subset_span hxs, ht.2 ▸ subset_span hxt⟩

  rw [hz, mem_bot] at hx
  exact independent_zero_not_mem hs.1 (hx ▸ hxs)

/-- Theorem: the union of bases of subspaces with zero intersection
is a basis of their sum. -/
theorem union_is_basis [DecidableEq V] {s t : Finset V} {U W : Submodule K V}
    (hs : IsBasisOf s U) (ht : IsBasisOf t W) (hz : U ⊓ W = ⊥) :
    IsBasisOf (s ∪ t) (U ⊔ W) := by
  classical

  have hd : Disjoint s t := disjoint_basis_sets hs ht hz

  refine ⟨linearIndepOn_finset_iff.mpr ?_, ?_⟩

  · intro a ha x hx
    change ∑ y ∈ s ∪ t, a y • y = 0 at ha
    rw [Finset.sum_union hd] at ha

    have hsm : (∑ y ∈ s, a y • y) ∈ U := by
      exact U.sum_mem fun y hy => U.smul_mem _ (hs.2 ▸ subset_span hy)

    have htm : (∑ y ∈ t, a y • y) ∈ W := by
      exact W.sum_mem fun y hy => W.smul_mem _ (ht.2 ▸ subset_span hy)

    have hsz : (∑ y ∈ s, a y • y) = 0 := by
      have hm : (∑ y ∈ s, a y • y) ∈ U ⊓ W :=
        ⟨hsm, (eq_neg_of_add_eq_zero_left ha) ▸ W.neg_mem htm⟩

      simpa only [hz, mem_bot] using hm

    have htz : (∑ y ∈ t, a y • y) = 0 := by
      simpa only [hsz, zero_add] using ha

    rcases Finset.mem_union.mp hx with hx | hx

    · exact linearIndepOn_finset_iff.mp hs.1 a hsz x hx
    · exact linearIndepOn_finset_iff.mp ht.1 a htz x hx
  · rw [Finset.coe_union, span_union, hs.2, ht.2]

/-- Theorem: dimensions add in a finite-dimensional direct sum. -/
theorem finrank_directSum [Module.Finite K V] {U W : Submodule K V}
    (h : IsDirectSum U W) : Module.finrank K V = Module.finrank K U + Module.finrank K W := by
  classical

  obtain ⟨b, hb⟩ := hasFiniteBasis_iff_finite.mpr (inferInstance : Module.Finite K V)
  obtain ⟨s, hs, _⟩ := subspace_has_basis b hb.2 U

  obtain ⟨t, ht, _⟩ := subspace_has_basis b hb.2 W
  obtain ⟨hsp, hz⟩ := directSum_sup_inf h

  have hu : IsBasisOf (s ∪ t) (⊤ : Submodule K V) := hsp ▸ union_is_basis hs ht hz

  have hd : Disjoint s t := disjoint_basis_sets hs ht hz

  rw [← dimension_eq_finrank ⟨s ∪ t, hu⟩, dimension_eq_card ⟨s ∪ t, hu⟩ hu,
    finrank_eq_card_of_basisOf hs, finrank_eq_card_of_basisOf ht, Finset.card_union_of_disjoint hd]

/-- Definition: the direct product of two vector spaces, with pointwise operations. -/
abbrev DirectProduct (U W : Type*) := U × W

/-- Definition: the direct product of a finite family of vector spaces. -/
abbrev FiniteProduct {ι : Type*} (W : ι → Type*) := ∀ i, W i

/-- Definition: a finite family of subspaces gives a unique sum decomposition. -/
def IsFiniteDirectSum {ι : Type*} [Fintype ι] (W : ι → Submodule K V) : Prop :=
  ∀ x : V, ∃! p : ∀ i, W i, ∑ i, (p i : V) = x

end LinearAlgebra.Chapter01
