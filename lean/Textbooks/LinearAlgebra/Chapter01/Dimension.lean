import Textbooks.LinearAlgebra.Chapter01.Exchange
import Mathlib.LinearAlgebra.Dimension.Finite

namespace LinearAlgebra.Chapter01

open Submodule Set

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Definition: a finite set of vectors is a basis of a subspace. -/
def IsBasisOf (s : Finset V) (W : Submodule K V) : Prop :=
  LinearIndepOn K id (s : Set V) ∧ span K (s : Set V) = W

/-- Theorem: any two finite bases of a subspace have equal size. -/
theorem basis_card_eq {s t : Finset V} {W : Submodule K V}
    (hs : IsBasisOf s W) (ht : IsBasisOf t W) : s.card = t.card := by
  apply Nat.le_antisymm
  · apply independent_card_le hs.1
    rw [ht.2, ← hs.2]
    exact subset_span
  · apply independent_card_le ht.1
    rw [hs.2, ← ht.2]
    exact subset_span

/-- Theorem: extend an independent finite set inside a subspace,
using a finite ambient spanning set as a bound on the number of insertions. -/
theorem extend_in_subspace (t : Finset V) (W : Submodule K V)
    (ht : W ≤ span K (t : Set V)) (s : Finset V)
    (hs : LinearIndepOn K id (s : Set V)) (hsW : (s : Set V) ⊆ W) :
    ∃ u : Finset V, s ⊆ u ∧ IsBasisOf u W ∧ u.card ≤ t.card := by
  classical
  by_cases he : span K (s : Set V) = W
  · exact ⟨s, Finset.Subset.refl _, ⟨hs, he⟩, independent_card_le hs (hsW.trans ht)⟩
  · have hn : ¬(W : Set V) ⊆ span K (s : Set V) := by
      intro h
      exact he (le_antisymm (span_le.mpr hsW) h)
    obtain ⟨x, hxW, hx⟩ := not_subset.mp hn
    have hxs : x ∉ s := fun h => hx (subset_span h)
    have his : LinearIndepOn K id (↑(insert x s) : Set V) := by
      simpa only [Finset.coe_insert] using independent_insert hs hx
    have hiW : (↑(insert x s) : Set V) ⊆ W := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hxW
      · exact hsW hy
    obtain ⟨u, hu, hb, hc⟩ := extend_in_subspace t W ht (insert x s) his hiW
    exact ⟨u, (Finset.subset_insert _ _).trans hu, hb, hc⟩
termination_by t.card - s.card
decreasing_by
  classical
  have hb := independent_card_le his (hiW.trans ht)
  rw [Finset.card_insert_of_notMem hxs] at hb ⊢
  omega

/-- Theorem: every subspace of a finitely generated space has a finite basis. -/
theorem subspace_has_basis (t : Finset V) (ht : span K (t : Set V) = ⊤)
    (W : Submodule K V) : ∃ s : Finset V, IsBasisOf s W ∧ s.card ≤ t.card := by
  obtain ⟨s, _, hs, hc⟩ := extend_in_subspace t W (by rw [ht]; exact le_top)
    (∅ : Finset V) (by simp) (by simp)
  exact ⟨s, hs, hc⟩

/-- Definition: finite dimension is the existence of a finite basis. -/
def HasFiniteBasis (K V : Type*) [Field K] [AddCommGroup V] [Module K V] : Prop :=
  ∃ s : Finset V, IsBasisOf s (⊤ : Submodule K V)

/-- Definition: a space has dimension `n` if a finite basis has `n` elements. -/
def HasDimension (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (n : ℕ) : Prop :=
  ∃ s : Finset V, IsBasisOf s (⊤ : Submodule K V) ∧ s.card = n

/-- Theorem: dimension does not depend on the choice of basis. -/
theorem dimension_unique {m n : ℕ} (hm : HasDimension K V m) (hn : HasDimension K V n) :
    m = n := by
  obtain ⟨s, hs, rfl⟩ := hm
  obtain ⟨t, ht, rfl⟩ := hn
  exact basis_card_eq hs ht

/-- Definition: the dimension of a finite-dimensional space. -/
noncomputable def dimension (h : HasFiniteBasis K V) : ℕ := by
  classical
  exact Nat.find (show ∃ n, HasDimension K V n from by
    obtain ⟨s, hs⟩ := h
    exact ⟨s.card, s, hs, rfl⟩)

/-- Theorem: the defined dimension is attained by a basis. -/
theorem hasDimension_dimension (h : HasFiniteBasis K V) :
    HasDimension K V (dimension h) := by
  classical
  exact Nat.find_spec _

/-- Theorem: every basis has the defined dimension. -/
theorem dimension_eq_card (h : HasFiniteBasis K V) {s : Finset V}
    (hs : IsBasisOf s (⊤ : Submodule K V)) : dimension h = s.card :=
  dimension_unique (hasDimension_dimension h) ⟨s, hs, rfl⟩

/-- Definition: a line is a one-dimensional subspace. -/
def IsLine (W : Submodule K V) : Prop := HasDimension K W 1

/-- Definition: a plane is a two-dimensional subspace. -/
def IsPlane (W : Submodule K V) : Prop := HasDimension K W 2

/-- Theorem: an independent family of the full dimension is a basis. -/
theorem independent_full_card_is_basis {s t : Finset V}
    (ht : IsBasisOf t (⊤ : Submodule K V)) (hs : LinearIndepOn K id (s : Set V))
    (hc : s.card = t.card) : IsBasisOf s (⊤ : Submodule K V) := by
  obtain ⟨u, hsu, hu, huc⟩ := extend_in_subspace t ⊤ (by rw [ht.2]) s hs (by simp)
  have he : s = u := Finset.eq_of_subset_of_card_le hsu (by omega)
  simpa only [he] using hu

/-- Theorem: a generating family of the full dimension is a basis. -/
theorem spanning_full_card_is_basis {s t : Finset V}
    (ht : IsBasisOf t (⊤ : Submodule K V)) (hs : span K (s : Set V) = ⊤)
    (hc : s.card = t.card) : IsBasisOf s (⊤ : Submodule K V) := by
  classical
  let choices := s.powerset.filter fun (u : Finset V) => LinearIndepOn K id (u : Set V)
  have hne : choices.Nonempty := ⟨∅, by simp [choices, linearIndepOn_empty]⟩
  obtain ⟨u, hu, hmax⟩ := choices.exists_max_image Finset.card hne
  have hus : u ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp hu).1
  have hui : LinearIndepOn K id (u : Set V) := (Finset.mem_filter.mp hu).2
  have hm : MaximalIndependentIn (K := K) (u : Set V) (s : Set V) := by
    refine ⟨hus, hui, ?_⟩
    intro x hx hxu hi
    have hin : insert x u ∈ choices := by
      simp only [choices, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.insert_subset hx hus, by simpa only [Finset.coe_insert] using hi⟩
    have := hmax (insert x u) hin
    rw [Finset.card_insert_of_notMem hxu] at this
    omega
  have hub : IsBasisOf u (⊤ : Submodule K V) := by
    refine ⟨hui, top_unique ?_⟩
    rw [← hs]
    exact span_le.mpr (maximal_spans hm)
  have he : u = s := Finset.eq_of_subset_of_card_le hus (by rw [hc, basis_card_eq ht hub])
  simpa only [he] using hub

/-- Definition: a finite basis set determines a basis structure. -/
noncomputable def basisOfSet {s : Finset V} (hs : IsBasisOf s (⊤ : Submodule K V)) :
    Module.Basis s K V :=
  Module.Basis.mk (v := fun x : s => (x : V)) hs.1 (by
    rw [show range (fun x : s => (x : V)) = (s : Set V) by ext; simp, hs.2])

/-- Lemma (Supporting lemma): a finite basis set gives an indexed finite basis. -/
theorem isFiniteBasis_coe_of_isBasisOf {s : Finset V}
    (hs : IsBasisOf s (⊤ : Submodule K V)) :
    IsFiniteBasis (K := K) (fun x : s => (x : V)) := by
  exact (finiteBasis_iff _).mpr ⟨basisOfSet hs, Module.Basis.coe_mk _ _⟩

/-- Proposition: the locally determined finite dimension agrees
with `Module.finrank`. -/
theorem dimension_eq_finrank (h : HasFiniteBasis K V) : dimension h = Module.finrank K V := by
  obtain ⟨s, hs⟩ := h
  rw [dimension_eq_card ⟨s, hs⟩ hs]
  simpa only [Fintype.card_coe] using (Module.finrank_eq_card_basis (basisOfSet hs)).symm


/-- Definition: a basis of a subspace with vectors regarded as elements of that subspace. -/
noncomputable def subspaceBasis {s : Finset V} {W : Submodule K V} (hs : IsBasisOf s W) :
    Module.Basis s K W := by
  let v : s → W := fun x => ⟨x, hs.2 ▸ subset_span x.property⟩
  have hi : LinearIndependent K v := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha i
    have hs' : LinearIndependent K (fun x : s => (x : V)) := hs.1
    apply Fintype.linearIndependent_iff.mp hs' a _ i
    have he := congrArg (fun x : W => (x : V)) ha
    simpa only [v, Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero, id_eq] using he
  apply Module.Basis.mk hi
  intro x _
  apply (mem_span_range_iff_exists_fun K).mpr
  have hx : (x : V) ∈ span K (Set.range (fun y : s => (y : V))) := by
    rw [show Set.range (fun y : s => (y : V)) = (s : Set V) by ext; simp, hs.2]
    exact x.property
  obtain ⟨a, ha⟩ := (mem_span_range_iff_exists_fun K).mp hx
  refine ⟨a, Subtype.ext ?_⟩
  simpa only [v, Submodule.coe_sum, Submodule.coe_smul] using ha

/-- Proposition: the cardinality of an explicitly constructed
subspace basis is its standard finite rank. -/
theorem finrank_eq_card_of_basisOf {s : Finset V} {W : Submodule K V}
    (hs : IsBasisOf s W) : Module.finrank K W = s.card := by
  simpa only [Fintype.card_coe] using Module.finrank_eq_card_basis (subspaceBasis hs)

/-- Theorem: finite generation and finite basis existence are equivalent. -/
theorem hasFiniteBasis_iff_finite : HasFiniteBasis K V ↔ Module.Finite K V := by
  constructor
  · rintro ⟨s, hs⟩
    exact Module.Finite.of_fg_top ⟨s, hs.2⟩
  · intro h
    obtain ⟨t, ht⟩ := h.fg_top
    obtain ⟨s, hs, _⟩ := subspace_has_basis t ht ⊤
    exact ⟨s, hs⟩

/-- Theorem: a subspace has dimension at most the ambient finite dimension. -/
theorem subspace_finrank_le [Module.Finite K V] (W : Submodule K V) :
    Module.finrank K W ≤ Module.finrank K V := by
  obtain ⟨t, ht⟩ := hasFiniteBasis_iff_finite.mpr (inferInstance : Module.Finite K V)
  obtain ⟨s, hs, hc⟩ := subspace_has_basis t ht.2 W
  rw [finrank_eq_card_of_basisOf hs, ← dimension_eq_finrank ⟨t, ht⟩,
    dimension_eq_card ⟨t, ht⟩ ht]
  exact hc

/-- Theorem: a subspace of full finite dimension is the whole space. -/
theorem subspace_eq_top_of_finrank_eq [Module.Finite K V] (W : Submodule K V)
    (h : Module.finrank K W = Module.finrank K V) : W = ⊤ := by
  obtain ⟨t, ht⟩ := hasFiniteBasis_iff_finite.mpr (inferInstance : Module.Finite K V)
  obtain ⟨s, hs, _⟩ := subspace_has_basis t ht.2 W
  have hc : s.card = t.card := by
    rw [← finrank_eq_card_of_basisOf hs, h, ← dimension_eq_finrank ⟨t, ht⟩,
      dimension_eq_card ⟨t, ht⟩ ht]
  exact hs.2.symm.trans (independent_full_card_is_basis ht hs.1 hc).2

/-- Theorem: an independent finite set extends to a basis with
exactly the ambient dimension many vectors. -/
theorem extend_to_basis [Module.Finite K V] (s : Finset V)
    (hs : LinearIndepOn K id (s : Set V)) :
    ∃ t : Finset V, s ⊆ t ∧ IsBasisOf t (⊤ : Submodule K V) ∧
      t.card = Module.finrank K V := by
  obtain ⟨u, hu⟩ := hasFiniteBasis_iff_finite.mpr (inferInstance : Module.Finite K V)
  obtain ⟨t, hst, ht, _⟩ := extend_in_subspace u ⊤ (by rw [hu.2]) s hs (by simp)
  exact ⟨t, hst, ht, (dimension_eq_card ⟨t, ht⟩ ht).symm.trans (dimension_eq_finrank ⟨t, ht⟩)⟩


/-- Theorem: an independent finite family is no larger than a generating family. -/
theorem independent_le_generating {ι κ : Type*} [Fintype ι] [Fintype κ]
    {v : ι → V} {w : κ → V} (hv : LinearIndependent K v) (hw : Generates (K := K) w) :
    Fintype.card ι ≤ Fintype.card κ := by
  classical
  let s := Finset.univ.image v
  let t := Finset.univ.image w
  have hs : LinearIndepOn K id (s : Set V) := by
    simpa only [s, Finset.coe_image, Finset.coe_univ, image_univ] using hv.linearIndepOn_id
  have ht : span K (t : Set V) = ⊤ := by
    apply top_unique
    intro x _
    rw [show (t : Set V) = range w by simp [t]]
    exact (mem_span_range_iff_exists_fun K).mpr (hw x)
  have hc : s.card ≤ t.card := independent_card_le hs (by rw [ht]; simp)
  have hsc : s.card = Fintype.card ι := by
    exact (Finset.card_image_of_injective _ hv.injective).trans (Finset.card_univ)
  have htc : t.card ≤ Fintype.card κ := (Finset.card_image_le).trans_eq Finset.card_univ
  omega

/-- Theorem: an independent family whose size is the dimension is a basis. -/
theorem independent_card_finrank_is_basis [Module.Finite K V]
    {ι : Type*} [Fintype ι] {v : ι → V} (hv : LinearIndependent K v)
    (hc : Fintype.card ι = Module.finrank K V) : IsFiniteBasis (K := K) v := by
  classical
  obtain ⟨t, ht⟩ := hasFiniteBasis_iff_finite.mpr (inferInstance : Module.Finite K V)
  let s := Finset.univ.image v
  have hs : LinearIndepOn K id (s : Set V) := by
    simpa only [s, Finset.coe_image, Finset.coe_univ, image_univ] using hv.linearIndepOn_id
  have hsc : s.card = t.card := by
    rw [show s.card = Fintype.card ι from
      (Finset.card_image_of_injective _ hv.injective).trans Finset.card_univ,
      hc, ← dimension_eq_finrank ⟨t, ht⟩, dimension_eq_card ⟨t, ht⟩ ht]
  have hb := independent_full_card_is_basis ht hs hsc
  refine ⟨hv, fun x => (mem_span_range_iff_exists_fun K).mp ?_⟩
  rw [← show (s : Set V) = range v by simp [s], hb.2]
  trivial

/-- Definition: infinite dimension means that no finite basis exists. -/
def IsInfiniteDimensional (K V : Type*) [Field K] [AddCommGroup V] [Module K V] : Prop :=
  ¬HasFiniteBasis K V

/-- Theorem: the zero space has the empty basis and dimension zero. -/
theorem zero_space_dimension [Subsingleton V] : HasDimension K V 0 := by
  refine ⟨∅, ⟨by simp, ?_⟩, rfl⟩
  apply le_antisymm le_top
  intro x _
  have hx : x = 0 := Subsingleton.elim _ _
  rw [hx]
  exact zero_mem _

end LinearAlgebra.Chapter01
