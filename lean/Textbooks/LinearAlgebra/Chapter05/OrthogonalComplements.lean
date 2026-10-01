import Textbooks.LinearAlgebra.Chapter05.GramSchmidt
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Projection

namespace LinearAlgebra.Chapter05

open Module Submodule
open scoped BigOperators

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- Lemma: perpendicularity to a finite basis is perpendicularity to its subspace. -/
theorem mem_orthogonal_iff_basis {ι : Type*} [Fintype ι] (W : Submodule 𝕜 E)
    (b : Basis ι 𝕜 W) (v : E) :
    v ∈ Wᗮ ↔ ∀ i, ⟪(b i : E), v⟫ = 0 := by
  classical
  constructor

  · intro h i
    exact h (b i) (b i).property

  · intro h x hx
    let y : W := ⟨x, hx⟩
    have he : x = ∑ i, b.repr y i • (b i : E) := by
      have hs := b.sum_repr y
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using
        (congrArg (fun z : W => (z : E)) hs).symm

    rw [he, sum_inner]
    simp only [inner_smul_left, h, mul_zero, Finset.sum_const_zero]

/-- Theorem: every finite-dimensional subspace splits off its orthogonal complement. -/
theorem orthogonal_directSum (W : Submodule 𝕜 E) [Module.Finite 𝕜 W] :
    Chapter01.IsDirectSum W Wᗮ := by
  obtain ⟨b, hb⟩ := exists_orthonormal_basis (𝕜 := 𝕜) (E := W)
  let u := fun i => (b i : E)
  have hu : Pairwise fun i j => ⟪u i, u j⟫ = 0 := hb.2

  apply Chapter01.directSum_of_sup_inf

  · apply top_unique
    intro v _
    have hp : orthogonalProjection (𝕜 := 𝕜) u v ∈ W := by
      apply W.sum_mem
      intro i _
      exact W.smul_mem _ (b i).property

    have hr : v - orthogonalProjection (𝕜 := 𝕜) u v ∈ Wᗮ := by
      rw [mem_orthogonal_iff_basis W b]
      exact inner_sub_orthogonalProjection u hu v

    exact mem_sup.mpr ⟨_, hp, _, hr, add_sub_cancel _ _⟩

  · apply bot_unique
    intro x hx
    exact inner_self_eq_zero.mp (hx.2 x hx.1)

/-- Theorem: dimensions of a subspace and its orthogonal complement add to the ambient dimension. -/
theorem finrank_add_finrank_orthogonal [Module.Finite 𝕜 E] (W : Submodule 𝕜 E) :
    finrank 𝕜 W + finrank 𝕜 Wᗮ = finrank 𝕜 E :=
  (Chapter01.finrank_directSum (orthogonal_directSum W)).symm

/-- Theorem: any finite orthogonal basis of a subspace extends to an orthogonal basis of the
space. -/
theorem exists_orthogonal_basis_extension [Module.Finite 𝕜 E]
    {ι : Type*} [Fintype ι] (W : Submodule 𝕜 E) (b : Basis ι 𝕜 W)
    (hb : Pairwise fun i j => ⟪b i, b j⟫ = 0) :
    ∃ c : Basis (ι ⊕ Fin (finrank 𝕜 Wᗮ)) 𝕜 E,
      (∀ i, c (Sum.inl i) = (b i : E)) ∧
      Pairwise fun i j => ⟪c i, c j⟫ = 0 := by
  classical

  obtain ⟨d, hd⟩ := exists_orthonormal_basis (𝕜 := 𝕜) (E := Wᗮ)
  obtain ⟨hs, hz⟩ := Chapter01.directSum_sup_inf (orthogonal_directSum W)
  have hc : IsCompl W Wᗮ := ⟨disjoint_iff.mpr hz, codisjoint_iff.mpr hs⟩
  let c := (b.prod d).map (W.prodEquivOfIsCompl Wᗮ hc)

  have hleft (i : ι) : c (Sum.inl i) = (b i : E) := by
    simp [c, Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']

  have hright (i : Fin (finrank 𝕜 Wᗮ)) : c (Sum.inr i) = (d i : E) := by
    simp [c, Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']

  refine ⟨c, hleft, ?_⟩
  intro i j hij
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      rw [hleft, hleft]
      exact hb (fun h => hij (congrArg Sum.inl h))

    | inr j =>
      rw [hleft, hright]
      exact (d j).property (b i) (b i).property

  | inr i =>
    cases j with
    | inl j =>
      rw [hright, hleft, inner_eq_zero_symm]
      exact (d i).property (b j) (b j).property

    | inr j =>
      rw [hright, hright]
      exact hd.2 (fun h => hij (congrArg Sum.inr h))

end LinearAlgebra.Chapter05
