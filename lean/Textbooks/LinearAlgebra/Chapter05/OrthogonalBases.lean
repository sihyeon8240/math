import Textbooks.LinearAlgebra.Chapter05.ScalarProducts
import Textbooks.LinearAlgebra.Chapter01.DirectSums
import Mathlib.LinearAlgebra.Basis.Fin

namespace LinearAlgebra.Chapter05

open Module Submodule

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Lemma: a vector of nonzero square splits off its perpendicular subspace. -/
theorem line_orthogonal_directSum (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (x : V) (hx : B x x ≠ 0) :
    Chapter01.IsDirectSum (K ∙ x) ((K ∙ x).orthogonalBilin B) := by
  apply Chapter01.directSum_of_sup_inf

  · apply top_unique
    intro y _
    refine mem_sup.mpr ⟨lineProjection B y x, ?_, y - lineProjection B y x, ?_, ?_⟩

    · exact smul_mem _ _ (mem_span_singleton_self x)

    · intro z hz
      obtain ⟨c, rfl⟩ := mem_span_singleton.mp hz
      rw [map_smul, LinearMap.smul_apply, hB.eq]
      rw [sub_lineProjection_orthogonal B y x hx, smul_zero]

    · exact add_sub_cancel _ _

  · apply bot_unique
    intro y hy
    obtain ⟨c, rfl⟩ := mem_span_singleton.mp hy.1

    have hc := hy.2 x (mem_span_singleton_self x)
    rw [map_smul, smul_eq_mul] at hc
    have hz : c = 0 := (mul_eq_zero.mp hc).resolve_right hx

    rw [hz, zero_smul]
    exact zero_mem _

/-- Lemma: a nonzero vector spans a one-dimensional subspace. -/
private theorem finrank_line (x : V) (hx : x ≠ 0) : finrank K (K ∙ x) = 1 := by
  classical

  have hs : Chapter01.IsBasisOf {x} (K ∙ x) := by
    constructor

    · simpa only [Finset.coe_singleton, linearIndepOn_singleton_iff, id_eq] using hx

    · simp only [Finset.coe_singleton]

  rw [Chapter01.finrank_eq_card_of_basisOf hs, Finset.card_singleton]

/-- Theorem: a symmetric form in characteristic not two has an orthogonal basis. -/
theorem exists_orthogonal_basis [Module.Finite K V] (B : LinearMap.BilinForm K V)
    (hB : B.IsSymm) (h2 : (2 : K) ≠ 0) :
    ∃ b : Basis (Fin (finrank K V)) K V, B.IsOrthoᵢ b := by
  suffices ∀ d, finrank K V = d → ∃ b : Basis (Fin d) K V, B.IsOrthoᵢ b from
    this _ rfl

  intro d
  induction d generalizing V with
  | zero =>
    intro hd
    refine ⟨(Chapter01.finiteBasis (K := K) (V := V)).reindex (finCongr hd), ?_⟩
    intro i
    exact Fin.elim0 i

  | succ d ih =>
    intro hd
    by_cases hz : B = 0

    · subst B
      let b := (Chapter01.finiteBasis (K := K) (V := V)).reindex (finCongr hd)
      exact ⟨b, fun _ _ _ => rfl⟩

    obtain ⟨x, hx⟩ := exists_self_ne_zero B hB h2 hz
    let W := (K ∙ x).orthogonalBilin B
    have hsplit := line_orthogonal_directSum B hB x hx

    have hdim : finrank K W = d := by
      have he := Chapter01.finrank_directSum hsplit
      rw [finrank_line x (show x ≠ 0 from fun h => hx (h ▸ map_zero _)), hd] at he
      change finrank K W = d
      change d + 1 = 1 + finrank K W at he
      omega

    let C := B.domRestrict₁₂ W W
    obtain ⟨b, hb⟩ := ih C ⟨fun u v => hB.eq u v⟩ hdim
    let c := Basis.mkFinCons x b
      (by
        intro a y hy he

        have hm : a • x ∈ (K ∙ x) ⊓ W := by
          refine ⟨smul_mem _ _ (mem_span_singleton_self x), ?_⟩
          rw [eq_neg_of_add_eq_zero_left he]
          exact W.neg_mem hy

        have hz := (Chapter01.directSum_sup_inf hsplit).2
        rw [hz, mem_bot] at hm

        exact (smul_eq_zero.mp hm).resolve_right (fun h => hx (h ▸ map_zero _)))
      (by
        intro y
        refine ⟨-component B y x, ?_⟩

        have hp : y - lineProjection B y x ∈ W := by
          intro z hz
          obtain ⟨a, rfl⟩ := mem_span_singleton.mp hz
          rw [map_smul, LinearMap.smul_apply, hB.eq,
            sub_lineProjection_orthogonal B y x hx, smul_zero]

        simpa only [lineProjection, neg_smul, sub_eq_add_neg, add_comm] using hp)

    refine ⟨c, ?_⟩
    rw [Basis.coe_mkFinCons]
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j <;>
      intro hij <;>
      simp only [Function.onFun, Fin.cons_zero, Fin.cons_succ, Function.comp_apply]

    · exact (hij rfl).elim

    · exact (b j).property x (mem_span_singleton_self x)

    · rw [hB.eq]
      exact (b i).property x (mem_span_singleton_self x)

    · exact hb (fun h => hij (congrArg Fin.succ h))

end LinearAlgebra.Chapter05
