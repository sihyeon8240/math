import Textbooks.LinearAlgebra.Chapter01.DirectSums

namespace LinearAlgebra.Chapter01

open scoped BigOperators

variable {K U W : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup W] [Module K W]

/-- Definition: place each basis vector in its own component of a product. -/
def productFamily {ι κ : Type*} (u : ι → U) (w : κ → W) : ι ⊕ κ → U × W :=
  Sum.elim (fun i => (u i, 0)) (fun j => (0, w j))

/-- Lemma (Supporting lemma): a product combination splits into two component combinations. -/
theorem combination_product {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : ι → U) (w : κ → W) (a : ι ⊕ κ → K) :
    linearCombination (productFamily u w) a =
      (linearCombination u (a ∘ Sum.inl), linearCombination w (a ∘ Sum.inr)) := by
  ext <;> simp [linearCombination, productFamily, Fintype.sum_sum_type, Prod.fst_sum, Prod.snd_sum]

/-- Theorem (Core result): bases of the factors give a basis of the direct product. -/
theorem product_is_basis {ι κ : Type*} [Fintype ι] [Fintype κ]
    {u : ι → U} {w : κ → W} (hu : IsFiniteBasis (K := K) u)
    (hw : IsFiniteBasis (K := K) w) : IsFiniteBasis (K := K) (productFamily u w) := by
  refine ⟨Fintype.linearIndependent_iff.mpr ?_, ?_⟩
  · intro a ha i
    change linearCombination (productFamily u w) a = 0 at ha
    rw [combination_product] at ha
    cases i with
    | inl i => exact Fintype.linearIndependent_iff.mp hu.1 _ (congrArg Prod.fst ha) i
    | inr i => exact Fintype.linearIndependent_iff.mp hw.1 _ (congrArg Prod.snd ha) i
  · rintro ⟨x, y⟩
    obtain ⟨a, ha⟩ := hu.2 x
    obtain ⟨b, hb⟩ := hw.2 y
    refine ⟨Sum.elim a b, ?_⟩
    rw [combination_product]
    exact Prod.ext ha hb

/-- Theorem (Core result): the dimension of a product is the sum of the dimensions. -/
theorem finrank_product [Module.Finite K U] [Module.Finite K W] :
    Module.finrank K (U × W) = Module.finrank K U + Module.finrank K W := by
  obtain ⟨s, hs⟩ := hasFiniteBasis_iff_finite.mpr (inferInstance : Module.Finite K U)
  obtain ⟨t, ht⟩ := hasFiniteBasis_iff_finite.mpr (inferInstance : Module.Finite K W)
  have hu : IsFiniteBasis (K := K) (fun x : s => (x : U)) :=
    (finiteBasis_iff _).mpr ⟨basisOfSet hs, Module.Basis.coe_mk _ _⟩
  have hw : IsFiniteBasis (K := K) (fun x : t => (x : W)) :=
    (finiteBasis_iff _).mpr ⟨basisOfSet ht, Module.Basis.coe_mk _ _⟩
  obtain ⟨b, _⟩ := (finiteBasis_iff _).mp (product_is_basis hu hw)
  rw [Module.finrank_eq_card_basis b, Fintype.card_sum, Fintype.card_coe, Fintype.card_coe,
    ← dimension_eq_finrank ⟨s, hs⟩, dimension_eq_card ⟨s, hs⟩ hs,
    ← dimension_eq_finrank ⟨t, ht⟩, dimension_eq_card ⟨t, ht⟩ ht]

/-- Definition: split a coordinate tuple into two consecutive blocks. -/
def coordinateProductEquiv (r s : ℕ) :
    CoordinateSpace K (r + s) ≃ₗ[K] CoordinateSpace K r × CoordinateSpace K s where
  toFun x := (fun i => x (Fin.castAdd s i), fun j => x (Fin.natAdd r j))
  invFun p := Fin.append p.1 p.2
  left_inv x := by ext i; exact Fin.addCases (fun j => by simp) (fun j => by simp) i
  right_inv p := by ext <;> simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end LinearAlgebra.Chapter01
