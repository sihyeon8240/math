import Textbooks.LinearAlgebra.Chapter05.QuadraticForms
import Textbooks.LinearAlgebra.Chapter03.KernelImage

namespace LinearAlgebra.Chapter05

open Module
open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Definition: count the positive squares of the vectors in a finite basis. -/
noncomputable def positiveCount {ι : Type*} (B : LinearMap.BilinForm ℝ V)
    (b : Basis ι ℝ V) : ℕ := Nat.card {i : ι // 0 < B (b i) (b i)}

/-- Lemma: a positive combination has a nonzero coordinate in the positive part of any orthogonal
basis. -/
theorem positive_coordinates_injective {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : LinearMap.BilinForm ℝ V) (b : Basis ι ℝ V) (hb : B.IsOrthoᵢ b)
    (c : Basis κ ℝ V) (hc : B.IsOrthoᵢ c) :
    ∃ f : ({j : κ // 0 < B (c j) (c j)} → ℝ) →ₗ[ℝ]
      ({i : ι // 0 < B (b i) (b i)} → ℝ), Function.Injective f := by
  classical

  let P := {j : κ // 0 < B (c j) (c j)}
  let Q := {i : ι // 0 < B (b i) (b i)}
  let inclusion : (P → ℝ) →ₗ[ℝ] V :=
    ∑ j : P, (LinearMap.smulRight (LinearMap.proj j) (c j))
  let f : (P → ℝ) →ₗ[ℝ] (Q → ℝ) :=
    { toFun := fun a i => b.repr (inclusion a) i
      map_add' := by
        intro a d
        ext i
        simp only [map_add, Finsupp.add_apply, Pi.add_apply]
      map_smul' := by
        intro t a
        ext i
        simp only [map_smul, Finsupp.smul_apply, Pi.smul_apply, RingHom.id_apply] }

  have hinclusion (a : P → ℝ) : inclusion a = ∑ j : P, a j • c j := by
    simp only [inclusion, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]

  refine ⟨f, ?_⟩
  apply (Chapter03.ker_eq_bot_iff_injective f).mp
  apply bot_unique
  intro a ha
  change f a = 0 at ha
  by_contra hn
  have hane : a ≠ 0 := hn

  have hp : 0 < B (inclusion a) (inclusion a) := by
    rw [hinclusion, bilin_sum_self B (fun j : P => c j)]

    · apply Finset.sum_pos'

      · intro j _
        exact mul_nonneg j.property.le (sq_nonneg _)

      · obtain ⟨j, hj⟩ := Function.ne_iff.mp hane
        exact ⟨j, Finset.mem_univ _, mul_pos j.property (sq_pos_of_ne_zero hj)⟩

    · intro i j hij
      exact hc (fun h => hij (Subtype.ext h))

  have hm : B (inclusion a) (inclusion a) ≤ 0 := by
    change B.toQuadraticMap (inclusion a) ≤ 0
    rw [quadraticForm_eq_sum B b hb]
    apply Finset.sum_nonpos
    intro i _
    by_cases hi : 0 < B (b i) (b i)

    · have hz : b.repr (inclusion a) i = 0 := congrFun ha ⟨i, hi⟩
      rw [hz, zero_pow (by omega), mul_zero]

    · exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hi) (sq_nonneg _)

  linarith

/-- Lemma: comparing positive coordinate spaces bounds the number of positive basis vectors. -/
theorem positiveCount_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : LinearMap.BilinForm ℝ V) (b : Basis ι ℝ V) (hb : B.IsOrthoᵢ b)
    (c : Basis κ ℝ V) (hc : B.IsOrthoᵢ c) : positiveCount B c ≤ positiveCount B b := by
  classical

  obtain ⟨f, hf⟩ := positive_coordinates_injective B b hb c hc
  let d := Pi.basisFun ℝ {j : κ // 0 < B (c j) (c j)}
  let e := Pi.basisFun ℝ {i : ι // 0 < B (b i) (b i)}

  have hi := Chapter03.independent_map f hf d.linearIndependent
  have he : Chapter01.Generates (K := ℝ) e := by
    intro x
    exact ⟨fun i => e.repr x i, e.sum_repr x⟩

  have hn := Chapter01.independent_le_generating hi he
  simpa only [positiveCount, Nat.card_eq_fintype_card] using hn

/-- Theorem: the number of positive squares is independent of the orthogonal basis. -/
theorem positiveCount_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : LinearMap.BilinForm ℝ V) (b : Basis ι ℝ V) (hb : B.IsOrthoᵢ b)
    (c : Basis κ ℝ V) (hc : B.IsOrthoᵢ c) : positiveCount B b = positiveCount B c :=
  Nat.le_antisymm (positiveCount_le B c hc b hb) (positiveCount_le B b hb c hc)

/-- Definition: the index of positivity of a real symmetric form. -/
noncomputable def indexOfPositivity [Module.Finite ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm) : ℕ :=
  positiveCount B (Classical.choose (exists_orthogonal_basis B hB (by norm_num)))

/-- Theorem: Sylvester's integer counts the positive squares in every orthogonal basis. -/
theorem sylvester [Module.Finite ℝ V] (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm) :
    ∃ r : ℕ, ∀ {ι : Type*} [Fintype ι] (b : Basis ι ℝ V),
      B.IsOrthoᵢ b → positiveCount B b = r := by
  refine ⟨indexOfPositivity B hB, ?_⟩

  intro ι _ b hb
  exact positiveCount_eq B b hb _
    (Classical.choose_spec (exists_orthogonal_basis B hB (by norm_num)))

end LinearAlgebra.Chapter05
