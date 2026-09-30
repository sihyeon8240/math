import Textbooks.LinearAlgebra.Chapter04.Representation

/-!
Change of coordinates and conjugacy.
The transition from `c` to `b` is `toMatrix c b id`.
Inverse notation uses the existing Chapter II inverse with its two-sided
inverse witness, so no determinant theory is needed.
-/

namespace LinearAlgebra.Chapter04

open scoped Matrix

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}

/-- Corollary: the matrix of the identity changes coordinates between bases. -/
theorem change_coordinates (b c : Module.Basis (Fin n) K V) (v : V) :
    c.repr v = LinearMap.toMatrix b c (LinearMap.id : V →ₗ[K] V) *ᵥ b.repr v :=
  (toMatrix_mulVec_repr b c LinearMap.id v).symm

/-- Corollary: opposite changes of basis are two-sided inverses. -/
theorem transition_mul_transition (b c : Module.Basis (Fin n) K V) :
    LinearMap.toMatrix b c (LinearMap.id : V →ₗ[K] V) *
      LinearMap.toMatrix c b (LinearMap.id : V →ₗ[K] V) = 1 := by
  rw [← toMatrix_comp c b c]
  change LinearMap.toMatrix c c (LinearMap.id : V →ₗ[K] V) = 1
  exact toMatrix_id c

/-- Corollary: every transition matrix is invertible. -/
theorem transition_isNonsingular (b c : Module.Basis (Fin n) K V) :
    Chapter02.IsNonsingular (LinearMap.toMatrix b c (LinearMap.id : V →ₗ[K] V)) :=
  ⟨LinearMap.toMatrix c b LinearMap.id,
    transition_mul_transition b c, transition_mul_transition c b⟩

/-- Proposition: the chosen inverse is the transition in the opposite direction. -/
theorem inverse_transition (b c : Module.Basis (Fin n) K V) :
    Chapter02.inverse (transition_isNonsingular b c) =
      LinearMap.toMatrix c b (LinearMap.id : V →ₗ[K] V) :=
  Chapter02.inverse_unique (Chapter02.inverse_spec (transition_isNonsingular b c)).2
    (transition_mul_transition b c)

/-- Theorem: changing both bases conjugates the representing matrix. -/
theorem toMatrix_change_basis (b c : Module.Basis (Fin n) K V) (f : V →ₗ[K] V) :
    LinearMap.toMatrix c c f =
      LinearMap.toMatrix b c (LinearMap.id : V →ₗ[K] V) *
        LinearMap.toMatrix b b f * LinearMap.toMatrix c b (LinearMap.id : V →ₗ[K] V) := by
  rw [← toMatrix_comp b b c, ← toMatrix_comp c b c]
  rfl

/-- Theorem: the two matrices are conjugate by an invertible matrix, namely
`N = toMatrix c b id`, giving the formula `N⁻¹ M N`. -/
theorem exists_matrix_conjugacy (b c : Module.Basis (Fin n) K V) (f : V →ₗ[K] V) :
    ∃ (N : Matrix (Fin n) (Fin n) K) (hN : Chapter02.IsNonsingular N),
      LinearMap.toMatrix c c f = Chapter02.inverse hN * LinearMap.toMatrix b b f * N := by
  refine ⟨LinearMap.toMatrix c b LinearMap.id, transition_isNonsingular c b, ?_⟩
  rw [inverse_transition]
  exact toMatrix_change_basis b c f

end LinearAlgebra.Chapter04
