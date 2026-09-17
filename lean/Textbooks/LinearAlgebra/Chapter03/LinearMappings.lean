import Textbooks.LinearAlgebra.Chapter02.LinearEquations
import Textbooks.LinearAlgebra.Chapter03.Mappings

namespace LinearAlgebra.Chapter03

open scoped BigOperators Matrix
open Chapter01

variable {K U V W : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Definition: a map preserving vector addition and scalar multiplication. -/
def linearMapOf (f : V → W) (ha : ∀ x y, f (x + y) = f x + f y)
    (hs : ∀ (c : K) x, f (c • x) = c • f x) : V →ₗ[K] W where
  toFun := f
  map_add' := ha
  map_smul' := hs

/-- Proposition: a linear map sends zero to zero. -/
theorem map_zero (f : V →ₗ[K] W) : f 0 = 0 := by
  have h : f 0 + 0 = f 0 + f 0 := by
    rw [add_zero, ← f.map_add, zero_add]

  exact (add_left_cancel h).symm

/-- Lemma: a linear map preserves finite sums. -/
theorem map_sum {ι : Type*} (f : V →ₗ[K] W) (s : Finset ι) (v : ι → V) :
    f (∑ i ∈ s, v i) = ∑ i ∈ s, f (v i) := by
  classical

  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, map_zero]
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, f.map_add, ih]

/-- Proposition: a linear map preserves every finite linear combination. -/
theorem map_combination {ι : Type*} [Fintype ι] (f : V →ₗ[K] W) (v : ι → V) (a : ι → K) :
    f (linearCombination v a) = linearCombination (fun i => f (v i)) a := by
  simp only [linearCombination, map_sum, f.map_smul]

/-- Definition: the linear map associated with a matrix. -/
def matrixMap {m n : ℕ} (A : Chapter02.MatrixSpace K m n) : (Fin n → K) →ₗ[K] (Fin m → K) :=
  linearMapOf (fun x => A *ᵥ x)
    (fun x y => by simp only [Chapter02.mulVec_eq_combination, combination_add])
    (fun c x => by simp only [Chapter02.mulVec_eq_combination, combination_smul])

/-- Definition: the subspace of linear functions inside the space of all functions. -/
def linearFunctionSubspace : Submodule K (V → W) :=
  subspaceOfClosed {f | (∀ x y, f (x + y) = f x + f y) ∧
    (∀ (c : K) x, f (c • x) = c • f x)}
    (by constructor <;> intros <;> simp only [Pi.zero_apply, add_zero, scalar_smul_zero])
    (by
      rintro f ⟨hfa, hfs⟩ g ⟨hga, hgs⟩
      constructor

      · intro x y
        change f (x + y) + g (x + y) = (f x + g x) + (f y + g y)
        rw [hfa, hga]
        abel

      · intro c x
        change f (c • x) + g (c • x) = c • (f x + g x)
        rw [hfs, hgs, smul_add])
    (by
      rintro c f ⟨hfa, hfs⟩
      constructor

      · intro x y
        change c • f (x + y) = c • f x + c • f y
        rw [hfa, smul_add]

      · intro a x
        change c • f (a • x) = a • c • f x
        rw [hfs, smul_comm])

/-- Proposition: coordinates preserve addition. -/
theorem coordinates_add {ι : Type*} [Fintype ι] {v : ι → V}
    (h : IsFiniteBasis (K := K) v) (x y : V) :
    coordinates h (x + y) = coordinates h x + coordinates h y := by
  apply coefficients_unique h.1
  rw [combination_coordinates, combination_add, combination_coordinates, combination_coordinates]

/-- Proposition: coordinates preserve scalar multiplication. -/
theorem coordinates_smul {ι : Type*} [Fintype ι] {v : ι → V}
    (h : IsFiniteBasis (K := K) v) (c : K) (x : V) :
    coordinates h (c • x) = c • coordinates h x := by
  apply coefficients_unique h.1
  rw [combination_coordinates, combination_smul, combination_coordinates]

/-- Definition: the coordinate map of a finite basis. -/
noncomputable def coordinateMap {ι : Type*} [Fintype ι] {v : ι → V}
    (h : IsFiniteBasis (K := K) v) : V →ₗ[K] (ι → K) :=
  linearMapOf (coordinates h) (coordinates_add h) (coordinates_smul h)

/-- Lemma: a single unit coefficient selects its vector. -/
theorem combination_single {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → V) (i : ι) :
    linearCombination v (Pi.single i (1 : K)) = v i := by
  simp [linearCombination, Pi.single_apply]

/-- Definition: extend prescribed values on a basis by linear combinations. -/
noncomputable def mapOfBasis {ι : Type*} [Fintype ι] {v : ι → V}
    (h : IsFiniteBasis (K := K) v) (w : ι → W) : V →ₗ[K] W :=
  linearMapOf (fun x => linearCombination w (coordinates h x))
    (fun x y => by rw [coordinates_add, combination_add])
    (fun c x => by rw [coordinates_smul, combination_smul])

/-- Proposition: the constructed map takes the prescribed basis values. -/
theorem mapOfBasis_apply {ι : Type*} [Fintype ι] {v : ι → V}
    (h : IsFiniteBasis (K := K) v) (w : ι → W) (i : ι) : mapOfBasis h w (v i) = w i := by
  classical

  have hc : coordinates h (v i) = Pi.single i 1 := by
    apply coefficients_unique h.1
    rw [combination_coordinates, combination_single]

  change linearCombination w (coordinates h (v i)) = w i
  rw [hc, combination_single]

/-- Theorem: a linear map is determined by its values on a generating family. -/
theorem maps_eq_on_generators {ι : Type*} [Fintype ι] {v : ι → V}
    (hv : Generates (K := K) v) (f g : V →ₗ[K] W) (h : ∀ i, f (v i) = g (v i)) : f = g := by
  ext x

  obtain ⟨a, rfl⟩ := hv x

  rw [map_combination, map_combination]
  exact congrArg (fun w : ι → W => linearCombination w a) (funext h)

/-- Theorem: arbitrary values on a finite basis extend to exactly one linear map. -/
theorem exists_unique_map_basis {ι : Type*} [Fintype ι] {v : ι → V}
    (h : IsFiniteBasis (K := K) v) (w : ι → W) : ∃! f : V →ₗ[K] W, ∀ i, f (v i) = w i := by
  refine ⟨mapOfBasis h w, mapOfBasis_apply h w, ?_⟩
  intro f hf
  exact maps_eq_on_generators h.2 f _ (fun i => (hf i).trans (mapOfBasis_apply h w i).symm)

end LinearAlgebra.Chapter03
