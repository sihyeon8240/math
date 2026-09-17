import Mathlib.Algebra.Field.Subfield.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel

namespace LinearAlgebra.Chapter01

open scoped BigOperators

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Definition: the fields are subfields of the complex numbers. -/
abbrev ComplexSubfield := Subfield ℂ

/-- Definition: inclusion of subfields. -/
def IsSubfield (K L : ComplexSubfield) : Prop := K ≤ L

/-- Definition: the coordinate space `Kⁿ`. -/
abbrev CoordinateSpace (K : Type*) (n : ℕ) := Fin n → K

/-- Definition: the function space on a set/type, with pointwise operations. -/
abbrev FunctionSpace (S K : Type*) := S → K

/-- Proposition: the eight vector-space laws. -/
theorem vector_space_laws (u v w : V) (a b c : K) :
    (u + v) + w = u + (v + w) ∧ 0 + u = u ∧ u + -u = 0 ∧
    u + v = v + u ∧ c • (u + v) = c • u + c • v ∧
    (a + b) • v = a • v + b • v ∧ (a * b) • v = a • (b • v) ∧
    (1 : K) • u = u :=
  ⟨add_assoc .., zero_add _, add_neg_cancel _, add_comm .., smul_add ..,
    add_smul .., mul_smul .., one_smul ..⟩

/-- Proposition: uniqueness of the zero vector. -/
theorem zero_unique (z : V) (h : ∀ v : V, z + v = v) : z = 0 := by
  simpa only [add_zero] using h 0

/-- Proposition: scalar zero annihilates every vector. -/
theorem scalar_zero_smul (v : V) : (0 : K) • v = 0 := by
  have h : (0 : K) • v + 0 = (0 : K) • v + (0 : K) • v := by
    rw [add_zero, ← add_smul, zero_add]

  exact (add_left_cancel h).symm

/-- Proposition: multiplication by minus one. -/
theorem minus_one_smul (v : V) : (-1 : K) • v = -v := by
  apply add_left_cancel (a := v)
  calc
    v + (-1 : K) • v = (1 : K) • v + (-1 : K) • v := by
      rw [one_smul]
    _ = 0 := by
      rw [← add_smul, add_neg_cancel, scalar_zero_smul]
    _ = v + -v := (add_neg_cancel v).symm

/-- Proposition: every scalar annihilates the zero vector. -/
theorem scalar_smul_zero (c : K) : c • (0 : V) = 0 := by
  have h : c • (0 : V) + 0 = c • 0 + c • 0 := by
    rw [add_zero, ← smul_add, zero_add]

  exact (add_left_cancel h).symm

/-- Definition: a subspace is a set closed under addition and scalar multiplication,
containing zero; the structure provides the induced vector space. -/
def subspaceOfClosed (W : Set V) (h0 : (0 : V) ∈ W)
    (ha : ∀ u ∈ W, ∀ v ∈ W, u + v ∈ W)
    (hs : ∀ (c : K) v, v ∈ W → c • v ∈ W) : Submodule K V where
  carrier := W
  zero_mem' := h0
  add_mem' := fun hu hv => ha _ hu _ hv
  smul_mem' := hs

/-- Definition: intersection of two subspaces, with its closure proof. -/
def intersection (U W : Submodule K V) : Submodule K V :=
  subspaceOfClosed (U ∩ W : Set V) ⟨U.zero_mem, W.zero_mem⟩
    (fun _ hu _ hv => ⟨U.add_mem hu.1 hv.1, W.add_mem hu.2 hv.2⟩)
    (fun c _ hv => ⟨U.smul_mem c hv.1, W.smul_mem c hv.2⟩)

/-- Definition: a finite linear combination. -/
def linearCombination {ι : Type*} [Fintype ι] (v : ι → V) (a : ι → K) : V :=
  ∑ i, a i • v i

/-- Lemma: adding coefficient vectors adds combinations. -/
theorem combination_add {ι : Type*} [Fintype ι] (v : ι → V) (a b : ι → K) :
    linearCombination v (a + b) = linearCombination v a + linearCombination v b := by
  simp only [linearCombination, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- Lemma: scaling coefficients scales a combination. -/
theorem combination_smul {ι : Type*} [Fintype ι] (v : ι → V) (c : K) (a : ι → K) :
    linearCombination v (c • a) = c • linearCombination v a := by
  simp only [linearCombination, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- Definition: the subspace of all linear combinations of a family. -/
def generatedSubspace {ι : Type*} [Fintype ι] (v : ι → V) : Submodule K V :=
  subspaceOfClosed {x | ∃ a : ι → K, linearCombination v a = x}
    ⟨0, by simp only [linearCombination, Pi.zero_apply, zero_smul, Finset.sum_const_zero]⟩
    (fun _ ⟨a, ha⟩ _ ⟨b, hb⟩ => ⟨a + b, by rw [combination_add, ha, hb]⟩)
    (fun c _ ⟨a, ha⟩ => ⟨c • a, by rw [combination_smul, ha]⟩)

/-- Proposition: the generated subspace equals the span of the family. -/
theorem generatedSubspace_eq_span {ι : Type*} [Fintype ι] (v : ι → V) :
    generatedSubspace (K := K) v = Submodule.span K (Set.range v) := by
  ext x
  exact (Submodule.mem_span_range_iff_exists_fun K).symm

/-- Definition: a family generates the entire space. -/
def Generates {ι : Type*} [Fintype ι] (v : ι → V) : Prop :=
  ∀ x : V, ∃ a : ι → K, linearCombination v a = x

/-- Definition: the bilinear dot product on `Kⁿ`. -/
def dotProduct {n : ℕ} (a b : CoordinateSpace K n) : K := ∑ i, a i * b i

/-- Definition: perpendicularity for the bilinear dot product. -/
def Perpendicular {n : ℕ} (a b : CoordinateSpace K n) : Prop := dotProduct a b = 0

/-- Proposition: symmetry. -/
theorem dot_comm {n : ℕ} (a b : CoordinateSpace K n) : dotProduct a b = dotProduct b a := by
  simp only [dotProduct, mul_comm]

/-- Proposition: additivity. -/
theorem dot_add {n : ℕ} (a b c : CoordinateSpace K n) :
    dotProduct a (b + c) = dotProduct a b + dotProduct a c := by
  simp only [dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- Proposition: homogeneity. -/
theorem dot_smul {n : ℕ} (a b : CoordinateSpace K n) (c : K) :
    dotProduct (c • a) b = c * dotProduct a b := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- Definition: the perpendicular subspace to a fixed vector. -/
def perpendicularSubspace {n : ℕ} (a : CoordinateSpace K n) :
    Submodule K (CoordinateSpace K n) :=
  subspaceOfClosed {b | Perpendicular b a}
    (by change dotProduct (0 : CoordinateSpace K n) a = 0
        simp only [dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero])
    (fun b hb c hc => by
      change dotProduct (b + c) a = 0
      rw [dot_comm, dot_add, dot_comm a b, dot_comm a c, hb, hc, add_zero])
    (fun c b hb => by
      change dotProduct (c • b) a = 0
      rw [dot_smul, hb, mul_zero])

end LinearAlgebra.Chapter01
