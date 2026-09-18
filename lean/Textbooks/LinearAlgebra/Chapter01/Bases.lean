import Textbooks.LinearAlgebra.Chapter01.VectorSpaces
import Mathlib.LinearAlgebra.Basis.Basic

namespace LinearAlgebra.Chapter01

open scoped BigOperators
open Submodule

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Definition: dependence means a nonzero tuple of coefficients gives zero. -/
def Dependent {ι : Type*} [Fintype ι] (v : ι → V) : Prop :=
  ∃ a : ι → K, linearCombination v a = 0 ∧ a ≠ 0

/-- Proposition: the finite-sum definition agrees with the
negation of Mathlib's standard linear independence. -/
theorem dependent_iff {ι : Type*} [Fintype ι] (v : ι → V) :
    Dependent (K := K) v ↔ ¬LinearIndependent K v := by
  simp only [Dependent, Fintype.not_linearIndependent_iff, linearCombination,
    ne_eq, funext_iff, Pi.zero_apply, not_forall]

/-- Definition: a finite basis is an independent generating family. -/
def IsFiniteBasis {ι : Type*} [Fintype ι] (v : ι → V) : Prop :=
  LinearIndependent K v ∧ Generates (K := K) v

/-- Theorem: coefficients in an independent family are unique. -/
theorem coefficients_unique {ι : Type*} [Fintype ι] {v : ι → V}
    (hv : LinearIndependent K v) {a b : ι → K}
    (h : linearCombination v a = linearCombination v b) : a = b := by
  have hz : ∑ i, (a i - b i) • v i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr h

  have hc := Fintype.linearIndependent_iff.mp hv _ hz

  funext i
  exact sub_eq_zero.mp (hc i)

/-- Theorem: a basis supplies exactly one coordinate tuple. -/
theorem exists_unique_coordinates {ι : Type*} [Fintype ι] {v : ι → V}
    (hv : IsFiniteBasis (K := K) v) (x : V) :
    ∃! a : ι → K, linearCombination v a = x := by
  obtain ⟨a, ha⟩ := hv.2 x

  exact ⟨a, ha, fun b hb => coefficients_unique hv.1 (hb.trans ha.symm)⟩

/-- Definition: the coordinate tuple of a vector in a finite basis. -/
noncomputable def coordinates {ι : Type*} [Fintype ι] {v : ι → V}
    (hv : IsFiniteBasis (K := K) v) (x : V) : ι → K :=
  Classical.choose (hv.2 x)

/-- Theorem: reconstruction from coordinates. -/
theorem combination_coordinates {ι : Type*} [Fintype ι] {v : ι → V}
    (hv : IsFiniteBasis (K := K) v) (x : V) :
    linearCombination v (coordinates hv x) = x := Classical.choose_spec (hv.2 x)

/-- Proposition: independent generating families correspond to bases. -/
theorem finiteBasis_iff {ι : Type*} [Fintype ι] (v : ι → V) :
    IsFiniteBasis (K := K) v ↔ ∃ b : Module.Basis ι K V, ⇑b = v := by
  constructor

  · intro hv

    have hs : (⊤ : Submodule K V) ≤ span K (Set.range v) := by
      intro x _
      exact (mem_span_range_iff_exists_fun K).mpr (hv.2 x)

    exact ⟨Module.Basis.mk hv.1 hs, Module.Basis.coe_mk _ _⟩

  · rintro ⟨b, rfl⟩
    refine ⟨b.linearIndependent, fun x => ?_⟩
    exact (mem_span_range_iff_exists_fun K).mp (by
      rw [b.span_eq]
      trivial)

/-- Definition: standard unit vectors in a coordinate space. -/
def standardVector {n : ℕ} (i : Fin n) : CoordinateSpace K n :=
  fun j => if i = j then 1 else 0

/-- Lemma: combinations of unit vectors evaluate to their coefficients. -/
theorem combination_standard {n : ℕ} (a : Fin n → K) :
    linearCombination (standardVector (K := K)) a = a := by
  funext j
  simp [linearCombination, standardVector, Finset.sum_apply]

/-- Theorem: the coordinate unit vectors form a basis. -/
theorem standard_is_basis (n : ℕ) :
    IsFiniteBasis (K := K) (standardVector (K := K) (n := n)) := by
  refine ⟨Fintype.linearIndependent_iff.mpr ?_, fun x => ⟨x, combination_standard x⟩⟩
  intro a ha i

  have h : a = 0 := (combination_standard a).symm.trans ha

  exact congrFun h i

/-- Definition: maximal independence among a specified set of allowable vectors. -/
def MaximalIndependentIn (s t : Set V) : Prop :=
  s ⊆ t ∧ LinearIndepOn K id s ∧
    ∀ x ∈ t, x ∉ s → ¬LinearIndepOn K id (insert x s)

/-- Definition: maximal independence in the whole space. -/
def MaximalIndependent (s : Set V) : Prop :=
  MaximalIndependentIn (K := K) s Set.univ

/-- Lemma: adjoining a vector outside the span preserves independence.
Separate its coefficient from the remaining finite sum; a nonzero coefficient
would express the new vector in the old span. -/
theorem independent_insert {s : Set V} {x : V} (hs : LinearIndepOn K id s)
    (hx : x ∉ span K s) : LinearIndepOn K id (insert x s) := by
  classical

  apply linearIndepOn_iff'.mpr
  intro t a ht ha i hi
  change ∑ y ∈ t, a y • y = 0 at ha
  by_cases hxt : x ∈ t

  · have ht' : (↑(t.erase x) : Set V) ⊆ s := by
      intro y hy
      exact (ht (Finset.mem_of_mem_erase hy)).resolve_left (Finset.ne_of_mem_erase hy)

    have he : a x • x + ∑ y ∈ t.erase x, a y • y = 0 := by
      rw [← Finset.sum_insert (f := fun y => a y • y) (Finset.notMem_erase x t),
        Finset.insert_erase hxt]
      exact ha

    have hax : a x = 0 := by
      by_contra hn
      apply hx

      have hm : a x • x ∈ span K s := by
        rw [eq_neg_of_add_eq_zero_left he]
        exact (span K s).neg_mem ((span K s).sum_mem fun y hy =>
          (span K s).smul_mem _ (subset_span (ht' hy)))

      have := (span K s).smul_mem (a x)⁻¹ hm

      simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using this

    by_cases hix : i = x

    · simpa only [hix] using hax
    · apply linearIndepOn_iff'.mp hs (t.erase x) a ht' _ i (Finset.mem_erase.mpr ⟨hix, hi⟩)
      simpa only [hax, zero_smul, zero_add, id_eq] using he

  · apply linearIndepOn_iff'.mp hs t a _ ha i hi
    intro y hy
    exact (ht hy).resolve_left (fun he => hxt (he ▸ hy))

/-- Theorem: a maximal independent subset spans all allowable vectors. -/
theorem maximal_spans {s t : Set V} (h : MaximalIndependentIn (K := K) s t) :
    t ⊆ span K s := by
  intro x hx
  by_contra hn
  exact h.2.2 x hx (fun hm => hn (subset_span hm)) (independent_insert h.2.1 hn)

/-- Theorem: a finite maximal independent subset of a generating set
is a basis; this also covers maximal independent subsets of the whole space. -/
theorem maximal_is_basis {s : Finset V} {t : Set V}
    (h : MaximalIndependentIn (K := K) (s : Set V) t) (ht : span K t = ⊤) :
    IsFiniteBasis (K := K) (fun x : s => (x : V)) := by
  refine ⟨h.2.1, fun x => ?_⟩

  have he : span K (s : Set V) = ⊤ := by
    apply top_unique
    rw [← ht]
    exact span_le.mpr (maximal_spans h)

  apply (mem_span_range_iff_exists_fun K).mp
  rw [show Set.range (fun x : s => (x : V)) = (s : Set V) by
    ext
    simp, he]
  trivial

end LinearAlgebra.Chapter01
