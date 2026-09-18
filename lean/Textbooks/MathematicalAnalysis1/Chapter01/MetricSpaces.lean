import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.DerivedSet
import Mathlib.Topology.Perfect
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-! Metric topology developed from balls and the metric axioms.
Use Mathlib's metric interfaces directly; the core results use explicit metric arguments.
The owning book policy specifies this boundary. -/

set_option autoImplicit false

namespace MathematicalAnalysis1.Chapter01

open Set Metric

variable {X : Type*} [MetricSpace X]

/-- Lemma: the standard derived set has the punctured-ball characterization. -/
theorem mem_derivedSet_iff (E : Set X) (p : X) :
    p ∈ derivedSet E ↔ ∀ r : ℝ, 0 < r → ∃ q ∈ E, q ≠ p ∧ dist q p < r := by
  rw [mem_derivedSet, accPt_iff_nhds]
  constructor

  · intro h r hr
    obtain ⟨q, ⟨hq, hE⟩, hne⟩ := h (ball p r) (Metric.ball_mem_nhds p hr)
    exact ⟨q, hE, hne, hq⟩

  · intro h U hU
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hU
    obtain ⟨q, hE, hne, hq⟩ := h r hr
    exact ⟨q, ⟨hsub hq, hE⟩, hne⟩

/-- Definition: an isolated point belongs to E and is alone in some ball. -/
def isolatedPoints (E : Set X) : Set X :=
  {p | ∃ r : ℝ, 0 < r ∧ E ∩ ball p r = {p}}

/-- Lemma: boundedness is containment in a ball when the ambient space is nonempty.
The pairwise-distance characterization also covers the empty space. -/
theorem isBounded_iff (E : Set X) :
    Bornology.IsBounded E ↔ (Nonempty X → ∃ p : X, ∃ r > 0, E ⊆ ball p r) := by
  rw [Metric.isBounded_iff]
  constructor

  · rintro ⟨C, hC⟩ hX
    rcases E.eq_empty_or_nonempty with rfl | ⟨p, hp⟩

    · obtain ⟨p⟩ := hX
      exact ⟨p, 1, zero_lt_one, empty_subset _⟩

    · refine ⟨p, max C 0 + 1, by linarith [le_max_right C 0], ?_⟩
      intro q hq
      exact (hC hq hp).trans_lt (by linarith [le_max_left C 0])

  · intro h
    by_cases hX : Nonempty X

    · obtain ⟨p, r, _, hs⟩ := h hX
      refine ⟨r + r, ?_⟩
      intro x hx y hy
      have hx' : dist x p < r := hs hx
      have hy' : dist p y < r := by simpa only [mem_ball, dist_comm] using hs hy
      exact (dist_triangle x p y).trans (add_le_add hx'.le hy'.le)

    · refine ⟨0, ?_⟩
      intro x
      exact (hX ⟨x⟩).elim

/-- Proposition: a ball is open, using the remaining distance to its edge. -/
theorem ball_open (p : X) (r : ℝ) : IsOpen (ball p r) := by
  apply Metric.isOpen_iff.mpr
  intro q hq
  refine ⟨r - dist q p, sub_pos.mpr hq, ?_⟩
  intro s hs
  change dist s p < r

  have ht := dist_triangle s q p

  change dist s q < r - dist q p at hs
  linarith

/-- Lemma: a finite collection of positive numbers has a common
positive lower bound. The empty collection is included. -/
theorem finite_positive_lower_bound {ι : Type*} (s : Finset ι)
    (r : ι → ℝ) (hr : ∀ i ∈ s, 0 < r i) :
    ∃ δ > 0, ∀ i ∈ s, δ ≤ r i := by
  classical

  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp only [Finset.notMem_empty, false_implies, implies_true]⟩
  | @insert i s hi ih =>
    obtain ⟨δ, hδ, hle⟩ := ih (fun j hj => hr j (Finset.mem_insert_of_mem hj))

    refine ⟨min (r i) δ, lt_min (hr i (Finset.mem_insert_self i s)) hδ, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj

    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hle j hj)

/-- Proposition: a limit point has infinitely many nearby points. -/
theorem limit_point_infinite (E : Set X) (p : X)
    (hp : p ∈ derivedSet E) (r : ℝ) (hr : 0 < r) :
    (E ∩ ball p r).Infinite := by
  classical

  intro hf

  let s := (hf.subset (show (E ∩ ball p r) \ {p} ⊆ E ∩ ball p r from sdiff_subset)).toFinset

  have hpos : ∀ q ∈ s, 0 < dist q p := by
    intro q hq

    have h := (Set.Finite.mem_toFinset _).mp hq

    exact dist_pos.mpr h.2

  obtain ⟨δ, hδ, hle⟩ := finite_positive_lower_bound s (fun q => dist q p) hpos
  obtain ⟨q, hq, hqp, hdist⟩ := (mem_derivedSet_iff E p).mp hp (min r δ) (lt_min hr hδ)

  have hqs : q ∈ s := (Set.Finite.mem_toFinset _).mpr
    ⟨⟨hq, hdist.trans_le (min_le_left _ _)⟩, hqp⟩

  exact (not_lt_of_ge (hle q hqs)) (hdist.trans_le (min_le_right _ _))

/-- Proposition: complements exchange openness and containing limit points. -/
theorem open_iff_compl_derivedSet (E : Set X) :
    IsOpen E ↔ derivedSet Eᶜ ⊆ Eᶜ := by
  classical

  constructor

  · intro h p hp hpe

    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp h p hpe
    obtain ⟨q, hq, _, hd⟩ := (mem_derivedSet_iff _ _).mp hp r hr

    exact hq (hball hd)

  · intro h
    apply Metric.isOpen_iff.mpr
    intro p hp
    by_contra hn

    have hl : p ∈ derivedSet Eᶜ := by
      rw [mem_derivedSet_iff]
      intro r hr

      have hnsub : ¬ ball p r ⊆ E := fun hs => hn ⟨r, hr, hs⟩

      obtain ⟨q, hq, hqe⟩ := Set.not_subset.mp hnsub

      refine ⟨q, hqe, ?_, hq⟩
      intro heq
      exact hqe (heq.symm ▸ hp)

    exact h hl hp

/-- Lemma: Representational bridge for the textbook's definition of closedness. -/
theorem closed_iff_derivedSet (E : Set X) :
    IsClosed E ↔ derivedSet E ⊆ E := by
  have h := open_iff_compl_derivedSet Eᶜ

  rw [compl_compl] at h
  exact isOpen_compl_iff.symm.trans h

/-- Lemma: a perfect set equals its derived set, including the empty set. -/
theorem perfect_iff (E : Set X) : Perfect E ↔ E = derivedSet E := by
  rw [perfect_def]
  change (IsClosed E ∧ E ⊆ derivedSet E) ↔ E = derivedSet E
  rw [closed_iff_derivedSet]
  exact ⟨fun h => subset_antisymm h.2 h.1, fun h => ⟨h.symm.subset, h.subset⟩⟩

/-- Proposition: an arbitrary union inherits a ball from one member. -/
theorem open_union {ι : Type*} (E : ι → Set X)
    (h : ∀ i, IsOpen (E i)) : IsOpen (⋃ i, E i) := by
  apply Metric.isOpen_iff.mpr
  intro p hp

  obtain ⟨i, hi⟩ := mem_iUnion.mp hp
  obtain ⟨r, hr, hs⟩ := Metric.isOpen_iff.mp (h i) p hi

  exact ⟨r, hr, fun q hq => mem_iUnion.mpr ⟨i, hs hq⟩⟩

/-- Corollary: intersections preserve the limit-point condition. -/
theorem closed_intersection {ι : Type*} (E : ι → Set X)
    (h : ∀ i, IsClosed (E i)) : IsClosed (⋂ i, E i) := by
  apply (closed_iff_derivedSet _).mpr
  intro p hp
  apply mem_iInter.mpr
  intro i
  apply (closed_iff_derivedSet _).mp (h i)
  rw [mem_derivedSet_iff]
  intro r hr

  obtain ⟨q, hq, hn, hd⟩ := (mem_derivedSet_iff _ _).mp hp r hr

  exact ⟨q, mem_iInter.mp hq i, hn, hd⟩

/-- Lemma: the smaller of two radii works for an intersection. -/
theorem open_intersection (E F : Set X) (hE : IsOpen E) (hF : IsOpen F) :
    IsOpen (E ∩ F) := by
  apply Metric.isOpen_iff.mpr
  intro p hp

  obtain ⟨r, hr, hEr⟩ := Metric.isOpen_iff.mp hE p hp.1
  obtain ⟨s, hs, hFs⟩ := Metric.isOpen_iff.mp hF p hp.2

  refine ⟨min r s, lt_min hr hs, ?_⟩
  intro q hq
  change dist q p < min r s at hq
  exact ⟨hEr (hq.trans_le (min_le_left _ _)), hFs (hq.trans_le (min_le_right _ _))⟩

/-- Proposition: finite intersections, including the empty intersection. -/
theorem open_finite_intersection {ι : Type*} (s : Finset ι)
    (E : ι → Set X) (hE : ∀ i ∈ s, IsOpen (E i)) :
    IsOpen (⋂ i ∈ s, E i) := by
  classical

  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, iInter_of_empty, iInter_univ]
    exact Metric.isOpen_iff.mpr (fun p _ => ⟨1, zero_lt_one, subset_univ _⟩)

  | @insert i s hi ih =>
    rw [Finset.set_biInter_insert]
    exact open_intersection _ _ (hE i (Finset.mem_insert_self i s))
      (ih (fun j hj => hE j (Finset.mem_insert_of_mem hj)))

/-- Corollary: finite unions are obtained by taking complements. -/
theorem closed_finite_union {ι : Type*} (s : Finset ι)
    (E : ι → Set X) (hE : ∀ i ∈ s, IsClosed (E i)) :
    IsClosed (⋃ i ∈ s, E i) := by
  have ho := open_finite_intersection s (fun i => (E i)ᶜ)
    (fun i hi => (hE i hi).isOpen_compl)

  have heq : (⋃ i ∈ s, E i)ᶜ = ⋂ i ∈ s, (E i)ᶜ := by
    ext p
    simp only [mem_compl_iff, mem_iUnion, mem_iInter, not_exists]

  exact isOpen_compl_iff.mp (heq ▸ ho)

/-- Lemma: the standard closure equals the set plus its limit points. -/
theorem closure_eq_union_derivedSet (E : Set X) :
    closure E = E ∪ derivedSet E := by
  classical

  ext p
  constructor

  · intro hp
    by_cases he : p ∈ E

    · exact Or.inl he
    · right
      rw [mem_derivedSet_iff]
      intro r hr

      obtain ⟨q, hq, hd⟩ := Metric.mem_closure_iff.mp hp r hr

      exact ⟨q, hq, fun h => he (h ▸ hq), by rwa [dist_comm]⟩

  · intro hp
    apply Metric.mem_closure_iff.mpr
    intro r hr
    rcases hp with hp | hp

    · exact ⟨p, hp, by simpa only [dist_self] using hr⟩

    · obtain ⟨q, hq, _, hd⟩ := (mem_derivedSet_iff _ _).mp hp r hr

      exact ⟨q, hq, by rwa [dist_comm]⟩

/-- Lemma: a set is contained in its closure by the proved union characterization.
Mathlib counterpart: `subset_closure`. -/
theorem subset_closure (E : Set X) : E ⊆ closure E := by
  rw [closure_eq_union_derivedSet]
  exact fun _ hp => Or.inl hp

/-- Lemma: closure contains its own limit points. -/
theorem closure_closed (E : Set X) : IsClosed (closure E) := by
  apply (closed_iff_derivedSet _).mpr
  intro p hp
  apply Metric.mem_closure_iff.mpr
  intro r hr

  obtain ⟨q, hq, _, hdq⟩ := (mem_derivedSet_iff _ _).mp hp (r / 2) (half_pos hr)
  obtain ⟨s, hs, hds⟩ := Metric.mem_closure_iff.mp hq (r / 2) (half_pos hr)

  refine ⟨s, hs, ?_⟩

  have ht := dist_triangle p q s

  rw [dist_comm q p] at hdq
  linarith

/-- Proposition: the three universal properties of closure. -/
theorem closure_properties (E : Set X) :
    IsClosed (closure E) ∧ (E = closure E ↔ IsClosed E) ∧
    (∀ F : Set X, IsClosed F → E ⊆ F → closure E ⊆ F) := by
  refine ⟨closure_closed E, ?_, ?_⟩

  · constructor
    · intro h
      rw [h]
      exact closure_closed E

    · intro h
      rw [closure_eq_union_derivedSet]
      exact (union_eq_left.mpr ((closed_iff_derivedSet E).mp h)).symm

  · intro F hF hEF p hp
    rw [closure_eq_union_derivedSet] at hp
    rcases hp with hp | hp

    · exact hEF hp
    · apply (closed_iff_derivedSet F).mp hF
      rw [mem_derivedSet_iff]
      intro r hr

      obtain ⟨q, hq, hn, hd⟩ := (mem_derivedSet_iff _ _).mp hp r hr

      exact ⟨q, hEF hq, hn, hd⟩

/-- Proposition: the supremum lies in the closure, by the accepted least-upper-bound property. -/
theorem supremum_in_closure (E : Set ℝ) (hne : E.Nonempty) (hb : BddAbove E) :
    sSup E ∈ closure E ∧ (IsClosed E → sSup E ∈ E) := by
  have hc : sSup E ∈ closure E := by
    apply Metric.mem_closure_iff.mpr
    intro r hr

    obtain ⟨q, hq, hlt⟩ := exists_lt_of_lt_csSup hne (sub_lt_self (sSup E) hr)

    refine ⟨q, hq, ?_⟩
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (le_csSup hb hq))]
    linarith

  exact ⟨hc, fun h => by
    have heq := (closure_properties E).2.1.mpr h

    rw [← heq] at hc
    exact hc⟩

/-- Proposition: an isolated point is exactly a non-limit point in the set. -/
theorem isolated_eq_diff (E : Set X) : isolatedPoints E = E \ derivedSet E := by
  classical

  ext p
  constructor

  · rintro ⟨r, hr, heq⟩

    have hp : p ∈ E ∩ ball p r := heq.symm ▸ (mem_singleton p)

    refine ⟨hp.1, ?_⟩
    intro hl

    obtain ⟨q, hq, hn, hd⟩ := (mem_derivedSet_iff _ _).mp hl r hr

    have hmem : q ∈ E ∩ ball p r := ⟨hq, hd⟩

    rw [heq, mem_singleton_iff] at hmem
    exact hn hmem

  · rintro ⟨hp, hn⟩

    have hex : ∃ r > 0, ∀ q ∈ E, dist q p < r → q = p := by
      by_contra h
      push Not at h
      apply hn
      rw [mem_derivedSet_iff]
      intro r hr

      obtain ⟨q, hq, hd, hne⟩ := h r hr

      exact ⟨q, hq, hne, hd⟩

    obtain ⟨r, hr, h⟩ := hex

    refine ⟨r, hr, ?_⟩
    ext q
    constructor

    · intro hq
      exact h q hq.1 hq.2

    · intro hq
      rw [mem_singleton_iff] at hq
      subst q
      exact ⟨hp, by simpa only [mem_ball, dist_self] using hr⟩

/-- Lemma: failure to contain a ball means every ball meets the complement. -/
theorem compl_interior_eq_closure_compl (E : Set X) :
    (interior E)ᶜ = closure Eᶜ := by
  classical

  ext p
  rw [mem_compl_iff, mem_interior_iff_mem_nhds, Metric.mem_nhds_iff,
    Metric.mem_closure_iff]
  constructor

  · intro h r hr

    have hn : ¬ ball p r ⊆ E := fun hs => h ⟨r, hr, hs⟩

    obtain ⟨q, hq, hqe⟩ := Set.not_subset.mp hn

    exact ⟨q, hqe, by rwa [dist_comm]⟩

  · intro h ⟨r, hr, hs⟩

    obtain ⟨q, hq, hd⟩ := h r hr

    exact hq (hs (by simpa only [mem_ball, dist_comm] using hd))

/-- Proposition: relative openness is induced by an ambient open set. -/
theorem relative_open (E Y : Set X) (hEY : E ⊆ Y) :
    IsOpen ((Subtype.val : Y → X) ⁻¹' E) ↔
      ∃ V : Set X, IsOpen V ∧ E = V ∩ Y := by
  classical

  constructor

  · intro h

    have hex : ∀ p : E, ∃ r > 0, Y ∩ ball p.val r ⊆ E := by
      intro p

      obtain ⟨r, hr, hs⟩ := Metric.isOpen_iff.mp h ⟨p.val, hEY p.property⟩ p.property

      exact ⟨r, hr, fun q hq =>
        hs (show (⟨q, hq.1⟩ : Y) ∈ ball ⟨p.val, hEY p.property⟩ r from hq.2)⟩

    choose r hr hs using hex

    refine ⟨⋃ p : E, ball p.val (r p), open_union _ (fun p => ball_open _ _), ?_⟩
    ext q
    constructor

    · intro hq
      exact ⟨mem_iUnion.mpr ⟨⟨q, hq⟩, by simpa only [mem_ball, dist_self] using hr ⟨q, hq⟩⟩, hEY hq⟩

    · rintro ⟨hq, hy⟩

      obtain ⟨p, hp⟩ := mem_iUnion.mp hq

      exact hs p ⟨hy, hp⟩

  · rintro ⟨V, hV, heq⟩
    apply Metric.isOpen_iff.mpr
    intro p hp

    have hpV : p.val ∈ V := (show p.val ∈ V ∩ Y from heq ▸ hp).1

    obtain ⟨r, hr, hs⟩ := Metric.isOpen_iff.mp hV p.val hpV

    refine ⟨r, hr, ?_⟩
    intro q hq
    change q.val ∈ E
    rw [heq]
    exact ⟨hs hq, q.property⟩

/-- Lemma: an isolated point of a set is a limit point
of its complement when the ambient space has no isolated points. -/
theorem isolated_limit_compl (E : Set X)
    (hX : ∀ p : X, ∀ r > 0, ∃ q : X, q ≠ p ∧ dist q p < r) :
    isolatedPoints E ⊆ derivedSet Eᶜ := by
  intro p hp

  obtain ⟨r, hr, heq⟩ := hp

  rw [mem_derivedSet_iff]
  intro s hs

  obtain ⟨q, hne, hd⟩ := hX p (min r s) (lt_min hr hs)

  refine ⟨q, ?_, hne, hd.trans_le (min_le_right _ _)⟩
  intro hq

  have hm : q ∈ E ∩ ball p r := ⟨hq, hd.trans_le (min_le_left _ _)⟩

  rw [heq, mem_singleton_iff] at hm
  exact hne hm

/-- Lemma: the boundary definition agrees with the standard closures. -/
theorem boundary_eq (E : Set X) :
    frontier E = closure E ∩ closure Eᶜ := by
  rw [frontier, sdiff_eq_compl_inter, compl_interior_eq_closure_compl, inter_comm]

/-- Lemma: relative closedness is characterized by ambient limit points. -/
theorem relative_closed (E Y : Set X) (hEY : E ⊆ Y) :
    IsClosed ((Subtype.val : Y → X) ⁻¹' E) ↔ derivedSet E ∩ Y ⊆ E := by
  rw [closed_iff_derivedSet]
  constructor

  · intro h p hp
    apply h (show (⟨p, hp.2⟩ : Y) ∈ derivedSet (Subtype.val ⁻¹' E) from ?_)
    rw [mem_derivedSet_iff]
    intro r hr

    obtain ⟨q, hq, hne, hd⟩ := (mem_derivedSet_iff _ _).mp hp.1 r hr

    refine ⟨⟨q, hEY hq⟩, hq, ?_, hd⟩
    intro heq
    exact hne (congrArg Subtype.val heq)

  · intro h p hp
    apply h
    refine ⟨?_, p.property⟩
    rw [mem_derivedSet_iff]
    intro r hr

    obtain ⟨q, hq, hne, hd⟩ := (mem_derivedSet_iff _ _).mp hp r hr

    exact ⟨q.val, hq, fun heq => hne (Subtype.ext heq), hd⟩

/-- Proposition: the inherited subtype distance satisfies the ambient metric axioms. -/
theorem subspace_metric (Y : Set X) (p q z : Y) :
    dist p q = dist p.val q.val ∧ 0 ≤ dist p q ∧
    (dist p q = 0 ↔ p = q) ∧ dist p q = dist q p ∧
    dist p z ≤ dist p q + dist q z := by
  exact ⟨rfl, dist_nonneg, dist_eq_zero, dist_comm _ _, dist_triangle _ _ _⟩

end MathematicalAnalysis1.Chapter01
