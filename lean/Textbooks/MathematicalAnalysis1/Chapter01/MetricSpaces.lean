import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

/-! Metric topology developed from balls and the metric axioms.
The metric ball and open-set characterizations are representational bridges.
Euclidean norm identities are accepted finite-dimensional prerequisites.
All other results below are core results with explicit metric arguments. -/

set_option autoImplicit false

namespace MathematicalAnalysis1.Chapter01

open Set Metric

variable {X : Type*} [MetricSpace X]

/-- Standard metric spaces and Euclidean spaces include the empty coordinate type. -/
abbrev MetricStructure (A : Type*) := MetricSpace A

abbrev Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Balls use distance to the center; metric symmetry matches d(p,q) in print. -/
abbrev neighborhood (p : X) (r : ℝ) : Set X := ball p r

abbrev deletedNeighborhood (p : X) (r : ℝ) : Set X := ball p r \ {p}

noncomputable abbrev interiorPoints (E : Set X) : Set X := interior E

abbrev openSets : Set (Set X) := {E | IsOpen E}

abbrev closedSets : Set (Set X) := {E | IsClosed E}

noncomputable abbrev setClosure (E : Set X) : Set X := closure E

noncomputable abbrev boundary (E : Set X) : Set X := frontier E

abbrev relativeOpen (E Y : Set X) : Prop :=
  E ⊆ Y ∧ IsOpen ((Subtype.val : Y → X) ⁻¹' E)

abbrev relativeClosed (E Y : Set X) : Prop :=
  E ⊆ Y ∧ IsClosed ((Subtype.val : Y → X) ⁻¹' E)

/-- The textbook's boundedness convention also covers an empty ambient space. -/
def bounded (E : Set X) : Prop :=
  Nonempty X → ∃ p : X, ∃ r > 0, E ⊆ ball p r

/-- The textbook's punctured-ball definition of a limit point. -/
def limitPoints (E : Set X) : Set X :=
  {p | ∀ r : ℝ, 0 < r → ∃ q ∈ E, q ≠ p ∧ dist q p < r}

/-- The textbook's isolated points, including membership in the set. -/
def isolatedPoints (E : Set X) : Set X :=
  {p | ∃ r : ℝ, 0 < r ∧ E ∩ ball p r = {p}}

abbrev perfect (E : Set X) : Prop := E = limitPoints E

abbrev dense (E : Set X) : Prop := closure E = univ

/-- Representation bridge for the ball definition of interior points. -/
theorem interior_iff (E : Set X) (p : X) :
    p ∈ interiorPoints E ↔ ∃ r > 0, ball p r ⊆ E := by
  exact mem_interior_iff_mem_nhds.trans Metric.mem_nhds_iff

/-- Representation bridge for the punctured ball's positive-distance formula. -/
theorem deleted_neighborhood_iff (p q : X) (r : ℝ) :
    q ∈ deletedNeighborhood p r ↔ 0 < dist q p ∧ dist q p < r := by
  change (dist q p < r ∧ q ≠ p) ↔ _
  rw [dist_pos]
  exact and_comm

/-- Accepted prerequisite: the Euclidean norm gives a metric. -/
theorem euclidean_metric (n : ℕ) :
    (∀ x y : EuclideanSpace ℝ (Fin n), 0 ≤ ‖x - y‖) ∧
    (∀ x y : EuclideanSpace ℝ (Fin n), ‖x - y‖ = 0 ↔ x = y) ∧
    (∀ x y : EuclideanSpace ℝ (Fin n), ‖x - y‖ = ‖y - x‖) ∧
    (∀ x y z : EuclideanSpace ℝ (Fin n),
      ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖) := by
  refine ⟨fun x y => norm_nonneg _, ?_, ?_, ?_⟩
  · intro x y
    rw [norm_eq_zero, sub_eq_zero]
  · intro x y
    exact norm_sub_rev x y
  · intro x y z
    calc
      ‖x - z‖ = ‖(x - y) + (y - z)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖x - y‖ + ‖y - z‖ := norm_add_le _ _

/-- Core result: a ball is open, using the remaining distance to its edge. -/
theorem ball_open (p : X) (r : ℝ) : IsOpen (ball p r) := by
  apply Metric.isOpen_iff.mpr
  intro q hq
  refine ⟨r - dist q p, sub_pos.mpr hq, ?_⟩
  intro s hs
  change dist s p < r
  have ht := dist_triangle s q p
  change dist s q < r - dist q p at hs
  linarith

/-- Core result: a finite collection of positive numbers has a common
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

/-- Core result: a limit point has infinitely many nearby points. -/
theorem limit_point_infinite (E : Set X) (p : X)
    (hp : p ∈ limitPoints E) (r : ℝ) (hr : 0 < r) :
    (E ∩ ball p r).Infinite := by
  classical
  intro hf
  let s := (hf.subset (show (E ∩ ball p r) \ {p} ⊆ E ∩ ball p r from sdiff_subset)).toFinset
  have hpos : ∀ q ∈ s, 0 < dist q p := by
    intro q hq
    have h := (Set.Finite.mem_toFinset _).mp hq
    exact dist_pos.mpr h.2
  obtain ⟨δ, hδ, hle⟩ := finite_positive_lower_bound s (fun q => dist q p) hpos
  obtain ⟨q, hq, hqp, hdist⟩ := hp (min r δ) (lt_min hr hδ)
  have hqs : q ∈ s := (Set.Finite.mem_toFinset _).mpr
    ⟨⟨hq, hdist.trans_le (min_le_left _ _)⟩, hqp⟩
  exact (not_lt_of_ge (hle q hqs)) (hdist.trans_le (min_le_right _ _))

/-- Core result: complements exchange openness and containing limit points. -/
theorem open_iff_compl_limitPoints (E : Set X) :
    IsOpen E ↔ limitPoints Eᶜ ⊆ Eᶜ := by
  classical
  constructor
  · intro h p hp hpe
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp h p hpe
    obtain ⟨q, hq, _, hd⟩ := hp r hr
    exact hq (hball hd)
  · intro h
    apply Metric.isOpen_iff.mpr
    intro p hp
    by_contra hn
    have hl : p ∈ limitPoints Eᶜ := by
      intro r hr
      have hnsub : ¬ ball p r ⊆ E := fun hs => hn ⟨r, hr, hs⟩
      obtain ⟨q, hq, hqe⟩ := Set.not_subset.mp hnsub
      refine ⟨q, hqe, ?_, hq⟩
      intro heq
      exact hqe (heq.symm ▸ hp)
    exact h hl hp

/-- Representational bridge for the textbook's definition of closedness. -/
theorem closed_iff_limitPoints (E : Set X) :
    IsClosed E ↔ limitPoints E ⊆ E := by
  have h := open_iff_compl_limitPoints Eᶜ
  rw [compl_compl] at h
  exact isOpen_compl_iff.symm.trans h

/-- Core result: an arbitrary union inherits a ball from one member. -/
theorem open_union {ι : Type*} (E : ι → Set X)
    (h : ∀ i, IsOpen (E i)) : IsOpen (⋃ i, E i) := by
  apply Metric.isOpen_iff.mpr
  intro p hp
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp
  obtain ⟨r, hr, hs⟩ := Metric.isOpen_iff.mp (h i) p hi
  exact ⟨r, hr, fun q hq => mem_iUnion.mpr ⟨i, hs hq⟩⟩

/-- Core result: intersections preserve the limit-point condition. -/
theorem closed_intersection {ι : Type*} (E : ι → Set X)
    (h : ∀ i, IsClosed (E i)) : IsClosed (⋂ i, E i) := by
  apply (closed_iff_limitPoints _).mpr
  intro p hp
  apply mem_iInter.mpr
  intro i
  apply (closed_iff_limitPoints _).mp (h i)
  intro r hr
  obtain ⟨q, hq, hn, hd⟩ := hp r hr
  exact ⟨q, mem_iInter.mp hq i, hn, hd⟩

/-- Core result: the smaller of two radii works for an intersection. -/
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

/-- Core result: finite intersections, including the empty intersection. -/
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

/-- Core result: finite unions are obtained by taking complements. -/
theorem closed_finite_union {ι : Type*} (s : Finset ι)
    (E : ι → Set X) (hE : ∀ i ∈ s, IsClosed (E i)) :
    IsClosed (⋃ i ∈ s, E i) := by
  have ho := open_finite_intersection s (fun i => (E i)ᶜ)
    (fun i hi => (hE i hi).isOpen_compl)
  have heq : (⋃ i ∈ s, E i)ᶜ = ⋂ i ∈ s, (E i)ᶜ := by
    ext p
    simp only [mem_compl_iff, mem_iUnion, mem_iInter, not_exists]
  exact isOpen_compl_iff.mp (heq ▸ ho)

/-- Core bridge: the standard closure equals the set plus its limit points. -/
theorem closure_eq_union_limitPoints (E : Set X) :
    closure E = E ∪ limitPoints E := by
  classical
  ext p
  constructor
  · intro hp
    by_cases he : p ∈ E
    · exact Or.inl he
    · right
      intro r hr
      obtain ⟨q, hq, hd⟩ := Metric.mem_closure_iff.mp hp r hr
      exact ⟨q, hq, fun h => he (h ▸ hq), by rwa [dist_comm]⟩
  · intro hp
    apply Metric.mem_closure_iff.mpr
    intro r hr
    rcases hp with hp | hp
    · exact ⟨p, hp, by simpa only [dist_self] using hr⟩
    · obtain ⟨q, hq, _, hd⟩ := hp r hr
      exact ⟨q, hq, by rwa [dist_comm]⟩

/-- Core result: closure contains its own limit points. -/
theorem closure_closed (E : Set X) : IsClosed (closure E) := by
  apply (closed_iff_limitPoints _).mpr
  intro p hp
  apply Metric.mem_closure_iff.mpr
  intro r hr
  obtain ⟨q, hq, _, hdq⟩ := hp (r / 2) (half_pos hr)
  obtain ⟨s, hs, hds⟩ := Metric.mem_closure_iff.mp hq (r / 2) (half_pos hr)
  refine ⟨s, hs, ?_⟩
  have ht := dist_triangle p q s
  rw [dist_comm q p] at hdq
  linarith

/-- Core result: the three universal properties of closure. -/
theorem closure_properties (E : Set X) :
    IsClosed (closure E) ∧ (E = closure E ↔ IsClosed E) ∧
    (∀ F : Set X, IsClosed F → E ⊆ F → closure E ⊆ F) := by
  refine ⟨closure_closed E, ?_, ?_⟩
  · constructor
    · intro h
      rw [h]
      exact closure_closed E
    · intro h
      rw [closure_eq_union_limitPoints]
      exact (union_eq_left.mpr ((closed_iff_limitPoints E).mp h)).symm
  · intro F hF hEF p hp
    rw [closure_eq_union_limitPoints] at hp
    rcases hp with hp | hp
    · exact hEF hp
    · apply (closed_iff_limitPoints F).mp hF
      intro r hr
      obtain ⟨q, hq, hn, hd⟩ := hp r hr
      exact ⟨q, hEF hq, hn, hd⟩

/-- Core result from the accepted least-upper-bound property. -/
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

/-- Core result: an isolated point is exactly a non-limit point in the set. -/
theorem isolated_eq_diff (E : Set X) : isolatedPoints E = E \ limitPoints E := by
  classical
  ext p
  constructor
  · rintro ⟨r, hr, heq⟩
    have hp : p ∈ E ∩ ball p r := heq.symm ▸ (mem_singleton p)
    refine ⟨hp.1, ?_⟩
    intro hl
    obtain ⟨q, hq, hn, hd⟩ := hl r hr
    have hmem : q ∈ E ∩ ball p r := ⟨hq, hd⟩
    rw [heq, mem_singleton_iff] at hmem
    exact hn hmem
  · rintro ⟨hp, hn⟩
    have hex : ∃ r > 0, ∀ q ∈ E, dist q p < r → q = p := by
      by_contra h
      push Not at h
      exact hn (fun r hr => by
        obtain ⟨q, hq, hd, hne⟩ := h r hr
        exact ⟨q, hq, hne, hd⟩)
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

/-- Core result: failure to contain a ball means every ball meets the complement. -/
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

/-- Core result: relative openness is induced by an ambient open set. -/
theorem relative_open (E Y : Set X) (hEY : E ⊆ Y) :
    IsOpen ((Subtype.val : Y → X) ⁻¹' E) ↔
      ∃ V : Set X, IsOpen V ∧ E = V ∩ Y := by
  classical
  constructor
  · intro h
    have hex : ∀ p : E, ∃ r > 0, Y ∩ ball p.val r ⊆ E := by
      intro p
      obtain ⟨r, hr, hs⟩ := Metric.isOpen_iff.mp h ⟨p.val, hEY p.property⟩ p.property
      exact ⟨r, hr, fun q hq => hs (show (⟨q, hq.1⟩ : Y) ∈ ball ⟨p.val, hEY p.property⟩ r from hq.2)⟩
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

/-- Core result: a positive-dimensional Euclidean space has no isolated points. -/
theorem euclidean_punctured_ball (n : ℕ+)
    (p : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) :
    ∃ q : EuclideanSpace ℝ (Fin n), q ≠ p ∧ dist q p < r := by
  let v : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, n.pos⟩ (r / 2)
  have hv : ‖v‖ = r / 2 := by
    rw [PiLp.norm_single, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
  refine ⟨p + v, ?_, ?_⟩
  · intro heq
    have hz : v = 0 := add_left_cancel (heq.trans (add_zero p).symm)
    rw [hz, norm_zero] at hv
    linarith
  · rw [dist_eq_norm, add_sub_cancel_left, hv]
    linarith

/-- Supporting core argument: an isolated point of a set is a limit point
of its complement when the ambient space has no isolated points. -/
theorem isolated_limit_compl (E : Set X)
    (hX : ∀ p : X, ∀ r > 0, ∃ q : X, q ≠ p ∧ dist q p < r) :
    isolatedPoints E ⊆ limitPoints Eᶜ := by
  intro p hp
  obtain ⟨r, hr, heq⟩ := hp
  intro s hs
  obtain ⟨q, hne, hd⟩ := hX p (min r s) (lt_min hr hs)
  refine ⟨q, ?_, hne, hd.trans_le (min_le_right _ _)⟩
  intro hq
  have hm : q ∈ E ∩ ball p r := ⟨hq, hd.trans_le (min_le_left _ _)⟩
  rw [heq, mem_singleton_iff] at hm
  exact hne hm

/-- Core result: decompose the boundary according to the two limit-point sets. -/
theorem euclidean_boundary (n : ℕ+)
    (E : Set (EuclideanSpace ℝ (Fin n))) :
    frontier E = isolatedPoints E ∪ isolatedPoints Eᶜ ∪
      (limitPoints E ∩ limitPoints Eᶜ) := by
  have hE := isolated_limit_compl E (euclidean_punctured_ball n)
  have hEc := isolated_limit_compl Eᶜ (euclidean_punctured_ball n)
  rw [compl_compl] at hEc
  rw [isolated_eq_diff] at hE hEc
  rw [frontier, sdiff_eq_compl_inter,
    compl_interior_eq_closure_compl, closure_eq_union_limitPoints,
    closure_eq_union_limitPoints, isolated_eq_diff, isolated_eq_diff]
  ext p
  have h1 := @hE p
  have h2 := @hEc p
  simp only [mem_inter_iff, mem_union, mem_sdiff, mem_compl_iff] at *
  tauto

/-- Core representation bridge for the two boundary formulas. -/
theorem boundary_eq (E : Set X) :
    boundary E = closure E ∩ closure Eᶜ := by
  change closure E \ interior E = _
  rw [sdiff_eq_compl_inter, compl_interior_eq_closure_compl, inter_comm]

/-- Core representation bridge for relative closedness. -/
theorem relative_closed (E Y : Set X) (hEY : E ⊆ Y) :
    IsClosed ((Subtype.val : Y → X) ⁻¹' E) ↔ limitPoints E ∩ Y ⊆ E := by
  rw [closed_iff_limitPoints]
  constructor
  · intro h p hp
    apply h (show (⟨p, hp.2⟩ : Y) ∈ limitPoints (Subtype.val ⁻¹' E) from ?_)
    intro r hr
    obtain ⟨q, hq, hne, hd⟩ := hp.1 r hr
    refine ⟨⟨q, hEY hq⟩, hq, ?_, hd⟩
    intro heq
    exact hne (congrArg Subtype.val heq)
  · intro h p hp
    apply h
    refine ⟨?_, p.property⟩
    intro r hr
    obtain ⟨q, hq, hne, hd⟩ := hp r hr
    exact ⟨q.val, hq, fun heq => hne (Subtype.ext heq), hd⟩

/-- Accepted metric axioms on a subtype: distances are unchanged. -/
theorem subspace_metric (Y : Set X) (p q z : Y) :
    dist p q = dist p.val q.val ∧ 0 ≤ dist p q ∧
    (dist p q = 0 ↔ p = q) ∧ dist p q = dist q p ∧
    dist p z ≤ dist p q + dist q z := by
  exact ⟨rfl, dist_nonneg, dist_eq_zero, dist_comm _ _, dist_triangle _ _ _⟩

/-- Core zero-dimensional case: there is only one vector and no deleted ball. -/
theorem zero_dimensional (p q : EuclideanSpace ℝ (Fin 0)) (r : ℝ) :
    p = q ∧ deletedNeighborhood p r = ∅ := by
  have heq : ∀ x y : EuclideanSpace ℝ (Fin 0), x = y := by
    intro x y
    ext j
    exact Fin.elim0 j
  refine ⟨heq p q, ?_⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hx.2 (heq x p)

end MathematicalAnalysis1.Chapter01
