import Textbooks.MathematicalAnalysis1.Chapter01.MetricSpaces
import Mathlib.Topology.Compactness.Compact

/-! Core compactness results from the finite-open-subcover definition.
`isCompact_iff_finite_subcover` only translates Mathlib's filter representation.
No compactness, sequential compactness, or completeness theorem is used as a
substitute for the arguments below. -/

set_option autoImplicit false

namespace MathematicalAnalysis1.Chapter01

open Set Metric

variable {X : Type*} [MetricSpace X]

/-- Open covers and subcovers retain the original index set. -/
abbrev openCover {ι : Type*} (E : Set X) (U : ι → Set X) : Prop :=
  (∀ i, IsOpen (U i)) ∧ E ⊆ ⋃ i, U i

abbrev subcover {ι : Type*} (E : Set X) (U : ι → Set X) (S : Set ι) : Prop :=
  E ⊆ ⋃ i ∈ S, U i

abbrev compactSets : Set (Set X) := {E | IsCompact E}

/-- Core result: a finite union of balls avoiding an exterior point still
avoids a sufficiently small ball about that point. -/
theorem compact_closed (E : Set X) (hE : IsCompact E) : IsClosed E := by
  classical
  apply isOpen_compl_iff.mp
  apply Metric.isOpen_iff.mpr
  intro p hp
  let r : E → ℝ := fun q => dist q.val p / 2
  have hr : ∀ q : E, 0 < r q := by
    intro q
    exact half_pos (dist_pos.mpr (fun heq => hp (heq ▸ q.property)))
  have hcover : E ⊆ ⋃ q : E, ball q.val (r q) := by
    intro q hq
    exact mem_iUnion.mpr ⟨⟨q, hq⟩, by simpa only [mem_ball, dist_self] using hr ⟨q, hq⟩⟩
  obtain ⟨s, hs⟩ := hE.elim_finite_subcover _ (fun q => ball_open _ _) hcover
  obtain ⟨δ, hδ, hle⟩ := finite_positive_lower_bound s r (fun q _ => hr q)
  refine ⟨δ, hδ, ?_⟩
  intro x hx hxe
  obtain ⟨q, hq⟩ := mem_iUnion.mp (hs hxe)
  obtain ⟨hqs, hxq⟩ := mem_iUnion.mp hq
  have hd := dist_triangle q.val x p
  rw [dist_comm q.val x] at hd
  have hδq := hle q hqs
  change dist x p < δ at hx
  change dist x q.val < dist q.val p / 2 at hxq
  change δ ≤ dist q.val p / 2 at hδq
  linarith

/-- Core result: concentric balls cover the whole space; a finite subcover
has a common bound, obtained here by a finite sum. -/
theorem compact_bounded (E : Set X) (hE : IsCompact E) : bounded E := by
  classical
  intro hX
  obtain ⟨p⟩ := hX
  have hc : E ⊆ ⋃ n : ℕ, ball p (n + 1 : ℝ) := by
    intro q _
    obtain ⟨n, hn⟩ := exists_nat_gt (dist q p)
    exact mem_iUnion.mpr ⟨n, by change dist q p < (n : ℝ) + 1; linarith⟩
  obtain ⟨s, hs⟩ := hE.elim_finite_subcover _ (fun n => ball_open _ _) hc
  let R : ℝ := 1 + ∑ n ∈ s, (n + 1 : ℝ)
  have hnonneg : 0 ≤ ∑ n ∈ s, (n + 1 : ℝ) :=
    Finset.sum_nonneg (fun n _ => by positivity)
  refine ⟨p, R, by dsimp [R]; linarith, ?_⟩
  intro q hq
  obtain ⟨n, hn⟩ := mem_iUnion.mp (hs hq)
  obtain ⟨hns, hdist⟩ := mem_iUnion.mp hn
  have hle : (n + 1 : ℝ) ≤ ∑ k ∈ s, (k + 1 : ℝ) :=
    Finset.single_le_sum (f := fun k : ℕ => (k + 1 : ℝ)) (fun k _ => by positivity) hns
  change dist q p < R
  change dist q p < (n + 1 : ℝ) at hdist
  dsimp [R]
  linarith

/-- Core result: append the open complement to cover a closed subset. -/
theorem closed_subset_compact (E F : Set X) (hE : IsCompact E)
    (hF : IsClosed F) (hFE : F ⊆ E) : IsCompact F := by
  classical
  apply isCompact_of_finite_subcover
  intro ι U hU hcover
  let V : Option ι → Set X := fun i => match i with
    | none => Fᶜ
    | some j => U j
  have hV : ∀ i, IsOpen (V i) := by
    intro i
    cases i with
    | none => exact hF.isOpen_compl
    | some j => exact hU j
  have hc : E ⊆ ⋃ i, V i := by
    intro x _
    by_cases hx : x ∈ F
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
      exact mem_iUnion.mpr ⟨some i, hi⟩
    · exact mem_iUnion.mpr ⟨none, hx⟩
  obtain ⟨s, hs⟩ := hE.elim_finite_subcover V hV hc
  refine ⟨s.biUnion Option.toFinset, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hs (hFE hx))
  obtain ⟨his, hxi⟩ := mem_iUnion.mp hi
  cases i with
  | none => exact False.elim (hxi hx)
  | some j =>
    exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨Finset.mem_biUnion.mpr ⟨some j, his, by simp⟩, hxi⟩⟩

/-- Core result: if every point has a ball meeting F at most at its center,
a finite subcover would force F to be finite. -/
theorem infinite_subset_limit_point (E F : Set X) (hE : IsCompact E)
    (hFE : F ⊆ E) (hF : F.Infinite) : (limitPoints F ∩ E).Nonempty := by
  classical
  by_contra hn
  have hlocal : ∀ p : E, ∃ r > 0, ∀ q ∈ F, dist q p.val < r → q = p.val := by
    intro p
    by_contra h
    push Not at h
    apply hn
    refine ⟨p.val, ?_, p.property⟩
    intro r hr
    obtain ⟨q, hq, hd, hne⟩ := h r hr
    exact ⟨q, hq, hne, hd⟩
  choose r hr hsingle using hlocal
  have hc : E ⊆ ⋃ p : E, ball p.val (r p) := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, by simpa only [mem_ball, dist_self] using hr ⟨p, hp⟩⟩
  obtain ⟨s, hs⟩ := hE.elim_finite_subcover _ (fun p => ball_open _ _) hc
  apply hF
  apply (s.finite_toSet.image Subtype.val).subset
  intro q hq
  obtain ⟨p, hp⟩ := mem_iUnion.mp (hs (hFE hq))
  obtain ⟨hps, hd⟩ := mem_iUnion.mp hp
  exact ⟨p, hps, (hsingle p q hq hd).symm⟩

/-- Core result: compactness is unchanged on passage to a metric subspace. -/
theorem compact_subspace (E Y : Set X) (hEY : E ⊆ Y) :
    IsCompact ((Subtype.val : Y → X) ⁻¹' E) ↔ IsCompact E := by
  classical
  constructor
  · intro h
    apply isCompact_of_finite_subcover
    intro ι U hU hc
    have ho : ∀ i, IsOpen ((Subtype.val : Y → X) ⁻¹' U i) := by
      intro i
      apply Metric.isOpen_iff.mpr
      intro p hp
      obtain ⟨r, hr, hs⟩ := Metric.isOpen_iff.mp (hU i) p.val hp
      exact ⟨r, hr, fun q hq => hs hq⟩
    have hcov : (Subtype.val : Y → X) ⁻¹' E ⊆ ⋃ i, Subtype.val ⁻¹' U i := by
      intro p hp
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hc hp)
      exact mem_iUnion.mpr ⟨i, hi⟩
    obtain ⟨s, hs⟩ := h.elim_finite_subcover _ ho hcov
    refine ⟨s, ?_⟩
    intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hs (show (⟨p, hEY hp⟩ : Y) ∈ Subtype.val ⁻¹' E from hp))
    obtain ⟨his, hpi⟩ := mem_iUnion.mp hi
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨his, hpi⟩⟩
  · intro h
    apply isCompact_of_finite_subcover
    intro ι U hU hc
    have hex : ∀ i, ∃ V : Set X, IsOpen V ∧ Subtype.val '' U i = V ∩ Y := by
      intro i
      apply (relative_open _ Y (by rintro x ⟨p, _, rfl⟩; exact p.property)).mp
      have heq : (Subtype.val : Y → X) ⁻¹' (Subtype.val '' U i) = U i :=
        preimage_image_eq _ Subtype.val_injective
      rw [heq]
      exact hU i
    choose V hV heq using hex
    have hcov : E ⊆ ⋃ i, V i := by
      intro p hp
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hc (show (⟨p, hEY hp⟩ : Y) ∈ Subtype.val ⁻¹' E from hp))
      have hm : p ∈ Subtype.val '' U i := ⟨⟨p, hEY hp⟩, hi, rfl⟩
      rw [heq i] at hm
      exact mem_iUnion.mpr ⟨i, hm.1⟩
    obtain ⟨s, hs⟩ := h.elim_finite_subcover V hV hcov
    refine ⟨s, ?_⟩
    intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hs hp)
    obtain ⟨his, hpi⟩ := mem_iUnion.mp hi
    have hm : p.val ∈ Subtype.val '' U i := (heq i).symm ▸ ⟨hpi, p.property⟩
    obtain ⟨q, hq, he⟩ := hm
    have hqp : q = p := Subtype.ext he
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨his, hqp ▸ hq⟩⟩

/-- Core result: the empty indexing family is covered by its FIP hypothesis. -/
theorem compact_finite_intersection {ι : Type*} (K : ι → Set X)
    (hK : ∀ i, IsCompact (K i))
    (hfinite : ∀ s : Finset ι, (⋂ i ∈ s, K i).Nonempty) :
    (⋂ i, K i).Nonempty := by
  classical
  by_cases hi : Nonempty ι
  · obtain ⟨i₀⟩ := hi
    by_contra hn
    have hc : K i₀ ⊆ ⋃ i, (K i)ᶜ := by
      intro p _
      by_contra hp
      apply hn
      refine ⟨p, mem_iInter.mpr ?_⟩
      intro i
      by_contra hpi
      exact hp (mem_iUnion.mpr ⟨i, hpi⟩)
    obtain ⟨s, hs⟩ := (hK i₀).elim_finite_subcover _
      (fun i => (compact_closed _ (hK i)).isOpen_compl) hc
    obtain ⟨p, hp⟩ := hfinite (insert i₀ s)
    have hp0 := mem_iInter.mp (mem_iInter.mp hp i₀) (Finset.mem_insert_self _ _)
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hs hp0)
    obtain ⟨his, hpi⟩ := mem_iUnion.mp hi
    exact hpi (mem_iInter.mp (mem_iInter.mp hp i) (Finset.mem_insert_of_mem his))
  · obtain ⟨p, _⟩ := hfinite ∅
    refine ⟨p, mem_iInter.mpr ?_⟩
    intro i
    exact False.elim (hi ⟨i⟩)

/-- Core result from real least upper bounds, not compactness. -/
theorem nested_intervals (a b : ℕ → ℝ)
    (h : ∀ n, a n ≤ a (n + 1) ∧ a (n + 1) ≤ b (n + 1) ∧ b (n + 1) ≤ b n) :
    ∃ x : ℝ, ∀ n, a n ≤ x ∧ x ≤ b n := by
  have ha : Monotone a := monotone_nat_of_le_succ (fun n => (h n).1)
  have hb : Antitone b := antitone_nat_of_succ_le (fun n => (h n).2.2)
  have hab : ∀ n, a n ≤ b n := fun n => (h n).1.trans ((h n).2.1.trans (h n).2.2)
  have hcross : ∀ n m, a n ≤ b m := by
    intro n m
    rcases le_total n m with hnm | hmn
    · exact (ha hnm).trans (hab m)
    · exact (hab n).trans (hb hmn)
  have hne : (range a).Nonempty := ⟨a 0, mem_range_self 0⟩
  have hbd : BddAbove (range a) := ⟨b 0, by rintro x ⟨n, rfl⟩; exact hcross n 0⟩
  refine ⟨sSup (range a), ?_⟩
  intro n
  exact ⟨le_csSup hbd (mem_range_self n), csSup_le hne (by rintro x ⟨m, rfl⟩; exact hcross m n)⟩

/-- Core result: choose one point in each nested coordinate interval. -/
theorem nested_cells (k : ℕ) (a b : ℕ → Fin k → ℝ)
    (h : ∀ n j, a n j ≤ a (n + 1) j ∧
      a (n + 1) j ≤ b (n + 1) j ∧ b (n + 1) j ≤ b n j) :
    ∃ x : EuclideanSpace ℝ (Fin k), ∀ n j, a n j ≤ x j ∧ x j ≤ b n j := by
  have hex : ∀ j, ∃ x : ℝ, ∀ n, a n j ≤ x ∧ x ≤ b n j :=
    fun j => nested_intervals (fun n => a n j) (fun n => b n j) (fun n => h n j)
  choose x hx using hex
  exact ⟨WithLp.toLp 2 x, fun n j => hx j n⟩

/-- Supporting core result: pull an open cover back along a continuous map. -/
theorem compact_image {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (K : Set A) (hK : IsCompact K) (f : A → B) (hf : Continuous f) :
    IsCompact (f '' K) := by
  apply isCompact_of_finite_subcover
  intro ι U hU hc
  have hcov : K ⊆ ⋃ i, f ⁻¹' U i := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hc ⟨x, hx, rfl⟩)
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover _ (fun i => (hU i).preimage hf) hcov
  refine ⟨s, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hs hx)
  obtain ⟨his, hxi⟩ := mem_iUnion.mp hi
  exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨his, hxi⟩⟩

/-- Supporting core result: compactness of a singleton is a one-set cover. -/
theorem singleton_compact {A : Type*} [MetricSpace A] (a : A) :
    IsCompact ({a} : Set A) := by
  apply isCompact_of_finite_subcover
  intro ι U _ hc
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hc (mem_singleton a))
  refine ⟨{i}, ?_⟩
  intro x hx
  rw [mem_singleton_iff] at hx
  subst x
  exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨Finset.mem_singleton_self _, hi⟩⟩

/-- Core result: the supremum of finitely covered initial intervals can be
extended inside an open cover member, and therefore reaches the right endpoint. -/
theorem interval_compact (a b : ℝ) (hab : a ≤ b) : IsCompact (Icc a b) := by
  classical
  apply isCompact_of_finite_subcover
  intro ι U hU hc
  let T : Set ℝ := {x | x ∈ Icc a b ∧ ∃ s : Finset ι, Icc a x ⊆ ⋃ i ∈ s, U i}
  obtain ⟨i₀, hi₀⟩ := mem_iUnion.mp (hc (show a ∈ Icc a b from ⟨le_rfl, hab⟩))
  have ha : a ∈ T := by
    refine ⟨⟨le_rfl, hab⟩, {i₀}, ?_⟩
    intro x hx
    have heq : x = a := le_antisymm hx.2 hx.1
    subst x
    exact mem_iUnion.mpr ⟨i₀, mem_iUnion.mpr ⟨Finset.mem_singleton_self _, hi₀⟩⟩
  have hne : T.Nonempty := ⟨a, ha⟩
  have hb : BddAbove T := ⟨b, fun x hx => hx.1.2⟩
  let c := sSup T
  have hac : a ≤ c := le_csSup hb ha
  have hcb : c ≤ b := csSup_le hne (fun x hx => hx.1.2)
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hc (show c ∈ Icc a b from ⟨hac, hcb⟩))
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hU i) c hi
  obtain ⟨t, ht, hct⟩ := exists_lt_of_lt_csSup hne (show c - r / 2 < sSup T by dsimp [c]; linarith)
  obtain ⟨s, hs⟩ := ht.2
  let d := min b (c + r / 2)
  have hcd : c ≤ d := le_min hcb (by linarith)
  have hd : d ∈ T := by
    refine ⟨⟨hac.trans hcd, min_le_left _ _⟩, insert i s, ?_⟩
    intro x hx
    by_cases hxt : x ≤ t
    · obtain ⟨j, hj⟩ := mem_iUnion.mp (hs ⟨hx.1, hxt⟩)
      obtain ⟨hjs, hxj⟩ := mem_iUnion.mp hj
      exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨Finset.mem_insert_of_mem hjs, hxj⟩⟩
    · have hxu : x ≤ c + r / 2 := hx.2.trans (min_le_right _ _)
      have hxball : x ∈ ball c r := by
        rw [mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith
      exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨Finset.mem_insert_self _ _, hball hxball⟩⟩
  have hdc : d ≤ c := le_csSup hb hd
  have hbc : b ≤ c := by
    by_contra h
    have hlt : c < d := lt_min (lt_of_not_ge h) (by linarith)
    exact (not_lt_of_ge hdc) hlt
  have hdb : d = b := le_antisymm (min_le_left _ _) (hbc.trans hcd)
  rw [hdb] at hd
  exact hd.2

/-- Supporting core result: finite subcovers in each factor give a finite
subcover of the product. The common radius is obtained before the second cover. -/
theorem compact_product {A B : Type*} [MetricSpace A] [MetricSpace B]
    (K : Set A) (L : Set B) (hK : IsCompact K) (hL : IsCompact L) :
    IsCompact (K ×ˢ L) := by
  classical
  apply isCompact_of_finite_subcover
  intro ι U hU hc
  have htube : ∀ x : K, ∃ δ > 0, ∃ s : Finset ι,
      ∀ x' ∈ ball x.val δ, ∀ y ∈ L, (x', y) ∈ ⋃ i ∈ s, U i := by
    intro x
    have hlocal : ∀ y : L, ∃ i : ι, ∃ r > 0, ball (x.val, y.val) r ⊆ U i := by
      intro y
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hc (show (x.val, y.val) ∈ K ×ˢ L from ⟨x.property, y.property⟩))
      obtain ⟨r, hr, hs⟩ := Metric.isOpen_iff.mp (hU i) (x.val, y.val) hi
      exact ⟨i, r, hr, hs⟩
    choose i r hr hs using hlocal
    have hcov : L ⊆ ⋃ y : L, ball y.val (r y) := by
      intro y hy
      exact mem_iUnion.mpr ⟨⟨y, hy⟩, by simpa only [mem_ball, dist_self] using hr ⟨y, hy⟩⟩
    obtain ⟨t, ht⟩ := hL.elim_finite_subcover _ (fun y => ball_open _ _) hcov
    obtain ⟨δ, hδ, hle⟩ := finite_positive_lower_bound t r (fun y _ => hr y)
    refine ⟨δ, hδ, t.image i, ?_⟩
    intro x' hx' y hy
    obtain ⟨z, hz⟩ := mem_iUnion.mp (ht hy)
    obtain ⟨hzt, hyz⟩ := mem_iUnion.mp hz
    have hpair : (x', y) ∈ ball (x.val, z.val) (r z) := by
      change max (dist x' x.val) (dist y z.val) < r z
      exact max_lt (hx'.trans_le (hle z hzt)) hyz
    exact mem_iUnion.mpr ⟨i z, mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨z, hzt, rfl⟩, hs z hpair⟩⟩
  choose δ hδ s hs using htube
  have hcov : K ⊆ ⋃ x : K, ball x.val (δ x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, by simpa only [mem_ball, dist_self] using hδ ⟨x, hx⟩⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover _ (fun x => ball_open _ _) hcov
  refine ⟨t.biUnion s, ?_⟩
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  obtain ⟨z, hz⟩ := mem_iUnion.mp (ht hx)
  obtain ⟨hzt, hxz⟩ := mem_iUnion.mp hz
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hs z x hxz y hy)
  obtain ⟨his, hxyi⟩ := mem_iUnion.mp hi
  exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨Finset.mem_biUnion.mpr ⟨z, hzt, his⟩, hxyi⟩⟩

/-- Core finite-coordinate induction; the zero-coordinate box is a singleton. -/
theorem pi_cell_compact (n : ℕ) (a b : Fin n → ℝ) (hab : ∀ j, a j ≤ b j) :
    IsCompact {x : Fin n → ℝ | ∀ j, a j ≤ x j ∧ x j ≤ b j} := by
  induction n with
  | zero =>
    have heq : {x : Fin 0 → ℝ | ∀ j, a j ≤ x j ∧ x j ≤ b j} = {fun j => Fin.elim0 j} := by
      ext x
      simp only [mem_ofPred_eq, mem_singleton_iff]
      constructor
      · intro _
        funext j
        exact Fin.elim0 j
      · intro _ j
        exact Fin.elim0 j
    rw [heq]
    exact singleton_compact _
  | succ n ih =>
    let K := {x : Fin n → ℝ | ∀ j, a j.succ ≤ x j ∧ x j ≤ b j.succ}
    let f : ℝ × (Fin n → ℝ) → (Fin (n + 1) → ℝ) := fun p => Fin.cons p.1 p.2
    have hf : Continuous f := by
      apply continuous_pi
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · exact continuous_fst
      · exact (continuous_apply k).comp continuous_snd
    have hk := compact_product (Icc (a 0) (b 0)) K (interval_compact _ _ (hab 0))
      (ih (fun j => a j.succ) (fun j => b j.succ) (fun j => hab j.succ))
    have heq : f '' (Icc (a 0) (b 0) ×ˢ K) =
        {x : Fin (n + 1) → ℝ | ∀ j, a j ≤ x j ∧ x j ≤ b j} := by
      ext x
      constructor
      · rintro ⟨⟨y, z⟩, ⟨hy, hz⟩, rfl⟩ j
        exact Fin.cases hy (fun k => hz k) j
      · intro hx
        refine ⟨(x 0, fun j => x j.succ), ⟨hx 0, fun j => hx j.succ⟩, ?_⟩
        funext j
        exact Fin.cases rfl (fun k => rfl) j
    rw [← heq]
    exact compact_image _ hk f hf

/-- Core result: the Euclidean topology is the finite-coordinate topology.
The change of norm is a representational map, not a compactness theorem. -/
theorem cell_compact (n : ℕ) (a b : Fin n → ℝ) (hab : ∀ j, a j ≤ b j) :
    IsCompact {x : EuclideanSpace ℝ (Fin n) | ∀ j, a j ≤ x j ∧ x j ≤ b j} := by
  have h := compact_image _ (pi_cell_compact n a b hab)
    (fun x : Fin n → ℝ => (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)))
    (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ))
  convert h using 1
  ext x
  constructor
  · intro hx
    exact ⟨WithLp.ofLp x, hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

/-- The one-dimensional interval statement, after the cell theorem. -/
theorem closed_interval_compact (a b : ℝ) (hab : a ≤ b) : IsCompact (Icc a b) := by
  exact interval_compact a b hab

/-- Core result: enclose a bounded set in a compact coordinate box. -/
theorem heine_borel (n : ℕ) (E : Set (EuclideanSpace ℝ (Fin n))) :
    IsCompact E ↔ IsClosed E ∧ bounded E := by
  constructor
  · intro h
    exact ⟨compact_closed E h, compact_bounded E h⟩
  · rintro ⟨hc, hb⟩
    obtain ⟨p, r, hr, hs⟩ := hb ⟨0⟩
    let K : Set (EuclideanSpace ℝ (Fin n)) := {x | ∀ j, p j - r ≤ x j ∧ x j ≤ p j + r}
    have hk : IsCompact K := cell_compact n _ _ (fun j => by linarith)
    apply closed_subset_compact K E hk hc
    intro x hx j
    have hd : ‖x - p‖ < r := by simpa only [mem_ball, dist_eq_norm] using hs hx
    have hj : ‖(x - p) j‖ ≤ ‖x - p‖ := PiLp.norm_apply_le _ _
    change ‖x j - p j‖ ≤ ‖x - p‖ at hj
    rw [Real.norm_eq_abs] at hj
    have hcoord := abs_le.mp (hj.trans (le_of_lt hd))
    constructor <;> linarith

end MathematicalAnalysis1.Chapter01
