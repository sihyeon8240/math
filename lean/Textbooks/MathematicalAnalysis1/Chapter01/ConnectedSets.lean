import Textbooks.MathematicalAnalysis1.Chapter01.MetricSpaces

/-! Core connectedness on the real line from the least-upper-bound property.
The book permits the empty set to be connected. Its separated-set definition
is recorded explicitly below, avoiding a nonemptiness assumption. -/

set_option autoImplicit false

namespace MathematicalAnalysis1.Chapter01

open Set Metric

/-- The separated-set formulation used in the textbook. -/
def separated {X : Type*} [MetricSpace X] (A B : Set X) : Prop :=
  Disjoint (closure A) B ∧ Disjoint A (closure B)

/-- The textbook convention includes the empty set. -/
def connected {X : Type*} [MetricSpace X] (E : Set X) : Prop :=
  ∀ A B : Set X, A.Nonempty → B.Nonempty → E = A ∪ B → ¬ separated A B

/-- Supporting core result: closure preserves a real upper bound. -/
theorem closure_upper_bound (A : Set ℝ) (c : ℝ) (h : ∀ x ∈ A, x ≤ c) :
    ∀ x ∈ closure A, x ≤ c := by
  intro x hx
  by_contra hn
  have hc : c < x := lt_of_not_ge hn
  obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.mp hx (x - c) (sub_pos.mpr hc)
  rw [Real.dist_eq, abs_lt] at hd
  have hyc := h y hy
  linarith

/-- Supporting core result: closure preserves a real lower bound. -/
theorem closure_lower_bound (A : Set ℝ) (c : ℝ) (h : ∀ x ∈ A, c ≤ x) :
    ∀ x ∈ closure A, c ≤ x := by
  intro x hx
  by_contra hn
  have hc : x < c := lt_of_not_ge hn
  obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.mp hx (c - x) (sub_pos.mpr hc)
  rw [Real.dist_eq, abs_lt] at hd
  have hcy := h y hy
  linarith

/-- Supporting core argument: the supremum between points in opposite
separated sets cannot belong to either side of an interval. -/
theorem no_separation_of_between (E A B : Set ℝ)
    (hbetween : ∀ a ∈ E, ∀ b ∈ E, ∀ x : ℝ, a < x → x < b → x ∈ E)
    (heq : E = A ∪ B) (hsep : separated A B)
    (a b : ℝ) (ha : a ∈ A) (hb : b ∈ B) (hab : a < b) : False := by
  let S := A ∩ Icc a b
  have hane : a ∈ S := ⟨ha, le_rfl, hab.le⟩
  have hne : S.Nonempty := ⟨a, hane⟩
  have hbd : BddAbove S := ⟨b, fun x hx => hx.2.2⟩
  let c := sSup S
  have hac : a ≤ c := le_csSup hbd hane
  have hcb : c ≤ b := csSup_le hne (fun x hx => hx.2.2)
  have hcS : c ∈ closure S := (supremum_in_closure S hne hbd).1
  have hcA : c ∈ closure A := (closure_properties S).2.2 (closure A)
    (closure_closed A) (fun x hx => subset_closure hx.1) hcS
  have hcnotB : c ∉ B := fun h => Set.disjoint_left.mp hsep.1 hcA h
  have hcltb : c < b := lt_of_le_of_ne hcb (fun h => hcnotB (h.symm ▸ hb))
  have hcE : c ∈ E := by
    by_cases he : a = c
    · rw [← he, heq]
      exact Or.inl ha
    · exact hbetween a (heq.symm ▸ Or.inl ha) b (heq.symm ▸ Or.inr hb) c
        (lt_of_le_of_ne hac he) hcltb
  have hcain : c ∈ A := (show c ∈ A ∪ B from heq ▸ hcE).resolve_right hcnotB
  have hcnotclB : c ∉ closure B := fun h => Set.disjoint_left.mp hsep.2 hcain h
  have hex : ∃ r > 0, ∀ y ∈ B, r ≤ dist c y := by
    by_contra h
    push Not at h
    exact hcnotclB (Metric.mem_closure_iff.mpr h)
  obtain ⟨r, hr, hfar⟩ := hex
  let δ := min r (b - c) / 2
  have hδ : 0 < δ := half_pos (lt_min hr (sub_pos.mpr hcltb))
  have hδr : δ < r := (half_lt_self (lt_min hr (sub_pos.mpr hcltb))).trans_le (min_le_left _ _)
  have hδb : δ < b - c := (half_lt_self (lt_min hr (sub_pos.mpr hcltb))).trans_le (min_le_right _ _)
  let x := c + δ
  have hax : a < x := by dsimp [x]; linarith
  have hxb : x < b := by dsimp [x]; linarith
  have hxE := hbetween a (heq.symm ▸ Or.inl ha) b (heq.symm ▸ Or.inr hb) x hax hxb
  have hxnotB : x ∉ B := by
    intro hx
    have hdist := hfar x hx
    have hd : dist c x = δ := by
      rw [Real.dist_eq, show c - x = -δ by dsimp [x]; ring, abs_neg, abs_of_pos hδ]
    rw [hd] at hdist
    linarith
  have hxA := (show x ∈ A ∪ B from heq ▸ hxE).resolve_right hxnotB
  have hxc : x ≤ c := le_csSup hbd (show x ∈ S from ⟨hxA, hax.le, hxb.le⟩)
  dsimp [x] at hxc
  linarith

/-- Core result: real connected sets are exactly the sets containing all
points between any two of their elements. -/
theorem connected_iff_between (E : Set ℝ) :
    connected E ↔ ∀ a ∈ E, ∀ b ∈ E, ∀ x : ℝ, a < x → x < b → x ∈ E := by
  classical
  constructor
  · intro hc a ha b hb x hax hxb
    by_contra hx
    let A := E ∩ Iio x
    let B := E ∩ Ioi x
    have heq : E = A ∪ B := by
      ext y
      constructor
      · intro hy
        rcases lt_trichotomy y x with h | h | h
        · exact Or.inl ⟨hy, h⟩
        · exact False.elim (hx (h ▸ hy))
        · exact Or.inr ⟨hy, h⟩
      · rintro (h | h) <;> exact h.1
    apply hc A B ⟨a, ha, hax⟩ ⟨b, hb, hxb⟩ heq
    constructor
    · apply Set.disjoint_left.mpr
      intro y hy hB
      have hle := closure_upper_bound A x (fun z hz => hz.2.le) y hy
      exact (not_lt_of_ge hle) hB.2
    · apply Set.disjoint_left.mpr
      intro y hA hy
      have hle := closure_lower_bound B x (fun z hz => hz.2.le) y hy
      exact (not_lt_of_ge hle) hA.2
  · intro h A B hA hB heq hsep
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    have hne : a ≠ b := by
      intro he
      exact Set.disjoint_left.mp hsep.1 (subset_closure ha) (he.symm ▸ hb)
    rcases lt_or_gt_of_ne hne with hab | hba
    · exact no_separation_of_between E A B h heq hsep a b ha hb hab
    · have hsep' : separated B A := ⟨hsep.2.symm, hsep.1.symm⟩
      exact no_separation_of_between E B A h (heq.trans (union_comm _ _)) hsep' b a hb ha hba

end MathematicalAnalysis1.Chapter01
