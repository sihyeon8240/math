import Textbooks.MathematicalAnalysis.Chapter03.ContinuousFunctions
import Textbooks.MathematicalAnalysis.Chapter01.ConnectedSets
import Mathlib.Logic.Equiv.Set

namespace MathematicalAnalysis.Chapter03

open Set Metric
open MathematicalAnalysis.Chapter01

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- Lemma: continuity on a subset is continuity of the corresponding subtype map. -/
theorem continuousOn_iff_restrict (f : X → Y) (K : Set X) :
    ContinuousOn f K ↔ Continuous (fun x : K => f x) := by
  constructor
  · intro h
    apply Metric.continuous_iff.mpr
    intro a ε hε
    obtain ⟨δ, hδ, hd⟩ := Metric.continuousWithinAt_iff.mp (h a a.property) ε hε
    exact ⟨δ, hδ, fun x hx => hd x.property hx⟩

  · intro h a ha
    apply Metric.continuousWithinAt_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp
      (h.continuousAt (x := ⟨a, ha⟩)) ε hε
    exact ⟨δ, hδ, fun x hx hdxa => hd (x := ⟨x, hx⟩) hdxa⟩

/-- Theorem: a continuous image of a compact subset is compact. -/
theorem compact_image_on (K : Set X) (hK : IsCompact K) (f : X → Y)
    (hf : ContinuousOn f K) : IsCompact (f '' K) := by
  have hsub := (compact_subspace K K Subset.rfl).mpr hK
  have him := compact_image ((Subtype.val : K → X) ⁻¹' K) hsub
    (fun x : K => f x) ((continuousOn_iff_restrict f K).mp hf)
  convert him using 1
  ext y

  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, hx, rfl⟩
  · rintro ⟨x, _, rfl⟩
    exact ⟨x, x.property, rfl⟩

/-- Theorem: a continuous real function on a nonempty compact set attains its
supremum and infimum. -/
theorem extreme_value (K : Set X) (hK : IsCompact K) (hne : K.Nonempty)
    (f : X → ℝ) (hf : ContinuousOn f K) :
    (∃ a ∈ K, f a = sSup (f '' K)) ∧ (∃ b ∈ K, f b = sInf (f '' K)) := by
  let S := f '' K
  have hc : IsCompact S := compact_image_on K hK f hf
  have hs : S.Nonempty := hne.image f

  obtain ⟨p, r, hr, hball⟩ := (isBounded_iff S).mp (compact_bounded S hc)
    (show Nonempty ℝ from ⟨0⟩)
  have hupper : BddAbove S := by
    refine ⟨p + r, ?_⟩
    intro x hx
    have hd := hball hx
    rw [mem_ball, Real.dist_eq, abs_lt] at hd
    linarith

  have hlower : BddBelow S := by
    refine ⟨p - r, ?_⟩
    intro x hx
    have hd := hball hx
    rw [mem_ball, Real.dist_eq, abs_lt] at hd
    linarith

  have hsup : sSup S ∈ S := (supremum_in_closure S hs hupper).2 (compact_closed S hc)
  have hinfcl : sInf S ∈ closure S := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨x, hx, hlt⟩ := exists_lt_of_csInf_lt hs (lt_add_of_pos_right (sInf S) hε)
    refine ⟨x, hx, ?_⟩
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (csInf_le hlower hx))]
    linarith

  have hinf : sInf S ∈ S := by
    have heq := (closure_properties S).2.1.mpr (compact_closed S hc)
    have hsub : closure S ⊆ S := by rw [← heq]
    exact hsub hinfcl

  exact ⟨hsup, hinf⟩

/-- Corollary: a continuous function on a nonempty compact metric space attains
both extrema. -/
theorem extreme_value_compact [Nonempty X] (hX : IsCompact (univ : Set X))
    (f : X → ℝ) (hf : Continuous f) :
    (∃ a, f a = sSup (range f)) ∧ (∃ b, f b = sInf (range f)) := by
  simpa only [image_univ, mem_univ, true_and] using
    extreme_value univ hX ⟨Classical.choice inferInstance, mem_univ _⟩ f hf.continuousOn

/-- Corollary: a continuous function on a closed real interval attains both extrema. -/
theorem extreme_value_interval (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc a b)) :
    (∃ x ∈ Icc a b, f x = sSup (f '' Icc a b)) ∧
      (∃ y ∈ Icc a b, f y = sInf (f '' Icc a b)) :=
  extreme_value _ (interval_compact a b hab) ⟨a, le_rfl, hab⟩ f hf

/-- Theorem: the inverse on the range of a continuous injection from a compact
metric space is continuous. -/
theorem continuous_inverse_of_compact (hX : IsCompact (univ : Set X))
    (f : X → Y) (hf : Continuous f) (hinj : Function.Injective f) :
    Continuous (Equiv.ofInjective f hinj).symm := by
  classical

  let e := Equiv.ofInjective f hinj
  apply (continuous_iff_open_preimage e.symm).mpr
  intro U hU
  have hcomp : IsCompact (f '' Uᶜ) := compact_image Uᶜ
    (closed_subset_compact univ Uᶜ hX hU.isClosed_compl (subset_univ _)) f hf
  have hopen := (compact_closed _ hcomp).isOpen_compl
  have hval : Continuous (Subtype.val : range f → Y) := by
    apply Metric.continuous_iff.mpr
    intro _ ε hε
    exact ⟨ε, hε, fun _ hx => hx⟩

  have hpre := (continuous_iff_open_preimage (Subtype.val : range f → Y)).mp hval _ hopen
  convert hpre using 1
  ext y
  have hfy : f (e.symm y) = y := Equiv.apply_ofInjective_symm hinj y

  constructor
  · intro hy ⟨x, hx, hxy⟩
    have heq : x = e.symm y := hinj (hxy.trans hfy.symm)
    exact hx (heq.symm ▸ hy)
  · intro hy
    by_contra hn
    exact hy ⟨e.symm y, hn, hfy⟩

/-- Corollary: a continuous injection on a closed interval has a continuous inverse. -/
theorem continuous_inverse_interval (a b : ℝ) (hab : a ≤ b)
    (f : Icc a b → ℝ) (hf : Continuous f) (hinj : Function.Injective f) :
    Continuous (Equiv.ofInjective f hinj).symm := by
  have hsub := (compact_subspace (Icc a b) (Icc a b) Subset.rfl).mpr
    (interval_compact a b hab)
  have huniv : IsCompact (univ : Set (Icc a b)) := by
    have heq : (Subtype.val : Icc a b → ℝ) ⁻¹' Icc a b = univ := by
      ext x
      simp only [mem_preimage, x.property, mem_univ]
    rwa [heq] at hsub

  exact continuous_inverse_of_compact huniv f hf hinj

/-- Definition: uniform continuity uses a single positive radius for every pair
of points in the domain. -/
theorem uniformContinuous_iff (f : X → Y) :
    UniformContinuous f ↔ ∀ ε > 0, ∃ δ > 0,
      ∀ x y, dist x y < δ → dist (f x) (f y) < ε :=
  Metric.uniformContinuous_iff

/-- Theorem: a continuous map from a compact metric space is uniformly continuous. -/
theorem uniformContinuous_of_compact (hX : IsCompact (univ : Set X))
    (f : X → Y) (hf : Continuous f) : UniformContinuous f := by
  classical
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  have hex : ∀ a, ∃ r > 0, ∀ ⦃x⦄,
      dist x a < r → dist (f x) (f a) < ε / 2 := by
    intro a
    exact Metric.continuousAt_iff.mp hf.continuousAt (ε / 2) (half_pos hε)

  choose r hr hd using hex
  have hcover : (univ : Set X) ⊆ ⋃ a, ball a (r a / 2) := by
    intro a _
    exact mem_iUnion.mpr ⟨a, mem_ball_self (half_pos (hr a))⟩

  obtain ⟨s, hs⟩ := hX.elim_finite_subcover _ (fun a => ball_open _ _) hcover
  obtain ⟨δ, hδ, hle⟩ := finite_positive_lower_bound s (fun a => r a / 2)
    (fun a _ => half_pos (hr a))

  refine ⟨δ, hδ, ?_⟩
  intro x y hxy
  obtain ⟨a, ha⟩ := mem_iUnion.mp (hs (mem_univ x))
  obtain ⟨has, hxa⟩ := mem_iUnion.mp ha
  have hyx : dist y x < r a / 2 := by
    rw [dist_comm]
    exact hxy.trans_le (hle a has)

  have hya : dist y a < r a := by
    have ht := dist_triangle y x a
    change dist x a < r a / 2 at hxa
    linarith

  have hx := hd a (x := x) (hxa.trans (half_lt_self (hr a)))
  have hy := hd a (x := y) hya
  have ht := dist_triangle (f x) (f a) (f y)
  rw [dist_comm (f a) (f y)] at ht
  linarith

/-- Theorem: continuity on a compact subset implies uniform continuity on it. -/
theorem uniformContinuousOn_of_compact (K : Set X) (hK : IsCompact K)
    (f : X → Y) (hf : ContinuousOn f K) : UniformContinuousOn f K := by
  have hsub := (compact_subspace K K Subset.rfl).mpr hK
  have huniv : IsCompact (univ : Set K) := by
    have heq : (Subtype.val : K → X) ⁻¹' K = univ := by
      ext x
      simp only [mem_preimage, x.property, mem_univ]
    rwa [heq] at hsub

  have hu := uniformContinuous_of_compact huniv (fun x : K => f x)
    ((continuousOn_iff_restrict f K).mp hf)

  apply Metric.uniformContinuousOn_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  exact ⟨δ, hδ, fun x hx y hy hxy => hd (a := ⟨x, hx⟩) (b := ⟨y, hy⟩) hxy⟩

end MathematicalAnalysis.Chapter03
