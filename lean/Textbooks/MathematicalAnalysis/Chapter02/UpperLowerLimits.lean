import Textbooks.MathematicalAnalysis.Chapter02.MonotoneSequences
import Textbooks.MathematicalAnalysis.Chapter02.Subsequences
import Mathlib.Topology.Instances.EReal.Lemmas

namespace MathematicalAnalysis.Chapter02

open Set Filter
open scoped Topology

/-- Definition: extended subsequential limits include both infinite limits. -/
def extendedSubsequentialLimits (u : ℕ → ℝ) : Set EReal :=
  {a | ∃ φ : ℕ → ℕ, StrictMono φ ∧
    Tendsto (fun n => (u (φ n) : EReal)) atTop (𝓝 a)}

/-- Proposition: the positive and negative infinite values bound every real value strictly. -/
theorem real_between_infinities (a : ℝ) : (⊥ : EReal) < a ∧ (a : EReal) < ⊤ :=
  ⟨EReal.bot_lt_coe a, EReal.coe_lt_top a⟩

/-- Lemma: divergence to positive infinity is eventual exceedance of every positive bound. -/
theorem tendsto_atTop_iff_pos (u : ℕ → ℝ) :
    Tendsto u atTop atTop ↔ ∀ C > 0, ∃ N : ℕ, ∀ n > N, C < u n := by
  constructor

  · intro h C _
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_atTop.1 h) (C + 1))
    exact ⟨N, fun n hn => lt_of_lt_of_le (by linarith) (hN n hn.le)⟩

  · intro h
    apply tendsto_atTop.2
    intro C
    obtain ⟨N, hN⟩ := h (max C 0 + 1) (by linarith [le_max_right C 0])
    apply eventually_atTop.mpr
    refine ⟨N + 1, ?_⟩
    intro n hn
    have hn' : N < n := by omega
    exact (le_max_left C 0).trans (by linarith [hN n hn'])

/-- Lemma: divergence to negative infinity is eventual descent below every negative bound. -/
theorem tendsto_atBot_iff_neg (u : ℕ → ℝ) :
    Tendsto u atTop atBot ↔ ∀ C < 0, ∃ N : ℕ, ∀ n > N, u n < C := by
  constructor

  · intro h C _
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_atBot.1 h) (C - 1))
    exact ⟨N, fun n hn => lt_of_le_of_lt (hN n hn.le) (by linarith)⟩

  · intro h
    apply tendsto_atBot.2
    intro C
    obtain ⟨N, hN⟩ := h (min C 0 - 1) (by linarith [min_le_right C 0])
    apply eventually_atTop.mpr
    refine ⟨N + 1, ?_⟩
    intro n hn
    have hn' : N < n := by omega
    have hbound : u n ≤ min C 0 := by linarith [hN n hn']
    exact hbound.trans (min_le_left C 0)

private theorem limsup_tail_formula {Y : Type*} [CompleteLinearOrder Y] (u : ℕ → Y) :
    limsup u atTop = ⨅ n : ℕ, ⨆ k ≥ n, u k := by
  rw [limsup_eq]
  apply le_antisymm

  · apply le_iInf
    intro n
    apply sInf_le
    apply eventually_atTop.mpr
    exact ⟨n, fun k hk => le_iSup_of_le k (le_iSup_of_le hk le_rfl)⟩

  · apply le_sInf
    intro a ha
    obtain ⟨n, hn⟩ := eventually_atTop.mp ha
    exact (iInf_le _ n).trans (iSup_le fun k => iSup_le fun hk => hn k hk)

private theorem limsup_thresholds {Y : Type*} [CompleteLinearOrder Y] [DenselyOrdered Y]
    (u : ℕ → Y) (a : Y) :
    limsup u atTop = a ↔
      (∀ b > a, ∃ N : ℕ, ∀ n ≥ N, u n < b) ∧
      (∀ b < a, ∀ N : ℕ, ∃ n ≥ N, b < u n) := by
  rw [limsup_tail_formula]
  constructor

  · intro h
    constructor

    · intro b hb
      obtain ⟨N, hN⟩ := iInf_lt_iff.mp (h ▸ hb)
      refine ⟨N, ?_⟩
      intro n hn
      have hle : u n ≤ ⨆ k ≥ N, u k := le_iSup_of_le n (le_iSup_of_le hn le_rfl)
      exact hle.trans_lt hN

    · intro b hb N
      have hN : b < ⨆ k ≥ N, u k := hb.trans_le (h ▸ iInf_le _ N)
      obtain ⟨n, hn⟩ := lt_iSup_iff.mp hN
      obtain ⟨hnN, hbn⟩ := lt_iSup_iff.mp hn
      exact ⟨n, hnN, hbn⟩

  · rintro ⟨hupper, hlower⟩
    apply le_antisymm

    · apply le_of_forall_gt
      intro b hb
      obtain ⟨c, hc, hcb⟩ := exists_between hb
      obtain ⟨N, hN⟩ := hupper c hc
      have hbound : (⨆ n ≥ N, u n) ≤ c :=
        iSup_le fun n => iSup_le fun hn => (hN n hn).le
      exact ((iInf_le (fun N : ℕ => ⨆ n ≥ N, u n) N).trans hbound).trans_lt hcb

    · by_contra hn
      obtain ⟨b, hb, hba⟩ := exists_between (lt_of_not_ge hn)
      obtain ⟨N, hN⟩ := iInf_lt_iff.mp hb
      obtain ⟨n, hnN, hbn⟩ := hlower b hba N
      have hle : u n ≤ ⨆ k ≥ N, u k := le_iSup_of_le n (le_iSup_of_le hnN le_rfl)
      exact (not_lt_of_ge (hbn.le.trans hle)) hN

private theorem antitone_tendsto_iInf {Y : Type*} [CompleteLinearOrder Y]
    [TopologicalSpace Y] [OrderTopology Y] (u : ℕ → Y) (hu : Antitone u) :
    Tendsto u atTop (𝓝 (⨅ n, u n)) := by
  apply tendsto_order.2
  constructor

  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (iInf_le u n))

  · intro b hb
    obtain ⟨N, hN⟩ := iInf_lt_iff.mp hb
    exact eventually_atTop.mpr ⟨N, fun n hn => (hu hn).trans_lt hN⟩

/-- Theorem: the upper limit is the limit of the suprema of the tails, including infinite values. -/
theorem limsup_eq_and_tendsto_tail_sup (u : ℕ → ℝ) :
    limsup (fun n => (u n : EReal)) atTop = ⨅ n : ℕ, ⨆ k ≥ n, (u k : EReal) ∧
    Tendsto (fun n : ℕ => ⨆ k ≥ n, (u k : EReal)) atTop
      (𝓝 (limsup (fun n => (u n : EReal)) atTop)) := by
  refine ⟨limsup_tail_formula _, ?_⟩
  rw [limsup_tail_formula]
  apply antitone_tendsto_iInf
  intro m n hmn
  apply iSup_le
  intro k
  apply iSup_le
  intro hnk
  exact le_iSup_of_le k (le_iSup_of_le (hmn.trans hnk) le_rfl)

/-- Theorem: the lower limit is the limit of the infima of the tails, including infinite values. -/
theorem liminf_eq_and_tendsto_tail_inf (u : ℕ → ℝ) :
    liminf (fun n => (u n : EReal)) atTop = ⨆ n : ℕ, ⨅ k ≥ n, (u k : EReal) ∧
    Tendsto (fun n : ℕ => ⨅ k ≥ n, (u k : EReal)) atTop
      (𝓝 (liminf (fun n => (u n : EReal)) atTop)) := by
  have hformula := limsup_tail_formula (Y := ERealᵒᵈ) (fun n => (u n : EReal))
  change liminf (fun n => (u n : EReal)) atTop = ⨆ n : ℕ, ⨅ k ≥ n, (u k : EReal)
    at hformula
  refine ⟨hformula, ?_⟩
  rw [hformula]
  apply antitone_tendsto_iInf (Y := ERealᵒᵈ)
  intro m n hmn
  apply iSup_le
  intro k
  apply iSup_le
  intro hnk
  exact le_iSup_of_le k (le_iSup_of_le (hmn.trans hnk) le_rfl)

private theorem limsup_mono_eventually {Y : Type*} [CompleteLinearOrder Y] (f g : ℕ → Y)
    (hfg : ∀ᶠ n in atTop, f n ≤ g n) : limsup f atTop ≤ limsup g atTop := by
  rw [limsup_eq, limsup_eq]
  apply le_sInf
  intro a ha
  exact sInf_le (hfg.and ha |>.mono fun _ h => h.1.trans h.2)

/-- Theorem: eventual comparison orders both upper and lower limits. -/
theorem liminf_limsup_mono (u v : ℕ → ℝ) (huv : ∀ᶠ n in atTop, u n ≤ v n) :
    liminf (fun n => (u n : EReal)) atTop ≤ liminf (fun n => (v n : EReal)) atTop ∧
    limsup (fun n => (u n : EReal)) atTop ≤ limsup (fun n => (v n : EReal)) atTop := by
  have hE := huv.mono (fun _ h => EReal.coe_le_coe h)
  exact ⟨limsup_mono_eventually (Y := ERealᵒᵈ) _ _ hE, limsup_mono_eventually _ _ hE⟩

/-- Lemma: the upper limit is characterized by eventual upper bounds and recurrent lower bounds. -/
theorem limsup_eq_iff_thresholds (u : ℕ → EReal) (a : EReal) :
    limsup u atTop = a ↔
      (∀ b > a, ∃ N : ℕ, ∀ n ≥ N, u n < b) ∧
      (∀ b < a, ∀ N : ℕ, ∃ n ≥ N, b < u n) :=
  limsup_thresholds u a

/-- Theorem: a finite upper limit has eventual epsilon upper bounds and
infinitely many indices above each epsilon lower bound. -/
theorem limsup_eq_real_iff (u : ℕ → ℝ) (a : ℝ) :
    limsup (fun n => (u n : EReal)) atTop = (a : EReal) ↔
      (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, u n < a + ε) ∧
      (∀ ε > 0, {n : ℕ | a - ε < u n}.Infinite) := by
  rw [limsup_eq_iff_thresholds]
  constructor

  · rintro ⟨hupper, hlower⟩
    constructor

    · intro ε hε
      obtain ⟨N, hN⟩ := hupper (a + ε) (EReal.coe_lt_coe_iff.mpr (by linarith))
      exact ⟨N, fun n hn => EReal.coe_lt_coe_iff.mp (hN n hn)⟩

    · intro ε hε hf
      obtain ⟨M, hM⟩ := hf.bddAbove
      obtain ⟨n, hn, hlow⟩ := hlower (a - ε)
        (EReal.coe_lt_coe_iff.mpr (by linarith)) (M + 1)
      have hmem : n ∈ {n : ℕ | a - ε < u n} := EReal.coe_lt_coe_iff.mp hlow
      exact (Nat.not_succ_le_self M) (hn.trans (hM hmem))

  · rintro ⟨hupper, hlower⟩
    constructor

    · intro b hb
      induction b using EReal.rec with
      | bot => exact (not_lt_of_ge bot_le hb).elim
      | top => exact ⟨0, fun n _ => EReal.coe_lt_top (u n)⟩
      | coe b =>
        have hab : a < b := EReal.coe_lt_coe_iff.mp hb
        obtain ⟨N, hN⟩ := hupper (b - a) (sub_pos.mpr hab)
        refine ⟨N, fun n hn => EReal.coe_lt_coe_iff.mpr ?_⟩
        simpa only [add_sub_cancel] using hN n hn

    · intro b hb N
      induction b using EReal.rec with
      | bot => exact ⟨N, le_rfl, EReal.bot_lt_coe (u N)⟩
      | top => exact (not_lt_of_ge le_top hb).elim
      | coe b =>
        have hba : b < a := EReal.coe_lt_coe_iff.mp hb
        obtain ⟨n, hn, hnN⟩ := (hlower (a - b) (sub_pos.mpr hba)).exists_gt N
        change a - (a - b) < u n at hn
        refine ⟨n, hnN.le, EReal.coe_lt_coe_iff.mpr ?_⟩
        simpa only [sub_sub_cancel] using hn

private theorem limsup_mem_extended (u : ℕ → ℝ) :
    limsup (fun n => (u n : EReal)) atTop ∈ extendedSubsequentialLimits u := by
  classical
  generalize hL : limsup (fun n => (u n : EReal)) atTop = L
  have hthreshold := (limsup_eq_iff_thresholds _ L).mp hL
  induction L using EReal.rec with
  | bot =>
    refine ⟨id, strictMono_id, EReal.tendsto_nhds_bot_iff_real.mpr ?_⟩
    intro b
    obtain ⟨N, hN⟩ := hthreshold.1 b (EReal.bot_lt_coe b)
    exact eventually_atTop.mpr ⟨N, hN⟩

  | top =>
    have hex : ∀ n m : ℕ, ∃ k ≥ m, (n : ℝ) < u k := by
      intro n m
      obtain ⟨k, hkm, hk⟩ := hthreshold.2 (n : ℝ) (EReal.coe_lt_top _) m
      exact ⟨k, hkm, EReal.coe_lt_coe_iff.mp hk⟩
    choose k hk hd using hex
    let φ : ℕ → ℕ := fun n => Nat.rec (k 0 0) (fun n prev => k (n + 1) (prev + 1)) n
    have hmono : StrictMono φ := by
      apply strictMono_nat_of_lt_succ
      intro n
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (φ n)) (hk (n + 1) (φ n + 1))
    have hvalue : ∀ n : ℕ, (n : ℝ) < u (φ n) := by
      intro n
      cases n with
      | zero => exact hd 0 0
      | succ n => exact hd (n + 1) (φ n + 1)

    refine ⟨φ, hmono, EReal.tendsto_nhds_top_iff_real.mpr ?_⟩
    intro b
    obtain ⟨N, hN⟩ := exists_nat_gt b
    exact eventually_atTop.mpr ⟨N, fun n hn => EReal.coe_lt_coe_iff.mpr
      (hN.trans_le (Nat.cast_le.mpr hn) |>.trans (hvalue n))⟩

  | coe a =>
    have happrox : ∀ n m : ℕ, ∃ k ≥ m, dist (u k) a < 1 / (n + 1 : ℝ) := by
      intro n m
      let δ := 1 / (n + 1 : ℝ)
      have hδ : 0 < δ := by
        dsimp [δ]
        positivity
      obtain ⟨N, hN⟩ := hthreshold.1 (a + δ) (EReal.coe_lt_coe_iff.mpr (by linarith))
      obtain ⟨k, hk, hlow⟩ := hthreshold.2 (a - δ)
        (EReal.coe_lt_coe_iff.mpr (by linarith)) (max m N)
      have hupper := EReal.coe_lt_coe_iff.mp (hN k ((le_max_right _ _).trans hk))
      have hlower := EReal.coe_lt_coe_iff.mp hlow
      refine ⟨k, (le_max_left _ _).trans hk, ?_⟩
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith

    obtain ⟨φ, hφ, hlim⟩ :=
      MathematicalAnalysis.Chapter01.subsequence_of_frequent_approximation u a happrox
    exact ⟨φ, hφ, EReal.tendsto_coe.mpr hlim⟩

private theorem extended_limit_le_limsup (u : ℕ → ℝ) (a : EReal)
    (ha : a ∈ extendedSubsequentialLimits u) :
    a ≤ limsup (fun n => (u n : EReal)) atTop := by
  obtain ⟨φ, hφ, hlim⟩ := ha
  by_contra hn
  obtain ⟨b, hbL, hba⟩ := exists_between (lt_of_not_ge hn)
  obtain ⟨N, hN⟩ := ((limsup_eq_iff_thresholds _ _).mp rfl).1 b hbL
  obtain ⟨M, hM⟩ := eventually_atTop.mp ((tendsto_order.mp hlim).1 b hba)
  let k := max N M
  have hupper := hN (φ k) ((le_max_left N M).trans (hφ.id_le k))
  have hlower := hM k (le_max_right _ _)
  exact (not_lt_of_ge hlower.le) hupper

/-- Theorem: the upper limit is the supremum of the extended subsequential limits. -/
theorem limsup_eq_sSup_subsequentialLimits (u : ℕ → ℝ) :
    limsup (fun n => (u n : EReal)) atTop = sSup (extendedSubsequentialLimits u) := by
  apply le_antisymm
  · exact le_sSup (limsup_mem_extended u)
  · exact sSup_le (fun a ha => extended_limit_le_limsup u a ha)

private theorem extended_tendsto_neg (u : ℕ → EReal) (a : EReal)
    (hu : Tendsto u atTop (𝓝 a)) : Tendsto (fun n => -u n) atTop (𝓝 (-a)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    have hb' : a < -b := EReal.lt_neg_comm.mp hb
    exact ((tendsto_order.mp hu).2 (-b) hb').mono
      (fun n hn => EReal.lt_neg_comm.mpr hn)
  · intro b hb
    have hb' : -b < a := EReal.neg_lt_comm.mp hb
    exact ((tendsto_order.mp hu).1 (-b) hb').mono
      (fun n hn => EReal.neg_lt_comm.mpr hn)

private theorem limsup_neg_eq_neg_liminf (u : ℕ → ℝ) :
    limsup (fun n => (-u n : EReal)) atTop = -liminf (fun n => (u n : EReal)) atTop := by
  rw [limsup_tail_formula, (liminf_eq_and_tendsto_tail_inf u).1]
  have h := EReal.negOrderIso.map_iSup (fun n : ℕ => ⨅ k ≥ n, (u k : EReal))
  change -(⨆ n : ℕ, ⨅ k ≥ n, (u k : EReal)) = ⨅ n : ℕ, -(⨅ k ≥ n, (u k : EReal)) at h
  rw [h]
  congr 1
  funext n
  have hn := EReal.negOrderIso.map_iInf (fun k : ℕ => ⨅ (_ : k ≥ n), (u k : EReal))
  change -(⨅ k ≥ n, (u k : EReal)) = ⨆ k : ℕ, -(⨅ (_ : k ≥ n), (u k : EReal)) at hn
  rw [hn]
  congr 1
  funext k
  have hk := EReal.negOrderIso.map_iInf (fun _ : k ≥ n => (u k : EReal))
  exact hk.symm

/-- Theorem: the lower limit is the infimum of the extended subsequential limits. -/
theorem liminf_eq_sInf_subsequentialLimits (u : ℕ → ℝ) :
    liminf (fun n => (u n : EReal)) atTop = sInf (extendedSubsequentialLimits u) := by
  have hneg := limsup_neg_eq_neg_liminf u
  have hmem := limsup_mem_extended (fun n => -u n)
  simp only [EReal.coe_neg] at hmem
  rw [hneg] at hmem
  obtain ⟨φ, hφ, hlim⟩ := hmem
  have hlim' := extended_tendsto_neg _ _ hlim
  simp only [EReal.coe_neg, neg_neg] at hlim'
  have hmin : liminf (fun n => (u n : EReal)) atTop ∈ extendedSubsequentialLimits u :=
    ⟨φ, hφ, hlim'⟩
  apply le_antisymm

  · apply le_sInf
    intro a ha
    obtain ⟨ψ, hψ, hψlim⟩ := ha
    have hnlim := extended_tendsto_neg _ _ hψlim
    have hnmem : -a ∈ extendedSubsequentialLimits (fun n => -u n) := by
      exact ⟨ψ, hψ, by simpa only [EReal.coe_neg] using hnlim⟩
    have hbound := extended_limit_le_limsup (fun n => -u n) (-a) hnmem
    simp only [EReal.coe_neg] at hbound
    rw [hneg] at hbound
    exact EReal.neg_le_neg_iff.mp hbound

  · exact sInf_le hmin

private theorem limsup_of_order_tendsto {Y : Type*} [CompleteLinearOrder Y]
    [DenselyOrdered Y] [TopologicalSpace Y] [OrderTopology Y]
    (u : ℕ → Y) (a : Y) (hu : Tendsto u atTop (𝓝 a)) : limsup u atTop = a := by
  apply (limsup_thresholds u a).mpr
  constructor
  · intro b hb
    exact eventually_atTop.mp ((tendsto_order.mp hu).2 b hb)
  · intro b hb N
    obtain ⟨M, hM⟩ := eventually_atTop.mp ((tendsto_order.mp hu).1 b hb)
    exact ⟨max N M, le_max_left _ _, hM _ (le_max_right _ _)⟩

/-- Lemma: both extended upper and lower limits equal a finite sequence limit. -/
theorem liminf_limsup_of_tendsto (u : ℕ → ℝ) (a : ℝ) (hu : Tendsto u atTop (𝓝 a)) :
    liminf (fun n => (u n : EReal)) atTop = (a : EReal) ∧
    limsup (fun n => (u n : EReal)) atTop = (a : EReal) := by
  have hE := EReal.tendsto_coe.mpr hu
  exact ⟨limsup_of_order_tendsto (Y := ERealᵒᵈ) _ _ hE,
    limsup_of_order_tendsto _ _ hE⟩

/-- Theorem: the lower limit of a real sequence never exceeds its upper limit. -/
theorem liminf_le_limsup (u : ℕ → ℝ) :
    liminf (fun n => (u n : EReal)) atTop ≤ limsup (fun n => (u n : EReal)) atTop := by
  rw [(liminf_eq_and_tendsto_tail_inf u).1, (limsup_eq_and_tendsto_tail_sup u).1]
  apply iSup_le
  intro N
  apply le_iInf
  intro M
  let k := max N M
  have hlow : (⨅ n ≥ N, (u n : EReal)) ≤ (u k : EReal) :=
    iInf_le_of_le k (iInf_le_of_le (le_max_left N M) le_rfl)
  have hupp : (u k : EReal) ≤ ⨆ n ≥ M, (u n : EReal) :=
    le_iSup_of_le k (le_iSup_of_le (le_max_right N M) le_rfl)
  exact hlow.trans hupp

/-- Lemma: nonnegative terms have nonnegative extended lower and upper limits. -/
theorem nonneg_liminf_limsup (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) :
    0 ≤ liminf (fun n => (u n : EReal)) atTop ∧
    0 ≤ limsup (fun n => (u n : EReal)) atTop := by
  have h := (liminf_limsup_mono (fun _ => 0) u
    (Eventually.of_forall hu)).1
  rw [(liminf_limsup_of_tendsto (fun _ => 0) 0 (real_tendsto_const 0)).1] at h
  exact ⟨h, h.trans (liminf_le_limsup u)⟩

/-- Lemma: a strict real lower bound for the lower limit holds eventually. -/
theorem eventually_gt_of_lt_liminf (u : ℕ → ℝ) (q : ℝ)
    (hq : (q : EReal) < liminf (fun n => (u n : EReal)) atTop) :
    ∀ᶠ n in atTop, q < u n := by
  have h := (limsup_thresholds (Y := ERealᵒᵈ) (fun n => (u n : EReal)) _).mp rfl
  obtain ⟨N, hN⟩ := h.1 (q : EReal) hq
  exact eventually_atTop.mpr ⟨N, fun n hn => EReal.coe_lt_coe_iff.mp (hN n hn)⟩

end MathematicalAnalysis.Chapter02
