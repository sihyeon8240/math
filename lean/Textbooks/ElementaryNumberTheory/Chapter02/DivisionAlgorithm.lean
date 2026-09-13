import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith

namespace ElementaryNumberTheory.Chapter02

-- Mathlib counterpart: `Int.ediv_emod_unique`
theorem existsUnique_quotient_remainder (a : ℤ) (b : ℕ+) :
    ∃! qr : ℤ × ℕ, a = qr.1 * b + qr.2 ∧ qr.2 < b := by
  classical
  have hb : (1 : ℤ) ≤ (b : ℤ) := by exact_mod_cast b.pos
  have hnonneg : 0 ≤ a - (-|a|) * (b : ℤ) := by
    have ha : -|a| ≤ a := neg_abs_le a
    have habs : 0 ≤ |a| := abs_nonneg a
    nlinarith
  let h : ∃ n : ℕ, ∃ q : ℤ, a - q * b = (n : ℤ) :=
    ⟨(a - (-|a|) * b).toNat, -|a|, (Int.toNat_of_nonneg hnonneg).symm⟩
  obtain ⟨q, hq⟩ := Nat.find_spec h
  let r : ℕ := Nat.find h
  have hr0 : (0 : ℤ) ≤ r := Int.natCast_nonneg _
  have hminimal : ∀ s : ℤ, 0 ≤ s → (∃ x : ℤ, a - x * b = s) → (r : ℤ) ≤ s := by
    intro s hs ⟨x, hx⟩
    have hn : Nat.find h ≤ s.toNat :=
      Nat.find_min' h ⟨x, hx.trans (Int.toNat_of_nonneg hs).symm⟩
    have hc : (Nat.find h : ℤ) ≤ (s.toNat : ℤ) := Int.ofNat_le.mpr hn
    rwa [Int.toNat_of_nonneg hs] at hc
  have hrb_int : (r : ℤ) < b := by
    by_contra hnot
    have hs : 0 ≤ (r : ℤ) - b := by linarith
    have hsmaller := hminimal ((r : ℤ) - b) hs ⟨q + 1, by dsimp [r]; nlinarith [hq]⟩
    linarith
  have ha : a = q * b + r := by dsimp [r]; linarith [hq]
  have hrb : r < (b : ℕ) := by exact_mod_cast hrb_int
  refine ⟨(q, r), ⟨ha, hrb⟩, ?_⟩
  rintro ⟨q', r'⟩ ⟨ha', hr'b⟩
  change a = q' * b + r' at ha'
  have hr'0 : (0 : ℤ) ≤ r' := Int.natCast_nonneg _
  have hr'b_int : (r' : ℤ) < b := by exact_mod_cast hr'b
  have hqq : q' = q := by
    rcases lt_trichotomy q' q with hlt | heq | hgt
    · have hstep : q' + 1 ≤ q := hlt
      nlinarith
    · exact heq
    · have hstep : q + 1 ≤ q' := hgt
      nlinarith
  have hrr_int : (r' : ℤ) = r := by rw [hqq] at ha'; linarith
  have hrr : r' = r := by exact_mod_cast hrr_int
  exact Prod.ext hqq hrr

end ElementaryNumberTheory.Chapter02
