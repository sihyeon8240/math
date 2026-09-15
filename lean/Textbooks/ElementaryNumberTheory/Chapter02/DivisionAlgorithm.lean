import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith

namespace ElementaryNumberTheory.Chapter02

/-- Theorem: division algorithm for a positive divisor.
Mathlib counterpart: `Int.ediv_emod_unique`. -/
theorem existsUnique_quotient_remainder (a : ℤ) (b : ℕ+) :
    ∃! qr : ℤ × ℕ,
      a = qr.1 * b + qr.2 ∧ qr.2 < b := by

  classical

  have hb : (1 : ℤ) ≤ (b : ℤ) := by
    exact_mod_cast b.pos

  have hnonneg : 0 ≤ a - (-|a|) * (b : ℤ) := by
    have ha : -|a| ≤ a := neg_abs_le a
    have habs : 0 ≤ |a| := abs_nonneg a
    nlinarith

  let h : ∃ n : ℕ, ∃ q : ℤ, a - q * b = (n : ℤ) :=
    ⟨(a - (-|a|) * b).toNat, -|a|, (Int.toNat_of_nonneg hnonneg).symm⟩

  obtain ⟨q, hq⟩ := Nat.find_spec h

  let r : ℕ := Nat.find h

  have hr0 : (0 : ℤ) ≤ r := Int.natCast_nonneg _

  have hminimal :
      ∀ s : ℤ, 0 ≤ s → (∃ x : ℤ, a - x * b = s) → (r : ℤ) ≤ s := by
    intro s hs ⟨x, hx⟩

    have hn : Nat.find h ≤ s.toNat :=
      Nat.find_min' h ⟨x, hx.trans (Int.toNat_of_nonneg hs).symm⟩

    have hc : (Nat.find h : ℤ) ≤ (s.toNat : ℤ) :=
      Int.ofNat_le.mpr hn

    rwa [Int.toNat_of_nonneg hs] at hc

  have hrb_int : (r : ℤ) < b := by
    by_contra hnot

    have hs : 0 ≤ (r : ℤ) - b := by
      linarith

    have hsmaller := hminimal ((r : ℤ) - b) hs ⟨q + 1, by
      dsimp [r]
      nlinarith [hq]⟩

    linarith

  have ha : a = q * b + r := by
    dsimp [r]
    linarith [hq]

  have hrb : r < (b : ℕ) := by
    exact_mod_cast hrb_int

  refine ⟨(q, r), ⟨ha, hrb⟩, ?_⟩

  rintro ⟨q', r'⟩ ⟨ha', hr'b⟩

  change a = q' * b + r' at ha'

  have hr'0 : (0 : ℤ) ≤ r' := Int.natCast_nonneg _

  have hr'b_int : (r' : ℤ) < b := by
    exact_mod_cast hr'b

  have hqq : q' = q := by
    rcases lt_trichotomy q' q with hlt | heq | hgt

    · have hstep : q' + 1 ≤ q := hlt
      nlinarith

    · exact heq

    · have hstep : q + 1 ≤ q' := hgt
      nlinarith

  have hrr_int : (r' : ℤ) = r := by
    rw [hqq] at ha'
    linarith

  have hrr : r' = r := by
    exact_mod_cast hrr_int

  exact Prod.ext hqq hrr

/-- Theorem: division algorithm for a nonzero integer divisor. -/
theorem existsUnique_quotient_remainder_of_ne_zero (a b : ℤ) (hb : b ≠ 0) :
    ∃! qr : ℤ × ℕ,
      a = qr.1 * b + qr.2 ∧ (qr.2 : ℤ) < |b| := by

  have habs : 0 < |b| := abs_pos.mpr hb

  let d : ℕ+ := ⟨|b|.toNat, by omega⟩

  have hd : (d : ℤ) = |b| :=
    Int.toNat_of_nonneg (abs_nonneg b)

  obtain ⟨⟨q, r⟩, ⟨ha, hr⟩, huniq⟩ :=
    existsUnique_quotient_remainder a d

  change a = q * (d : ℤ) + (r : ℤ) at ha

  have hrabs : (r : ℤ) < |b| := by
    rw [← hd]
    exact_mod_cast hr

  rw [hd] at ha

  rcases lt_or_gt_of_ne hb with hbneg | hbpos

  · have habsneg : |b| = -b := abs_of_neg hbneg

    refine ⟨(-q, r), ⟨?_, hrabs⟩, ?_⟩

    · rw [habsneg] at ha
      nlinarith

    · rintro ⟨q', r'⟩ ⟨ha', hr'⟩

      have hr'd : r' < (d : ℕ) := by
        exact_mod_cast (show (r' : ℤ) < (d : ℤ) by
          rw [hd]
          exact hr')

      have hpair : (-q', r') = (q, r) := by
        apply huniq
        constructor

        · change a = (-q') * (d : ℤ) + (r' : ℤ)
          rw [hd, habsneg]
          nlinarith [ha']

        · exact hr'd

      have hq : -q' = q :=
        congrArg Prod.fst hpair

      have hrr : r' = r :=
        congrArg Prod.snd hpair

      apply Prod.ext
      · linarith
      · exact hrr

  · have habspos : |b| = b := abs_of_pos hbpos

    refine ⟨(q, r), ⟨?_, hrabs⟩, ?_⟩

    · rwa [habspos] at ha

    · rintro ⟨q', r'⟩ ⟨ha', hr'⟩

      have hr'd : r' < (d : ℕ) := by
        exact_mod_cast (show (r' : ℤ) < (d : ℤ) by
          rw [hd]
          exact hr')

      have hpair : (q', r') = (q, r) := by
        apply huniq
        constructor

        · change a = q' * (d : ℤ) + (r' : ℤ)
          rw [hd, habspos]
          exact ha'

        · exact hr'd

      exact hpair

end ElementaryNumberTheory.Chapter02
