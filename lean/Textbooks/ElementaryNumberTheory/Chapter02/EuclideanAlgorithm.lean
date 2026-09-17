import Textbooks.ElementaryNumberTheory.Chapter02.GreatestCommonDivisor
import Mathlib.Algebra.Order.Ring.Abs

namespace ElementaryNumberTheory.Chapter02

/-- Lemma: equal sets of common divisors determine equal gcds,
including the zero pair. -/
theorem gcd_eq_of_common_divisors (a b c d : ℤ)
    (h : ∀ z : ℤ, (z ∣ a ∧ z ∣ b) ↔ (z ∣ c ∧ z ∣ d)) :
    gcd a b = gcd c d := by
  by_cases hab : a ≠ 0 ∨ b ≠ 0
  · have hcd : c ≠ 0 ∨ d ≠ 0 := by
      by_contra hn
      push Not at hn
      obtain ⟨hc, hd⟩ := hn
      have hz := (h 0).2 ⟨⟨0, by simp [hc]⟩, ⟨0, by simp [hd]⟩⟩
      obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := hz
      simp only [zero_mul] at hu hv
      rcases hab with ha | hb
      · exact ha hu
      · exact hb hv
    obtain ⟨_, ha, hb, _⟩ := gcd_spec a b hab
    obtain ⟨_, hc, hd, _⟩ := gcd_spec c d hcd
    have h₁ := (h (gcd a b)).1 ⟨ha, hb⟩
    have h₂ := (h (gcd c d)).2 ⟨hc, hd⟩
    exact_mod_cast le_antisymm
      (common_divisor_le_gcd c d _ hcd h₁.1 h₁.2)
      (common_divisor_le_gcd a b _ hab h₂.1 h₂.2)
  · push Not at hab
    obtain ⟨rfl, rfl⟩ := hab
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := (h 0).1 ⟨⟨0, rfl⟩, ⟨0, rfl⟩⟩
    simp only [zero_mul] at hu hv
    rw [hu, hv]

/-- Lemma: replacing the dividend by a remainder preserves the gcd. -/
theorem gcd_eq_gcd_remainder (a b q r : ℤ) (ha : a = q * b + r) :
    gcd a b = gcd b r := by
  apply gcd_eq_of_common_divisors
  intro c
  constructor
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    refine ⟨⟨v, hv⟩, ⟨u - q * v, ?_⟩⟩
    calc
      r = a - q * b := by linarith [ha]
      _ = c * (u - q * v) := by rw [hu, hv]; ring
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    exact ⟨⟨q * u + v, by rw [ha, hu, hv]; ring⟩, ⟨u, hu⟩⟩

/-- Lemma: taking absolute values preserves the gcd. -/
theorem gcd_abs (a b : ℤ) : gcd |a| |b| = gcd a b := by
  have hdiv (c z : ℤ) : c ∣ |z| ↔ c ∣ z := by
    by_cases hz : 0 ≤ z
    · rw [abs_of_nonneg hz]
    · rw [abs_of_neg (lt_of_not_ge hz)]
      constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨-k, by linarith⟩
  exact gcd_eq_of_common_divisors _ _ _ _ (fun c => by rw [hdiv, hdiv])

/-- Lemma: a nonnegative integer paired with zero is its own gcd. -/
theorem gcd_zero_right (a : ℕ) : gcd (a : ℤ) 0 = a := by
  by_cases ha : a = 0
  · subst a
    exact gcd_zero_zero
  · apply gcd_eq_of_greatest _ _ (Or.inl (by exact_mod_cast ha)) a
    · exact ⟨1, by ring⟩
    · exact ⟨0, by ring⟩
    · rintro c ⟨k, hk⟩ _
      have ha' : (0 : ℤ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha
      by_cases hc : 0 < c
      · have hkpos : 0 < k := by nlinarith
        have hkone : 1 ≤ k := hkpos
        nlinarith
      · linarith

/-- Definition: a finite Euclidean division trace ending at the pair `(g, 0)`.
Each recursive step records a quotient and a strictly smaller natural remainder. -/
inductive EuclideanTrace : ℕ → ℕ → ℕ → Prop
  | done (a : ℕ) : EuclideanTrace a 0 a
  | step (a b r g : ℕ) (q : ℤ) (hr : r < b)
      (ha : (a : ℤ) = q * (b : ℤ) + (r : ℤ))
      (tail : EuclideanTrace b r g) : EuclideanTrace a b g

/-- Theorem: Euclidean division terminates, since the second
coordinate strictly decreases at each step. -/
theorem euclideanTrace_exists (a b : ℕ) : ∃ g, EuclideanTrace a b g := by
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
    by_cases hb : b = 0
    · subst b
      exact ⟨a, EuclideanTrace.done a⟩
    · obtain ⟨⟨q, r⟩, ⟨ha, hr⟩, _⟩ :=
        existsUnique_quotient_remainder (a : ℤ) ⟨b, Nat.pos_of_ne_zero hb⟩
      obtain ⟨g, hg⟩ := ih r hr b
      exact ⟨g, EuclideanTrace.step a b r g q hr ha hg⟩

/-- Theorem: the final nonzero entry of a Euclidean trace is the gcd.
For the zero pair the final entry is zero. -/
theorem EuclideanTrace.gcd_eq {a b g : ℕ} (h : EuclideanTrace a b g) :
    gcd (a : ℤ) (b : ℤ) = g := by
  induction h with
  | done a => exact gcd_zero_right a
  | step a b r g q hr ha tail ih =>
    exact (gcd_eq_gcd_remainder _ _ q _ ha).trans ih

/-- Corollary: for a positive second input, the terminal entry is
positive, so it is indeed the last nonzero remainder (or the initial divisor). -/
theorem EuclideanTrace.positive {a b g : ℕ} (h : EuclideanTrace a b g)
    (hb : 0 < b) : 0 < g := by
  rw [← h.gcd_eq]
  exact (gcd_spec a b (Or.inr (by exact_mod_cast (ne_of_gt hb)))).1

/-- Theorem: multiplying both inputs by a positive integer
multiplies their gcd by that integer. -/
theorem gcd_mul_of_pos (a b k : ℤ) (hk : 0 < k) :
    (gcd (k * a) (k * b) : ℤ) = k * (gcd a b : ℤ) := by
  by_cases hab : a ≠ 0 ∨ b ≠ 0
  · obtain ⟨hdpos, ⟨u, hu⟩, ⟨v, hv⟩, ⟨x, y, hxy⟩, _⟩ := gcd_spec a b hab
    have hpair : k * a ≠ 0 ∨ k * b ≠ 0 := by
      rcases hab with ha | hb
      · exact Or.inl (mul_ne_zero (ne_of_gt hk) ha)
      · exact Or.inr (mul_ne_zero (ne_of_gt hk) hb)
    have hdpos' : (0 : ℤ) < gcd a b := by exact_mod_cast hdpos
    apply Eq.symm
    apply (eq_gcd_iff_common_divisor _ _ _ hpair (mul_pos hk hdpos')).2
    refine ⟨⟨u, by nth_rw 1 [hu]; ring⟩, ⟨v, by nth_rw 1 [hv]; ring⟩, ?_⟩
    rintro c ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s * x + t * y, ?_⟩
    calc
      k * (gcd a b : ℤ) = (k * a) * x + (k * b) * y := by rw [hxy]; ring
      _ = c * (s * x + t * y) := by rw [hs, ht]; ring
  · push Not at hab
    obtain ⟨rfl, rfl⟩ := hab
    simp [gcd_zero_zero]

/-- Corollary: a nonzero integer factor scales the gcd by its
absolute value. -/
theorem gcd_mul_of_ne_zero (a b k : ℤ) (hk : k ≠ 0) :
    (gcd (k * a) (k * b) : ℤ) = |k| * (gcd a b : ℤ) := by
  calc
    (gcd (k * a) (k * b) : ℤ) = gcd (|k| * |a|) (|k| * |b|) := by
      rw [← gcd_abs (k * a) (k * b), abs_mul, abs_mul]
    _ = |k| * (gcd |a| |b| : ℤ) := gcd_mul_of_pos _ _ _ (abs_pos.mpr hk)
    _ = |k| * (gcd a b : ℤ) := by rw [gcd_abs]

end ElementaryNumberTheory.Chapter02
