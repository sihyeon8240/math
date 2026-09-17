import Textbooks.ElementaryNumberTheory.Chapter02.EuclideanAlgorithm

namespace ElementaryNumberTheory.Chapter02

/-- Lemma: two nonzero integers have a positive common multiple. -/
theorem exists_positive_common_multiple (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ a ∣ (m : ℤ) ∧ b ∣ (m : ℤ) := by
  have hp : 0 < (a * b) * (a * b) := mul_self_pos.mpr (mul_ne_zero ha hb)
  refine ⟨((a * b) * (a * b)).toNat, ?_, ?_, ?_⟩
  · omega
  · rw [Int.toNat_of_nonneg (le_of_lt hp)]
    exact ⟨a * b * b, by ring⟩
  · rw [Int.toNat_of_nonneg (le_of_lt hp)]
    exact ⟨a * a * b, by ring⟩

/-- Definition: the least positive common multiple of two nonzero integers.
The value is zero when either input is zero. -/
noncomputable def lcm (a b : ℤ) : ℕ :=
  if h : a ≠ 0 ∧ b ≠ 0 then
    Nat.find (exists_positive_common_multiple a b h.1 h.2)
  else 0

/-- Theorem: the lcm is positive, is a common multiple, and is
no larger than any positive integer common multiple. -/
theorem lcm_spec (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    0 < lcm a b ∧ a ∣ (lcm a b : ℤ) ∧ b ∣ (lcm a b : ℤ) ∧
      (∀ c : ℤ, a ∣ c → b ∣ c → 0 < c → (lcm a b : ℤ) ≤ c) := by
  classical
  rw [lcm, dif_pos ⟨ha, hb⟩]
  obtain ⟨hp, hma, hmb⟩ := Nat.find_spec (exists_positive_common_multiple a b ha hb)
  refine ⟨hp, hma, hmb, ?_⟩
  intro c hac hbc hc
  have hc' : (c.toNat : ℤ) = c := Int.toNat_of_nonneg (le_of_lt hc)
  have hmin := Nat.find_min' (exists_positive_common_multiple a b ha hb)
    (show 0 < c.toNat ∧ a ∣ (c.toNat : ℤ) ∧ b ∣ (c.toNat : ℤ) from
      ⟨by omega, by rwa [hc'], by rwa [hc']⟩)
  exact_mod_cast (show (Nat.find (exists_positive_common_multiple a b ha hb) : ℤ) ≤ c by
    exact (Int.ofNat_le.mpr hmin).trans_eq hc')

/-- Theorem: the least-positive-common-multiple conditions
uniquely characterize the lcm. -/
theorem lcm_eq_of_least (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (m : ℕ)
    (hm : 0 < m) (ham : a ∣ (m : ℤ)) (hbm : b ∣ (m : ℤ))
    (hleast : ∀ c : ℤ, a ∣ c → b ∣ c → 0 < c → (m : ℤ) ≤ c) :
    lcm a b = m := by
  obtain ⟨hp, hla, hlb, hmin⟩ := lcm_spec a b ha hb
  exact_mod_cast le_antisymm
    (hmin m ham hbm (by exact_mod_cast hm))
    (hleast (lcm a b) hla hlb (by exact_mod_cast hp))

/-- Theorem: for positive integers, the product of the gcd and
lcm equals the product of the inputs. -/
theorem gcd_mul_lcm (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    (gcd a b : ℤ) * (lcm a b : ℤ) = a * b := by
  obtain ⟨hd, ⟨u, hu⟩, ⟨v, hv⟩, ⟨x, y, hxy⟩, _⟩ :=
    gcd_spec a b (Or.inl (ne_of_gt ha))
  generalize hg : gcd a b = d at *
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have hvpos : 0 < v := by nlinarith [hv]
  have hmpos : 0 < a * v := mul_pos ha hvpos
  have ham : a ∣ a * v := ⟨v, rfl⟩
  have hbm : b ∣ a * v := ⟨u, by rw [hu, hv]; ring⟩
  have hdiv (c : ℤ) (hac : a ∣ c) (hbc : b ∣ c) : a * v ∣ c := by
    obtain ⟨s, hs⟩ := hac
    obtain ⟨t, ht⟩ := hbc
    refine ⟨t * x + s * y, ?_⟩
    apply mul_left_cancel₀ (ne_of_gt hd')
    calc
      (d : ℤ) * c = (a * x + b * y) * c := by rw [hxy]
      _ = a * c * x + b * c * y := by ring
      _ = a * (b * t) * x + b * (a * s) * y := by nth_rw 1 [ht]; rw [hs]
      _ = (d : ℤ) * (a * v * (t * x + s * y)) := by rw [hv]; ring
  obtain ⟨hlpos, hla, hlb, hleast⟩ := lcm_spec a b (ne_of_gt ha) (ne_of_gt hb)
  have hle : (lcm a b : ℤ) ≤ a * v := hleast _ ham hbm hmpos
  obtain ⟨k, hk⟩ := hdiv (lcm a b) hla hlb
  have hlpos' : (0 : ℤ) < lcm a b := by exact_mod_cast hlpos
  have hkpos : 0 < k := by nlinarith
  have hkone : 1 ≤ k := hkpos
  have heq : (lcm a b : ℤ) = a * v := by nlinarith
  rw [heq, hv]
  ring

end ElementaryNumberTheory.Chapter02
