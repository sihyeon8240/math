import Textbooks.ElementaryNumberTheory.Chapter03.DigitTests

namespace ElementaryNumberTheory.Chapter03

/-- Definition: positional value of natural-number digits, units digit first. -/
def digitValue (b : ℕ) : List ℕ → ℕ

  | [] => 0

  | d :: ds => d + b * digitValue b ds

/-- Definition: bounded digits with no leading zero; the empty list represents zero. -/
def CanonicalDigits (b : ℕ) : List ℕ → Prop

  | [] => True

  | d :: ds => d < b ∧ (ds = [] → d ≠ 0) ∧ CanonicalDigits b ds

/-- Lemma: a nonempty canonical expansion has positive value. -/
theorem digitValue_pos (b : ℕ) (hb : 1 < b) (ds : List ℕ)
    (h : CanonicalDigits b ds) (hne : ds ≠ []) : 0 < digitValue b ds := by
  induction ds with
  | nil => exact (hne rfl).elim

  | cons d ds ih =>
    change d < b ∧ (ds = [] → d ≠ 0) ∧ CanonicalDigits b ds at h
    change 0 < d + b * digitValue b ds
    by_cases he : ds = []

    · have := h.2.1 he
      omega

    · have hh := ih h.2.2 he
      nlinarith

/-- Theorem: canonical base-b expansions are unique. -/
theorem digitValue_injective (b : ℕ) (hb : 1 < b) (ds es : List ℕ)
    (hd : CanonicalDigits b ds) (he : CanonicalDigits b es)
    (hv : digitValue b ds = digitValue b es) : ds = es := by
  induction ds generalizing es with
  | nil =>
    by_contra hh

    have hne : es ≠ [] := Ne.symm hh

    have hp := digitValue_pos b hb es he hne
    change 0 = digitValue b es at hv
    omega

  | cons d ds ih =>
    cases es with
    | nil =>
      have hp := digitValue_pos b hb (d :: ds) hd
        (by simp only [ne_eq, List.cons_ne_nil, not_false_eq_true])
      change digitValue b (d :: ds) = 0 at hv
      omega

    | cons e es =>
      obtain ⟨_, _, hu⟩ := Chapter01.existsUnique_quotient_remainder
        (digitValue b (d :: ds)) ⟨b, by omega⟩

      have hd' := hu ((digitValue b ds : ℤ), d) ⟨by
        change ((digitValue b (d :: ds) : ℕ) : ℤ) = (digitValue b ds : ℤ) * b + d
        simp only [digitValue, Nat.cast_add, Nat.cast_mul]
        ring, hd.1⟩

      have he' := hu ((digitValue b es : ℤ), e) ⟨by
        change ((digitValue b (d :: ds) : ℕ) : ℤ) = (digitValue b es : ℤ) * b + e
        rw [hv]
        simp only [digitValue, Nat.cast_add, Nat.cast_mul]
        ring, he.1⟩

      have hh := hd'.trans he'.symm

      have hde : d = e := congrArg Prod.snd hh

      have htail : digitValue b ds = digitValue b es := by
        have hh' : (digitValue b ds : ℤ) = digitValue b es := congrArg Prod.fst hh
        exact_mod_cast hh'
      rw [hde, ih es hd.2.2 he.2.2 htail]

/-- Theorem: every natural number has a unique canonical positional expansion. -/
theorem existsUnique_digits (b : ℕ) (hb : 1 < b) (n : ℕ) :
    ∃! ds : List ℕ, CanonicalDigits b ds ∧ digitValue b ds = n := by
  have hex : ∀ n : ℕ, ∃ ds : List ℕ, CanonicalDigits b ds ∧ digitValue b ds = n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n = 0

      · exact ⟨[], trivial, by exact hn.symm⟩

      · obtain ⟨⟨q, r⟩, ⟨heq, hr⟩, _⟩ :=
          Chapter01.existsUnique_quotient_remainder n ⟨b, by omega⟩
        change (n : ℤ) = q * b + r at heq
        change r < b at hr

        have hb' : (1 : ℤ) < b := by
          exact_mod_cast hb

        have hr' : (r : ℤ) < b := by
          exact_mod_cast hr
        have hq : 0 ≤ q := by
          nlinarith
        have hnpos : (0 : ℤ) < n := by
          omega
        have hqn : q < n := by
          nlinarith
        have hlt : q.toNat < n := by
          omega

        obtain ⟨ds, hds, hval⟩ := ih q.toNat hlt

        refine ⟨r :: ds, ⟨hr, ?_, hds⟩, ?_⟩

        · intro hnil hrzero
          rw [hnil] at hval
          change 0 = q.toNat at hval

          have : q = 0 := by
            omega
          rw [this, hrzero] at heq
          simp only [zero_mul, Nat.cast_zero, add_zero] at heq
          exact hn (by exact_mod_cast heq)

        · change r + b * digitValue b ds = n
          rw [hval]

          have hc : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq
          exact_mod_cast (show (r : ℤ) + (b : ℤ) * q.toNat = n by
              rw [hc]
              nlinarith)

  obtain ⟨ds, hd, hv⟩ := hex n

  exact ⟨ds, ⟨hd, hv⟩, fun es he => digitValue_injective b hb es ds he.1 hd (he.2.trans hv.symm)⟩

/-- Corollary: binary expansions use only zero and one, and are unique. -/
theorem existsUnique_binary_digits (n : ℕ) :
    ∃! ds : List ℕ, CanonicalDigits 2 ds ∧ digitValue 2 ds = n :=
  existsUnique_digits 2 (by decide) n

/-- Theorem: the two representations agree after casting to integers. -/
theorem digitValue_eq_positionalValue (b : ℕ) (ds : List ℕ) :
    (digitValue b ds : ℤ) = positionalValue b (ds.map Nat.cast) := by
  induction ds with
  | nil => rfl

  | cons d ds ih =>
    simp only [digitValue, positionalValue, List.map_cons, Nat.cast_add, Nat.cast_mul, ih]

end ElementaryNumberTheory.Chapter03
