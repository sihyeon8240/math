import Textbooks.ElementaryNumberTheory.Chapter03.Congruences

namespace ElementaryNumberTheory.Chapter03

/-- Theorem: a linear congruence is an integer linear equation. -/
theorem linear_modEq_iff (n a b x : ℤ) :
    a * x ≡ b [ZMOD n] ↔ ∃ y : ℤ, a * x + n * y = b := by
  rw [modEq_iff_dvd_sub]
  constructor

  · rintro ⟨k, hk⟩
    exact ⟨-k, by nlinarith⟩

  · rintro ⟨y, hy⟩
    exact ⟨-y, by nlinarith⟩

/-- Theorem: solvability of a linear congruence is characterized by the gcd. -/
theorem exists_linear_modEq_iff (n a b : ℤ) :
    (∃ x : ℤ, a * x ≡ b [ZMOD n]) ↔ (Chapter01.gcd a n : ℤ) ∣ b := by
  simp only [linear_modEq_iff]
  exact Chapter01.exists_mul_add_mul_eq_iff a n b

/-- Theorem: all solutions of a solvable linear congruence form an arithmetic progression. -/
theorem linear_modEq_iff_eq_add (n a b x₀ x : ℤ) (hn : n ≠ 0)
    (h₀ : a * x₀ ≡ b [ZMOD n]) :
    a * x ≡ b [ZMOD n] ↔ ∃ t : ℤ,
      x = x₀ + (n / (Chapter01.gcd a n : ℤ)) * t := by
  obtain ⟨y₀, hy₀⟩ := (linear_modEq_iff n a b x₀).1 h₀
  rw [linear_modEq_iff]
  constructor

  · rintro ⟨y, hy⟩

    obtain ⟨t, ht, _⟩ :=
      (Chapter01.mul_add_mul_eq_iff a n b x₀ y₀ x y (Or.inr hn) hy₀).1 hy

    exact ⟨t, ht⟩

  · rintro ⟨t, ht⟩
    refine ⟨y₀ - (a / (Chapter01.gcd a n : ℤ)) * t, ?_⟩
    exact (Chapter01.mul_add_mul_eq_iff a n b x₀ y₀ x _ (Or.inr hn) hy₀).2
      ⟨t, ht, rfl⟩

/-- Corollary: coprime coefficients give a solution unique modulo the modulus. -/
theorem exists_unique_linear_modEq (n a b : ℤ) (hn : n ≠ 0)
    (ha : Chapter01.gcd a n = 1) :
    ∃ x₀ : ℤ, a * x₀ ≡ b [ZMOD n] ∧
      ∀ x : ℤ, a * x ≡ b [ZMOD n] ↔ x ≡ x₀ [ZMOD n] := by
  obtain ⟨x₀, hx₀⟩ := (exists_linear_modEq_iff n a b).2 (by
    rw [ha, Nat.cast_one]
    exact ⟨b, by ring⟩)

  refine ⟨x₀, hx₀, ?_⟩
  intro x
  rw [linear_modEq_iff_eq_add n a b x₀ x hn hx₀, ha, Nat.cast_one, Int.ediv_one,
    modEq_iff_dvd_sub]

  constructor

  · rintro ⟨t, ht⟩
    exact ⟨t, by linarith⟩

  · rintro ⟨t, ht⟩
    exact ⟨t, by linarith⟩

/-- Definition: a modular inverse is an integer whose product with the given integer is
congruent to one. -/
def IsModularInverse (n a u : ℤ) : Prop := a * u ≡ 1 [ZMOD n]

/-- Corollary: a coprime integer admits a modular inverse. -/
theorem exists_modularInverse (n a : ℤ) (ha : Chapter01.gcd a n = 1) :
    ∃ u : ℤ, IsModularInverse n a u := by

  apply (exists_linear_modEq_iff n a 1).2
  rw [ha, Nat.cast_one]

/-- Theorem: multiplication by an inverse solves a linear congruence. -/
theorem linear_modEq_iff_inverse (n a b u x : ℤ) (hu : IsModularInverse n a u) :
    a * x ≡ b [ZMOD n] ↔ x ≡ u * b [ZMOD n] := by

  constructor

  · intro hx

    have h₁ := modEq_mul (modEq_refl n u) hx

    have h₂ := modEq_mul hu (modEq_refl n x)

    have heq : u * (a * x) = (a * u) * x := by ring
    rw [heq] at h₁
    exact modEq_trans (modEq_symm (by simpa only [one_mul] using h₂)) h₁

  · intro hx

    have h₁ := modEq_mul (modEq_refl n a) hx

    have h₂ := modEq_mul hu (modEq_refl n b)

    have heq : a * (u * b) = (a * u) * b := by ring
    rw [heq] at h₁
    exact modEq_trans h₁ (by simpa only [one_mul] using h₂)

/-- Theorem: two coprime moduli admit a simultaneous solution, unique modulo their product. This
is the two-modulus Chinese remainder theorem. -/
theorem chinese_remainder_pair (m n a b : ℤ) (h : Chapter01.gcd m n = 1) :
    ∃ x : ℤ, x ≡ a [ZMOD m] ∧ x ≡ b [ZMOD n] ∧
      ∀ y : ℤ, (y ≡ a [ZMOD m] ∧ y ≡ b [ZMOD n]) ↔ y ≡ x [ZMOD m * n] := by
  have hnz : m ≠ 0 ∨ n ≠ 0 := by
    by_contra hh
    push Not at hh

    obtain ⟨rfl, rfl⟩ := hh
    rw [Chapter01.gcd_zero_zero] at h
    contradiction

  obtain ⟨u, v, huv⟩ := (Chapter01.gcd_eq_one_iff_exists_mul_add_mul m n hnz).1 h

  let x := b * m * u + a * n * v

  have hma : x ≡ a [ZMOD m] := by
    apply (modEq_iff_dvd_sub _ _ _).2
    exact ⟨(b - a) * u, by
        dsimp [x]
        nlinarith [congrArg (fun z => a * z) huv]⟩

  have hnb : x ≡ b [ZMOD n] := by
    apply (modEq_iff_dvd_sub _ _ _).2
    exact ⟨(a - b) * v, by
        dsimp [x]
        nlinarith [congrArg (fun z => b * z) huv]⟩

  refine ⟨x, hma, hnb, ?_⟩
  intro y
  constructor

  · rintro ⟨hya, hyb⟩
    exact (modEq_iff_dvd_sub _ _ _).2 (Chapter01.mul_dvd_of_coprime m n (y - x) h
      ((modEq_iff_dvd_sub _ _ _).1 (modEq_trans hya (modEq_symm hma)))
      ((modEq_iff_dvd_sub _ _ _).1 (modEq_trans hyb (modEq_symm hnb))))

  · intro hy

    obtain ⟨k, hk⟩ := (modEq_iff_dvd_sub _ _ _).1 hy

    exact ⟨modEq_trans ((modEq_iff_dvd_sub _ _ _).2 ⟨n * k, by nlinarith⟩) hma,
      modEq_trans ((modEq_iff_dvd_sub _ _ _).2 ⟨m * k, by nlinarith⟩) hnb⟩

/-- Theorem: the gcd indexes exactly the incongruent solutions of a solvable congruence. -/
theorem linear_solution_classes (n a b x₀ : ℤ) (hn : 0 < n)
    (h₀ : a * x₀ ≡ b [ZMOD n]) :
    (∀ t : Fin (Chapter01.gcd a n),
      a * (x₀ + (n / (Chapter01.gcd a n : ℤ)) * t.val) ≡ b [ZMOD n]) ∧
    (∀ x : ℤ, a * x ≡ b [ZMOD n] →
      ∃! t : Fin (Chapter01.gcd a n),
        x ≡ x₀ + (n / (Chapter01.gcd a n : ℤ)) * t.val [ZMOD n]) := by
  have hnne := ne_of_gt hn

  obtain ⟨hg, _, ⟨u, hu⟩, _, _⟩ := Chapter01.gcd_spec a n (Or.inr hnne)

  have hgne : (Chapter01.gcd a n : ℤ) ≠ 0 := by exact_mod_cast ne_of_gt hg

  have hquot : n / (Chapter01.gcd a n : ℤ) = u := by
    calc
      n / (Chapter01.gcd a n : ℤ) =
          ((Chapter01.gcd a n : ℤ) * u) / (Chapter01.gcd a n : ℤ) :=
        congrArg (fun z => z / (Chapter01.gcd a n : ℤ)) hu
      _ = u := Int.mul_ediv_cancel_left u hgne

  have hupos : 0 < u := by
    have hgz : (0 : ℤ) < Chapter01.gcd a n := by exact_mod_cast hg
    nlinarith

  constructor

  · intro t
    exact (linear_modEq_iff_eq_add n a b x₀ _ hnne h₀).2 ⟨t.val, rfl⟩

  · intro x hx

    obtain ⟨t, ht⟩ := (linear_modEq_iff_eq_add n a b x₀ x hnne h₀).1 hx
    obtain ⟨⟨q, r⟩, ⟨htr, hr⟩, _⟩ :=
      Chapter01.existsUnique_quotient_remainder t ⟨Chapter01.gcd a n, hg⟩

    change t = q * (Chapter01.gcd a n : ℤ) + r at htr
    change r < Chapter01.gcd a n at hr

    have hrep : x ≡ x₀ + (n / (Chapter01.gcd a n : ℤ)) * r [ZMOD n] := by
      apply (modEq_iff_dvd_sub _ _ _).2
      refine ⟨q, ?_⟩
      rw [hquot] at ht ⊢
      rw [ht]
      nlinarith [congrArg (fun z => z * q) hu, congrArg (fun z => u * z) htr]

    refine ⟨⟨r, hr⟩, hrep, ?_⟩
    intro s hs

    have hdiff := modEq_trans (modEq_symm hs) hrep

    obtain ⟨k, hk⟩ := (modEq_iff_dvd_sub _ _ _).1 hdiff
    rw [hquot] at hk

    have he : (s.val : ℤ) - r = (Chapter01.gcd a n : ℤ) * k := by
      apply mul_left_cancel₀ (ne_of_gt hupos)
      calc
        u * ((s.val : ℤ) - r) = (x₀ + u * s.val) - (x₀ + u * r) := by ring
        _ = u * ((Chapter01.gcd a n : ℤ) * k) := by
          rw [hk]
          nlinarith [congrArg (fun z => z * k) hu]

    have hsbound : (s.val : ℤ) < Chapter01.gcd a n := by exact_mod_cast s.isLt

    have hrbound : (r : ℤ) < Chapter01.gcd a n := by exact_mod_cast hr

    have hgz : (0 : ℤ) < Chapter01.gcd a n := by exact_mod_cast hg

    have hkzero : k = 0 := by
      rcases lt_trichotomy k 0 with hneg | hzero | hpos

      · have : k ≤ -1 := by omega
        nlinarith [Int.natCast_nonneg s.val, Int.natCast_nonneg r]

      · exact hzero

      · have : 1 ≤ k := hpos
        nlinarith [Int.natCast_nonneg s.val, Int.natCast_nonneg r]

    apply Fin.ext

    have hval : (s.val : ℤ) = r := by
      rw [hkzero, mul_zero] at he
      linarith
    exact_mod_cast hval

end ElementaryNumberTheory.Chapter03
