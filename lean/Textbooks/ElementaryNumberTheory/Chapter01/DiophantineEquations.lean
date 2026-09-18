import Textbooks.ElementaryNumberTheory.Chapter01.GreatestCommonDivisor

namespace ElementaryNumberTheory.Chapter01

/-- Theorem: an integer linear equation is solvable exactly when its gcd divides
its constant term, including the equation with both coefficients zero. -/
theorem exists_mul_add_mul_eq_iff (a b c : ℤ) :
    (∃ x y : ℤ, a * x + b * y = c) ↔ (gcd a b : ℤ) ∣ c := by
  by_cases hab : a ≠ 0 ∨ b ≠ 0

  · obtain ⟨_, ⟨u, hu⟩, ⟨v, hv⟩, ⟨r, s, hrs⟩, _⟩ := gcd_spec a b hab
    generalize hg : gcd a b = d at *
    constructor

    · rintro ⟨x, y, rfl⟩
      refine ⟨u * x + v * y, ?_⟩
      rw [hu, hv]
      ring

    · rintro ⟨k, rfl⟩
      refine ⟨r * k, s * k, ?_⟩
      rw [hrs]
      ring

  · have ha : a = 0 := Classical.byContradiction (fun h => hab (Or.inl h))
    have hb : b = 0 := Classical.byContradiction (fun h => hab (Or.inr h))
    simp [ha, hb, gcd_zero_zero, eq_comm]

/-- Theorem: all solutions are obtained from one solution by an integer parameter.
The nonzero-pair hypothesis is necessary for this parametrization. -/
theorem mul_add_mul_eq_iff (a b c x₀ y₀ x y : ℤ) (hab : a ≠ 0 ∨ b ≠ 0)
    (h₀ : a * x₀ + b * y₀ = c) :
    a * x + b * y = c ↔ ∃ t : ℤ,
      x = x₀ + (b / (gcd a b : ℤ)) * t ∧
      y = y₀ - (a / (gcd a b : ℤ)) * t := by
  obtain ⟨hd, ⟨u, hu⟩, ⟨v, hv⟩, ⟨r, s, hrs⟩, _⟩ := gcd_spec a b hab
  generalize hg : gcd a b = d at *

  have hdne : (d : ℤ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hd)

  have ha : a / (d : ℤ) = u := by
    rw [hu]
    exact Int.mul_ediv_cancel_left u hdne

  have hb : b / (d : ℤ) = v := by
    rw [hv]
    exact Int.mul_ediv_cancel_left v hdne

  have hone : u * r + v * s = 1 := by
    apply mul_left_cancel₀ hdne
    calc
      (d : ℤ) * (u * r + v * s) = a * r + b * s := by
        rw [hu, hv]
        ring
      _ = (d : ℤ) * 1 := by linarith [hrs]

  rw [ha, hb]
  constructor

  · intro h
    have hdiff : u * (x - x₀) + v * (y - y₀) = 0 := by
      apply mul_left_cancel₀ hdne
      calc
        (d : ℤ) * (u * (x - x₀) + v * (y - y₀)) =
            (a * x + b * y) - (a * x₀ + b * y₀) := by
              rw [hu, hv]
              ring
        _ = (d : ℤ) * 0 := by
          rw [h, h₀]
          ring

    refine ⟨s * (x - x₀) - r * (y - y₀), ?_, ?_⟩

    · nlinarith [congrArg (fun z => z * (x - x₀)) hone,
        congrArg (fun z => z * r) hdiff]
    · nlinarith [congrArg (fun z => z * (y - y₀)) hone,
        congrArg (fun z => z * s) hdiff]

  · rintro ⟨t, rfl, rfl⟩
    calc
      a * (x₀ + v * t) + b * (y₀ - u * t) = a * x₀ + b * y₀ := by
        rw [hu, hv]
        ring
      _ = c := h₀

/-- Corollary: coprime coefficients give the steps b and -a. -/
theorem mul_add_mul_eq_iff_of_coprime (a b c x₀ y₀ x y : ℤ)
    (hab : gcd a b = 1) (h₀ : a * x₀ + b * y₀ = c) :
    a * x + b * y = c ↔ ∃ t : ℤ, x = x₀ + b * t ∧ y = y₀ - a * t := by
  have hnz : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨rfl, rfl⟩ := h
    rw [gcd_zero_zero] at hab
    contradiction

  simpa only [hab, Nat.cast_one, Int.ediv_one] using
    mul_add_mul_eq_iff a b c x₀ y₀ x y hnz h₀

end ElementaryNumberTheory.Chapter01
