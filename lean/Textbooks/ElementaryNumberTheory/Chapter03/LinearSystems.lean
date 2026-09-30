import Textbooks.ElementaryNumberTheory.Chapter03.LinearCongruences
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

namespace ElementaryNumberTheory.Chapter03

/-- Lemma: an invertible determinant solves a two-by-two system over a ring. -/
private theorem two_equations {R : Type*} [CommRing R] (a b c d r s t x y : R)
    (ht : (a * d - b * c) * t = 1) :
    (a * x + b * y = r ∧ c * x + d * y = s) ↔
      x = t * (d * r - b * s) ∧ y = t * (a * s - c * r) := by

  constructor

  · rintro ⟨hx, hy⟩
    constructor

    · linear_combination t * d * hx - t * b * hy - x * ht

    · linear_combination t * a * hy - t * c * hx - y * ht

  · rintro ⟨rfl, rfl⟩
    constructor

    · linear_combination r * ht

    · linear_combination s * ht

/-- Theorem: an inverse determinant gives the unique solution modulo n. -/
theorem linear_system_iff (n : ℕ) (a b c d r s t x y : ℤ)
    (ht : (a * d - b * c) * t ≡ 1 [ZMOD (n : ℤ)]) :
    (a * x + b * y ≡ r [ZMOD (n : ℤ)] ∧ c * x + d * y ≡ s [ZMOD (n : ℤ)]) ↔
      x ≡ t * (d * r - b * s) [ZMOD (n : ℤ)] ∧
      y ≡ t * (a * s - c * r) [ZMOD (n : ℤ)] := by
  simp only [← ZMod.intCast_eq_intCast_iff, Int.cast_add, Int.cast_mul,
    Int.cast_sub, Int.cast_one] at ht ⊢

  exact two_equations (a : ZMod n) b c d r s t x y ht

/-- Corollary: a determinant coprime to n guarantees a unique solution pair. -/
theorem exists_unique_linear_system (n : ℕ) (a b c d r s : ℤ)
    (hdet : Chapter01.gcd (a * d - b * c) n = 1) :
    ∃ x₀ y₀ : ℤ, ∀ x y : ℤ,
      (a * x + b * y ≡ r [ZMOD (n : ℤ)] ∧ c * x + d * y ≡ s [ZMOD (n : ℤ)]) ↔
        x ≡ x₀ [ZMOD (n : ℤ)] ∧ y ≡ y₀ [ZMOD (n : ℤ)] := by
  obtain ⟨t, ht⟩ := exists_modularInverse n (a * d - b * c) hdet

  exact ⟨t * (d * r - b * s), t * (a * s - c * r),
    fun x y => linear_system_iff n a b c d r s t x y ht⟩

end ElementaryNumberTheory.Chapter03
