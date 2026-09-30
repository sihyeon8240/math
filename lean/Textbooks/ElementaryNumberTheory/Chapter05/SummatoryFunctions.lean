import Textbooks.ElementaryNumberTheory.Chapter05.MobiusInversion
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace ElementaryNumberTheory.Chapter05

/-- Theorem: the number of positive multiples of k up to N is N/k. -/
theorem card_multiples (N k : ℕ) (hk : 0 < k) :
    ((Finset.Icc 1 N).filter (fun n => k ∣ n)).card = N / k := by
  classical

  have hcard : ((Finset.Icc 1 N).filter (fun n => k ∣ n)).card =
      (Finset.Icc 1 (N / k)).card := by

    apply Finset.card_bij (fun n _ => n / k)

    · intro n hn

      obtain ⟨hrange, hdiv⟩ := Finset.mem_filter.mp hn
      obtain ⟨hnpos, hnle⟩ := Finset.mem_Icc.mp hrange

      apply Finset.mem_Icc.mpr
      exact ⟨Nat.div_pos (Nat.le_of_dvd hnpos hdiv) hk, Nat.div_le_div_right hnle⟩

    · intro m hm n hn heq

      have hmd := (Finset.mem_filter.mp hm).2

      have hnd := (Finset.mem_filter.mp hn).2

      have h := congrArg (fun q => q * k) heq
      rwa [Nat.div_mul_cancel hmd, Nat.div_mul_cancel hnd] at h

    · intro j hj

      obtain ⟨hjpos, hjle⟩ := Finset.mem_Icc.mp hj

      refine ⟨j * k, ?_, Nat.mul_div_cancel j hk⟩

      apply Finset.mem_filter.mpr
      constructor

      · apply Finset.mem_Icc.mpr
        exact ⟨mul_pos hjpos hk, (Nat.le_div_iff_mul_le hk).1 hjle⟩

      · exact ⟨j, by ring⟩

  rw [hcard, Nat.card_Icc, Nat.add_sub_cancel]

/-- Theorem: summing divisor sums counts each value once for every multiple. -/
theorem sum_divisorSum (f : ℕ → ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, divisorSum f n) =
      ∑ k ∈ Finset.Icc 1 N, f k * (N / k : ℕ) := by
  classical

  have hexpand (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      divisorSum f n = ∑ d ∈ Finset.Icc 1 N, if d ∣ n then f d else 0 := by
    obtain ⟨hnpos, hnle⟩ := Finset.mem_Icc.mp hn

    have hset : n.divisors = (Finset.Icc 1 N).filter (fun d => d ∣ n) := by
      ext d
      constructor

      · intro hd
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
            (Nat.le_of_dvd hnpos (Nat.dvd_of_mem_divisors hd)).trans hnle⟩,
            Nat.dvd_of_mem_divisors hd⟩

      · intro hd
        exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hd).2, ne_of_gt hnpos⟩

    rw [divisorSum, hset, Finset.sum_filter]

  rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk

  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    card_multiples N k (Finset.mem_Icc.mp hk).1, mul_comm]

/-- Corollary: the summatory divisor count is a sum of integer quotients. -/
theorem sum_tau (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (tau n : ℤ)) = ∑ k ∈ Finset.Icc 1 N, (N / k : ℕ) := by
  have h := sum_divisorSum (fun _ => 1) N

  simpa only [divisorSum, Finset.sum_const, nsmul_eq_mul, mul_one, one_mul, tau, Nat.cast_sum] using h

/-- Corollary: the summatory divisor sum is the weighted quotient sum. -/
theorem sum_sigma (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (sigma n : ℤ)) =
      ∑ k ∈ Finset.Icc 1 N, (k : ℤ) * (N / k : ℕ) := by
  have h := sum_divisorSum (fun k => (k : ℤ)) N

  simpa only [divisorSum, sigma, Nat.cast_sum] using h

/-- Theorem: the floor bounds and fractional-part decomposition. -/
theorem floor_spec (x : ℝ) :
    (⌊x⌋ : ℝ) ≤ x ∧ x < (⌊x⌋ : ℝ) + 1 ∧
      ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ x = ⌊x⌋ + θ := by
  have hlo := Int.floor_le x

  have hhi := Int.lt_floor_add_one x

  exact ⟨hlo, hhi, x - ⌊x⌋, by linarith, by linarith, by ring⟩

/-- Theorem: a real number equals its floor exactly when it is an integer. -/
theorem floor_eq_self_iff (x : ℝ) : (⌊x⌋ : ℝ) = x ↔ ∃ z : ℤ, x = z := by
  constructor

  · intro h
    exact ⟨⌊x⌋, h.symm⟩

  · rintro ⟨z, rfl⟩
    rw [Int.floor_intCast]

/-- Theorem: the floor of a sum differs from the sum of the floors by zero or one. -/
theorem floor_add_carry (a b : ℝ) :
    ⌊a + b⌋ - ⌊a⌋ - ⌊b⌋ = 0 ∨ ⌊a + b⌋ - ⌊a⌋ - ⌊b⌋ = 1 := by
  have ha := floor_spec a

  have hb := floor_spec b

  have hab := floor_spec (a + b)

  have hlow : (⌊a⌋ : ℝ) + ⌊b⌋ - 1 < ⌊a + b⌋ := by linarith

  have hhigh : (⌊a + b⌋ : ℝ) < ⌊a⌋ + ⌊b⌋ + 2 := by linarith

  have hlow' : ⌊a⌋ + ⌊b⌋ - 1 < ⌊a + b⌋ := by exact_mod_cast hlow

  have hhigh' : ⌊a + b⌋ < ⌊a⌋ + ⌊b⌋ + 2 := by exact_mod_cast hhigh

  omega

/-- Corollary: the floor of a sum is at least the sum of the floors. -/
theorem floor_add_ge (a b : ℝ) : ⌊a⌋ + ⌊b⌋ ≤ ⌊a + b⌋ := by
  rcases floor_add_carry a b with h | h <;> omega

/-- Theorem: natural division is the floor of the corresponding real quotient. -/
theorem floor_nat_div (N k : ℕ) (hk : 0 < k) :
    ⌊(N : ℝ) / k⌋ = ((N / k : ℕ) : ℤ) := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have heq := Nat.mod_add_div N k
  have hlt := Nat.mod_lt N hk

  apply Int.floor_eq_iff.mpr
  constructor

  · apply (le_div_iff₀ hkreal).mpr
    exact_mod_cast Nat.div_mul_le_self N k

  · apply (div_lt_iff₀ hkreal).mpr
    simp only [Int.cast_natCast]

    have hreal : (N % k : ℕ) + (k : ℝ) * (N / k : ℕ) = N := by exact_mod_cast heq
    have hrlt : ((N % k : ℕ) : ℝ) < k := by exact_mod_cast hlt
    linarith

end ElementaryNumberTheory.Chapter05
