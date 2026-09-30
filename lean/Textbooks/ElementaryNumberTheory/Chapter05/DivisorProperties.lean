import Textbooks.ElementaryNumberTheory.Chapter05.DivisorFormulas

namespace ElementaryNumberTheory.Chapter05

/-- Theorem: primality is equivalent to having exactly two positive divisors. -/
theorem tau_eq_two_iff (n : ℕ) (hn : 1 < n) : tau n = 2 ↔ Chapter02.isPrime n := by
  have hnpos : 0 < n := by omega

  have hnne : n ≠ 0 := ne_of_gt hnpos

  have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with he | he

    · rw [he]
      exact Nat.one_mem_divisors.mpr (ne_of_gt hnpos)

    · rw [he]
      exact Nat.mem_divisors_self n (ne_of_gt hnpos)

  have hcard : ({1, n} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    simpa only [Finset.mem_singleton] using (by omega : (1 : ℕ) ≠ n)

  constructor

  · intro ht

    have heq : n.divisors = {1, n} :=
      (Finset.eq_of_subset_of_card_le hsub (by
          change tau n ≤ _
          rw [ht, hcard])).symm

    refine ⟨hn, ?_⟩
    intro d hd

    have hmem := Nat.mem_divisors.mpr ⟨hd, ne_of_gt hnpos⟩
    rw [heq, Finset.mem_insert, Finset.mem_singleton] at hmem
    exact hmem

  · intro hp

    have heq : n.divisors = {1, n} := by
      apply Finset.Subset.antisymm _ hsub
      intro d hd
      exact Finset.mem_insert.mpr ((hp.2 d (Nat.dvd_of_mem_divisors hd)).imp_right
        Finset.mem_singleton.mpr)

    rw [tau, heq, hcard]

/-- Theorem: a positive integer greater than one is prime exactly when its divisor sum is n+1. -/
theorem sigma_eq_succ_iff (n : ℕ) (hn : 1 < n) : sigma n = n + 1 ↔ Chapter02.isPrime n := by
  have hnpos : 0 < n := by omega

  have hnne : n ≠ 0 := ne_of_gt hnpos

  constructor

  · intro hs
    refine ⟨hn, ?_⟩
    intro d hd
    by_cases hd1 : d = 1

    · exact Or.inl hd1

    · by_cases hdn : d = n

      · exact Or.inr hdn

      · have hmem := Nat.mem_divisors.mpr ⟨hd, ne_of_gt hnpos⟩

        have hdpos := Nat.pos_of_mem_divisors hmem

        have hsub : ({d, 1, n} : Finset ℕ) ⊆ n.divisors := by
          intro k hk
          simp only [Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with he | he | he

          · rwa [he]

          · rw [he]
            exact Nat.one_mem_divisors.mpr (ne_of_gt hnpos)

          · rw [he]
            exact Nat.mem_divisors_self n (ne_of_gt hnpos)

        have hle := Finset.sum_le_sum_of_subset hsub (f := fun k => k)
        rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton,
          hd1, hdn, or_self, not_false_eq_true]),
          Finset.sum_insert (by simpa only [Finset.mem_singleton] using
            (by omega : (1 : ℕ) ≠ n)), Finset.sum_singleton] at hle
        change d + (1 + n) ≤ sigma n at hle
        omega

  · intro hp

    have heq : n.divisors = {1, n} := by
      ext d
      constructor

      · intro hd
        exact Finset.mem_insert.mpr ((hp.2 d (Nat.dvd_of_mem_divisors hd)).imp_right
          Finset.mem_singleton.mpr)

      · intro hd
        rcases Finset.mem_insert.mp hd with he | he

        · rw [he]
          exact Nat.one_mem_divisors.mpr hnne

        · rw [Finset.mem_singleton.mp he]
          exact Nat.mem_divisors_self n hnne

    rw [sigma, heq, Finset.sum_insert (by simpa only [Finset.mem_singleton] using
      (by omega : (1 : ℕ) ≠ n)), Finset.sum_singleton]
    omega

/-- Theorem: pairing complementary divisors gives the square of their product. -/
theorem prod_divisors_sq (n : ℕ) (hn : 0 < n) :
    (∏ d ∈ n.divisors, d) ^ 2 = n ^ tau n := by
  have hperm : (∏ d ∈ n.divisors, n / d) = ∏ d ∈ n.divisors, d := by
    apply Finset.prod_bij (fun d _ => n / d)

    · intro d hd
      exact Nat.mem_divisors.mpr
        ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), ne_of_gt hn⟩

    · intro d hd e he hde

      have h := congrArg (fun k => n / k) hde
      rwa [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) (ne_of_gt hn),
        Nat.div_div_self (Nat.dvd_of_mem_divisors he) (ne_of_gt hn)] at h

    · intro d hd
      refine ⟨n / d, Nat.mem_divisors.mpr
        ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), ne_of_gt hn⟩, ?_⟩

      exact Nat.div_div_self (Nat.dvd_of_mem_divisors hd) (ne_of_gt hn)

    · intro d hd
      rfl

  rw [pow_two]
  nth_rw 2 [← hperm]
  rw [← Finset.prod_mul_distrib]

  have hterm : ∀ d ∈ n.divisors, d * (n / d) = n := by
    intro d hd
    exact Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)

  rw [Finset.prod_congr rfl hterm, Finset.prod_const]
  rfl

end ElementaryNumberTheory.Chapter05
