import Textbooks.ElementaryNumberTheory.Chapter03.LinearCongruences
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace ElementaryNumberTheory.Chapter03

/-- Lemma: coprimality with each factor implies coprimality with the product. -/
theorem gcd_mul_eq_one (a b c : ℤ) (ha : Chapter01.gcd a c = 1)
    (hb : Chapter01.gcd b c = 1) (hc : c ≠ 0) : Chapter01.gcd (a * b) c = 1 := by
  obtain ⟨u, v, huv⟩ :=
    (Chapter01.gcd_eq_one_iff_exists_mul_add_mul a c (Or.inr hc)).1 ha

  obtain ⟨r, s, hrs⟩ :=
    (Chapter01.gcd_eq_one_iff_exists_mul_add_mul b c (Or.inr hc)).1 hb

  apply (Chapter01.gcd_eq_one_iff_exists_mul_add_mul (a * b) c (Or.inr hc)).2
  refine ⟨u * r, a * u * s + b * r * v + c * v * s, ?_⟩
  calc
    1 = (a * u + c * v) * (b * r + c * s) := by
      rw [← huv, ← hrs]
      ring
    _ = _ := by ring

/-- Lemma: coprimality extends to a finite product. -/
theorem gcd_prod_eq_one {ι : Type*} (s : Finset ι) (f : ι → ℤ) (c : ℤ)
    (hc : c ≠ 0) (h : ∀ i ∈ s, Chapter01.gcd (f i) c = 1) :
    Chapter01.gcd (∏ i ∈ s, f i) c = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact (Chapter01.gcd_eq_one_iff_exists_mul_add_mul 1 c (Or.inr hc)).2
      ⟨1, 0, by ring⟩

  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact gcd_mul_eq_one _ _ c (h i (Finset.mem_insert_self i s))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj))) hc

/-- Lemma: if pairwise coprime moduli divide an integer, their product divides it. -/
theorem prod_dvd_of_pairwise {ι : Type*} (s : Finset ι) (n : ι → ℤ)
    (hn : ∀ i ∈ s, n i ≠ 0)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Chapter01.gcd (n i) (n j) = 1)
    (z : ℤ) (hz : ∀ i ∈ s, n i ∣ z) : (∏ i ∈ s, n i) ∣ z := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨z, by simp only [Finset.prod_empty, one_mul]⟩

  | @insert i s hi ih =>
    have hcop := gcd_prod_eq_one s n (n i) (hn i (Finset.mem_insert_self i s))
      (fun j hj => hpair j (Finset.mem_insert_of_mem hj) i
        (Finset.mem_insert_self i s) (by
            intro heq
            subst j
            exact hi hj))

    have ht := ih (fun j hj => hn j (Finset.mem_insert_of_mem hj))
      (fun j hj k hk => hpair j (Finset.mem_insert_of_mem hj) k
        (Finset.mem_insert_of_mem hk)) (fun j hj => hz j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert hi, mul_comm]
    exact Chapter01.mul_dvd_of_coprime _ _ z hcop ht (hz i (Finset.mem_insert_self i s))

/-- Theorem: the finite Chinese remainder theorem, including the empty system. -/
theorem chinese_remainder {ι : Type*} (s : Finset ι) (n a : ι → ℤ)
    (hn : ∀ i ∈ s, n i ≠ 0)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Chapter01.gcd (n i) (n j) = 1) :
    ∃ x : ℤ, (∀ i ∈ s, x ≡ a i [ZMOD n i]) ∧
      ∀ y : ℤ, (∀ i ∈ s, y ≡ a i [ZMOD n i]) ↔ y ≡ x [ZMOD ∏ i ∈ s, n i] := by
  classical

  let N (i : ι) := ∏ j ∈ s.erase i, n j

  have hcop (i : ι) (hi : i ∈ s) : Chapter01.gcd (N i) (n i) = 1 := by
    apply gcd_prod_eq_one _ _ _ (hn i hi)
    intro j hj
    exact hpair j (Finset.mem_of_mem_erase hj) i hi (Finset.ne_of_mem_erase hj)

  have hinv (i : ι) (hi : i ∈ s) : ∃ u : ℤ, IsModularInverse (n i) (N i) u :=
    exists_modularInverse _ _ (hcop i hi)
  choose u hu using hinv

  let x := ∑ i ∈ s.attach, a i * N i * u i i.property

  have hx (i : ι) (hi : i ∈ s) : x ≡ a i [ZMOD n i] := by
    have hsum : x - a i =
        ∑ j ∈ s.attach, (a j * N j * u j j.property - if j.val = i then a i else 0) := by
      simp only [Finset.sum_sub_distrib]

      have he : (∑ j ∈ s.attach, if j.val = i then a i else 0) = a i := by
        rw [Finset.sum_eq_single ⟨i, hi⟩]

        · simp only [↓reduceIte]

        · intro j hj hji

          have hne : j.val ≠ i := by
            intro heq
            apply hji
            exact Subtype.ext heq
          simp only [hne, ↓reduceIte]

        · simp
      rw [he]

    apply (modEq_iff_dvd_sub _ _ _).2
    rw [hsum]
    apply Finset.dvd_sum
    intro j hj
    by_cases he : j.val = i

    · subst i
      simp only [↓reduceIte]

      obtain ⟨k, hk⟩ := (modEq_iff_dvd_sub _ _ _).1 (hu j.val j.property)

      exact ⟨a j * k, by nlinarith [congrArg (fun z => a j * z) hk]⟩

    · simp only [he, ↓reduceIte, sub_zero]

      have hmem : i ∈ s.erase j.val := Finset.mem_erase.mpr ⟨Ne.symm he, hi⟩

      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n hmem

      exact ⟨a j * k * u j j.property, by
          change N j = n i * k at hk
          rw [hk]
          ring⟩

  refine ⟨x, hx, ?_⟩
  intro y
  constructor

  · intro hy
    apply (modEq_iff_dvd_sub _ _ _).2
    apply prod_dvd_of_pairwise s n hn hpair
    intro i hi
    exact (modEq_iff_dvd_sub _ _ _).1 (modEq_trans (hy i hi) (modEq_symm (hx i hi)))

  · intro hy i hi

    obtain ⟨k, hk⟩ := (modEq_iff_dvd_sub _ _ _).1 hy
    obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem n hi
    apply modEq_trans _ (hx i hi)
    exact (modEq_iff_dvd_sub _ _ _).2 ⟨t * k, by
        rw [hk, ht]
        ring⟩

end ElementaryNumberTheory.Chapter03
