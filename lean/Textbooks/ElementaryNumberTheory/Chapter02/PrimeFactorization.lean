import Textbooks.ElementaryNumberTheory.Chapter02.Primes
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finsupp.Multiset

namespace ElementaryNumberTheory.Chapter02

/-- Lemma: every positive natural number has a list of prime factors;
the empty list represents one. -/
theorem exists_prime_factors (n : ℕ) (hn : 0 < n) :
    ∃ l : List ℕ, (∀ p ∈ l, isPrime p) ∧ l.prod = n := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hone : n = 1

    · exact ⟨[], by simp, by simpa using hone.symm⟩

    · have hgt : 1 < n := by omega
      by_cases hp : isPrime n

      · exact ⟨[n], by simpa, by simp⟩

      · have hdiv : ∃ d : ℕ, d ∣ n ∧ d ≠ 1 ∧ d ≠ n := by
          simpa only [isPrime, hgt, true_and, not_forall, not_or, exists_prop] using hp

        obtain ⟨d, ⟨k, hk⟩, hd1, hdn⟩ := hdiv
        have hdpos : 0 < d := by nlinarith
        have hkpos : 0 < k := by nlinarith
        have hdlt : d < n := by
          by_contra h
          have hk1 : k = 1 := by nlinarith
          simp [hk1] at hk
          exact hdn hk.symm

        have hklt : k < n := by
          have hd2 : 2 ≤ d := by omega
          nlinarith

        obtain ⟨l, hl, heql⟩ := ih d hdlt hdpos
        obtain ⟨m, hm, heqm⟩ := ih k hklt hkpos
        refine ⟨l ++ m, ?_, ?_⟩

        · intro p hp
          rcases List.mem_append.mp hp with hpl | hpm

          · exact hl p hpl
          · exact hm p hpm

        · rw [List.prod_append, heql, heqm, ← hk]

/-- Lemma: equal products of prime lists have the same factors with multiplicity. -/
theorem prime_factors_perm (l m : List ℕ) (hl : ∀ p ∈ l, isPrime p)
    (hm : ∀ p ∈ m, isPrime p) (hprod : l.prod = m.prod) : l.Perm m := by
  classical
  induction l generalizing m with
  | nil =>
    cases m with
    | nil => exact List.Perm.refl []
    | cons q m =>
      have hq := (hm q List.mem_cons_self).1
      change 1 = q * m.prod at hprod
      have hmpos : 0 < m.prod := by nlinarith
      nlinarith

  | cons p l ih =>
    have hp := hl p List.mem_cons_self
    have hpm : p ∈ m := by
      apply prime_eq_of_dvd_prod p hp m hm
      exact ⟨l.prod, hprod.symm⟩

    have hperm : m.Perm (p :: m.erase p) := List.perm_cons_erase hpm
    have htail : l.prod = (m.erase p).prod := by
      have heq := hperm.prod_eq
      simp only [List.prod_cons] at hprod heq
      exact Nat.eq_of_mul_eq_mul_left hp.1.le (hprod.trans heq)

    have htailperm : l.Perm (m.erase p) := ih (m.erase p)
      (fun q hq => hl q (List.mem_cons_of_mem p hq))
      (fun q hq => hm q (List.mem_of_mem_erase hq)) htail

    exact (List.Perm.cons p htailperm).trans hperm.symm

/-- Theorem: every integer greater than one is a nonempty product of primes,
unique up to permutation. A one-element list is the prime case. -/
theorem fundamental_theorem_of_arithmetic (n : ℕ) (hn : 1 < n) :
    ∃ l : List ℕ, l ≠ [] ∧ (∀ p ∈ l, isPrime p) ∧ l.prod = n ∧
      ∀ m : List ℕ, (∀ p ∈ m, isPrime p) → m.prod = n → m.Perm l := by
  obtain ⟨l, hl, hprod⟩ := exists_prime_factors n (by omega)
  refine ⟨l, ?_, hl, hprod, ?_⟩

  · intro heq
    subst l
    simp only [List.prod_nil] at hprod
    omega

  · intro m hm hmn
    exact prime_factors_perm m l hm hl (hmn.trans hprod.symm)

/-- Lemma: collecting equal factors gives a unique finitely supported exponent map. -/
theorem existsUnique_prime_exponents (n : ℕ) (hn : 0 < n) :
    ∃! e : ℕ →₀ ℕ, (∀ p ∈ e.support, isPrime p) ∧
      e.prod (fun p k => p ^ k) = n := by
  classical
  obtain ⟨l, hl, hprod⟩ := exists_prime_factors n hn
  let e := (l : Multiset ℕ).toFinsupp
  have he : (∀ p ∈ e.support, isPrime p) ∧ e.prod (fun p k => p ^ k) = n := by
    constructor

    · intro p hp
      exact hl p (by simpa [e] using hp)

    · rw [← Finsupp.prod_toMultiset, Multiset.toFinsupp_toMultiset]
      exact hprod

  refine ⟨e, he, ?_⟩
  rintro f ⟨hf, hfn⟩
  let m := f.toMultiset.toList
  have hm : ∀ p ∈ m, isPrime p := by
    intro p hp
    exact hf p (by simpa [m] using hp)

  have hmprod : m.prod = n := by
    rw [Multiset.prod_toList, Finsupp.prod_toMultiset]
    exact hfn

  have hperm := prime_factors_perm m l hm hl (hmprod.trans hprod.symm)
  have hmulti : f.toMultiset = (l : Multiset ℕ) := by
    simpa [m] using Multiset.coe_eq_coe.mpr hperm

  have heq := congrArg Multiset.toFinsupp hmulti
  simpa [e] using heq

/-- Definition: a canonical factorization lists the prime support in strictly
increasing order and records each multiplicity in a finitely supported map. -/
def isCanonicalFactorization (n : ℕ) (r : List ℕ × (ℕ →₀ ℕ)) : Prop :=
  r.1.Pairwise (· < ·) ∧ r.1.toFinset = r.2.support ∧
    (∀ p ∈ r.2.support, isPrime p) ∧ r.2.prod (fun p k => p ^ k) = n

/-- Corollary: every integer greater than one has a unique canonical factorization. -/
theorem existsUnique_canonical_factorization (n : ℕ) (hn : 1 < n) :
    ∃! r : List ℕ × (ℕ →₀ ℕ), isCanonicalFactorization n r := by
  classical
  obtain ⟨e, he, huniq⟩ := existsUnique_prime_exponents n (by omega)
  let l := e.support.sort (· ≤ ·)
  have hl : l.Pairwise (· < ·) :=
    List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort e.support)

  refine ⟨(l, e), ⟨hl, Finset.sort_toFinset _ _, he⟩, ?_⟩
  rintro ⟨m, f⟩ ⟨hm, hsupport, hf⟩
  have hfe : f = e := huniq f hf
  subst f

  have hsorted : e.support.sort (· ≤ ·) = m := by
    rw [← hsupport]
    exact (List.toFinset_sort (· ≤ ·) hm.nodup).mpr
      (hm.imp (fun h => Nat.le_of_lt h))

  exact Prod.ext hsorted.symm rfl

/-- Corollary: the canonical representation has nonempty increasing prime bases,
positive exponents, and the displayed product of prime powers. -/
theorem canonical_factorization_spec (n : ℕ) (hn : 1 < n)
    (r : List ℕ × (ℕ →₀ ℕ)) (hr : isCanonicalFactorization n r) :
    r.1 ≠ [] ∧ r.1.Pairwise (· < ·) ∧
      (∀ p ∈ r.1, isPrime p ∧ 0 < r.2 p) ∧
      (r.1.map (fun p => p ^ r.2 p)).prod = n := by
  obtain ⟨hsorted, hsupport, hprime, hprod⟩ := hr
  have hproduct : (r.1.map (fun p => p ^ r.2 p)).prod = n := by
    rw [← List.prod_toFinset _ hsorted.nodup, hsupport]
    exact hprod

  refine ⟨?_, hsorted, ?_, hproduct⟩

  · intro hnil
    rw [hnil] at hproduct
    simp only [List.map_nil, List.prod_nil] at hproduct
    omega

  · intro p hp
    have hmem : p ∈ r.2.support := by
      rw [← hsupport]
      exact List.mem_toFinset.mpr hp

    exact ⟨hprime p hmem, Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hmem)⟩

end ElementaryNumberTheory.Chapter02
