import Textbooks.ElementaryNumberTheory.Chapter05.Divisors
import Mathlib.Data.Finsupp.Order
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

namespace ElementaryNumberTheory.Chapter05

/-- Definition: the value of a finitely supported prime-exponent vector. -/
def factorValue (e : ℕ →₀ ℕ) : ℕ := e.prod (fun p k => p ^ k)

/-- Definition: the prime multiplicities selected from the independently proved unique
factorization theorem; zero is assigned the zero exponent vector. -/
noncomputable def primeExponents (n : ℕ) : ℕ →₀ ℕ :=
  if hn : 0 < n then (Chapter02.existsUnique_prime_exponents n hn).exists.choose else 0

/-- Theorem: the selected exponents are supported on primes and reconstruct n. -/
theorem primeExponents_spec (n : ℕ) (hn : 0 < n) :
    (∀ p ∈ (primeExponents n).support, Chapter02.isPrime p) ∧
      factorValue (primeExponents n) = n := by
  unfold primeExponents
  rw [dite_eq_left hn]
  exact (Chapter02.existsUnique_prime_exponents n hn).exists.choose_spec

/-- Lemma: any prime-supported exponent vector is the selected one for its value. -/
theorem primeExponents_unique (n : ℕ) (hn : 0 < n) (e : ℕ →₀ ℕ)
    (hp : ∀ p ∈ e.support, Chapter02.isPrime p) (he : factorValue e = n) :
    e = primeExponents n := by

  exact (Chapter02.existsUnique_prime_exponents n hn).unique ⟨hp, he⟩
    (primeExponents_spec n hn)

/-- Lemma: exponent-vector addition corresponds to multiplication. -/
theorem factorValue_add (e f : ℕ →₀ ℕ) : factorValue (e + f) = factorValue e * factorValue f := by
  exact Finsupp.prod_add_index' (fun p => pow_zero p) (fun p i j => pow_add p i j)

/-- Lemma: prime-supported exponent vectors have positive value. -/
theorem factorValue_pos (e : ℕ →₀ ℕ) (hp : ∀ p ∈ e.support, Chapter02.isPrime p) :
    0 < factorValue e := by

  apply Finset.prod_pos
  intro p hps
  exact pow_pos (by
      have := (hp p hps).1
      omega) _

/-- Theorem: multiplication adds the prime multiplicities. -/
theorem primeExponents_mul (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    primeExponents (m * n) = primeExponents m + primeExponents n := by
  symm
  apply primeExponents_unique (m * n) (mul_pos hm hn)

  · intro p hp
    rcases Finset.mem_union.mp (Finsupp.support_add hp) with hpm | hpn

    · exact (primeExponents_spec m hm).1 p hpm

    · exact (primeExponents_spec n hn).1 p hpn

  · rw [factorValue_add, (primeExponents_spec m hm).2, (primeExponents_spec n hn).2]

/-- Theorem: divisibility of positive integers is coordinatewise comparison of prime exponents.
This is the exponent description of all divisors. -/
theorem dvd_iff_primeExponents_le (d n : ℕ) (hd : 0 < d) (hn : 0 < n) :
    d ∣ n ↔ primeExponents d ≤ primeExponents n := by

  constructor

  · rintro ⟨k, hk⟩

    have hkpos : 0 < k := by
      nlinarith
    rw [hk, primeExponents_mul d k hd hkpos]
    exact le_add_right le_rfl

  · intro hle

    have hsum : primeExponents d + (primeExponents n - primeExponents d) =
        primeExponents n := add_tsub_cancel_of_le hle

    refine ⟨factorValue (primeExponents n - primeExponents d), ?_⟩

    have hh := congrArg factorValue hsum
    rw [factorValue_add, (primeExponents_spec d hd).2, (primeExponents_spec n hn).2] at hh
    exact hh.symm

/-- Theorem: exponent choices below those of n correspond uniquely to its divisors. -/
theorem divisor_exponents (n : ℕ) (hn : 0 < n) (e : ℕ →₀ ℕ)
    (he : e ≤ primeExponents n) :
    0 < factorValue e ∧ factorValue e ∣ n ∧ primeExponents (factorValue e) = e := by
  have hp : ∀ p ∈ e.support, Chapter02.isPrime p := by
    intro p hps
    apply (primeExponents_spec n hn).1
    apply Finsupp.mem_support_iff.mpr

    have hpos : 0 < e p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hps)

    have hle := he p
    omega

  have hpos := factorValue_pos e hp

  have heq := (primeExponents_unique (factorValue e) hpos e hp rfl).symm

  exact ⟨hpos, (dvd_iff_primeExponents_le _ n hpos hn).2 (by
      rw [heq]
      exact he), heq⟩

/-- Theorem: the integer one has no prime factors. -/
theorem primeExponents_one : primeExponents 1 = 0 := by
  symm
  apply primeExponents_unique 1 (by decide) 0

  · intro p hp
    simp only [Finsupp.support_zero, Finset.notMem_empty] at hp

  · simp only [factorValue, Finsupp.prod_zero_index]

/-- Theorem: a prime power has exactly its indicated prime exponent. -/
theorem primeExponents_prime_pow (p k : ℕ) (hp : Chapter02.isPrime p) :
    primeExponents (p ^ k) = Finsupp.single p k := by
  have hpos : 0 < p ^ k := pow_pos (by
      have := hp.1
      omega) _
  symm
  apply primeExponents_unique _ hpos

  · intro q hq

    have hh : q = p := Finset.mem_singleton.mp (Finsupp.support_single_subset hq)
    rwa [hh]

  · exact Finsupp.prod_single_index (pow_zero p)

end ElementaryNumberTheory.Chapter05
