import Textbooks.ElementaryNumberTheory.Chapter04.Fermat
import Mathlib.Algebra.BigOperators.Intervals

namespace ElementaryNumberTheory.Chapter04

/-- Lemma: inverse pairs cancel in the product of the nonzero residues. The only possible fixed
points are one and minus one. -/
private theorem prod_units_eq_neg_one (p : ℕ) [Fact p.Prime] :
    (∏ u : (ZMod p)ˣ, (u : ZMod p)) = -1 := by
  classical

  let s : Finset (ZMod p)ˣ := Finset.univ.erase (-1)

  have hs : (∏ u ∈ s, (u : ZMod p)) = 1 := by
    refine Finset.prod_involution (fun u _ => u⁻¹) ?_ ?_ ?_ ?_

    · intro u hu
      exact show (u : ZMod p) * ((u⁻¹ : (ZMod p)ˣ) : ZMod p) = 1 from
        congrArg (fun v : (ZMod p)ˣ => (v : ZMod p)) (mul_inv_cancel u)

    · intro u hu hne heq

      have he : (u : ZMod p) * (u : ZMod p) = 1 := by
        simpa only [heq] using show (u : ZMod p) * ((u⁻¹ : (ZMod p)ˣ) : ZMod p) = 1 from
        congrArg (fun v : (ZMod p)ˣ => (v : ZMod p)) (mul_inv_cancel u)
      rcases mul_self_eq_one_iff.mp he with hone | hneg

      · exact hne hone

      · have hu' := (Finset.mem_erase.mp hu).1
        exact hu' (Units.ext hneg)

    · intro u hu
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_univ _⟩
      intro heq

      have hu' := (Finset.mem_erase.mp hu).1
      apply hu'

      have hh := congrArg Inv.inv heq
      simpa only [inv_inv, inv_neg, inv_one] using hh

    · intro u hu
      exact inv_inv u

  have h := Finset.mul_prod_erase Finset.univ (fun u : (ZMod p)ˣ => (u : ZMod p))
    (Finset.mem_univ (-1))
  change (-1 : ZMod p) * (∏ u ∈ s, (u : ZMod p)) = _ at h
  rw [hs, mul_one] at h
  exact h.symm

/-- Theorem: Wilson's factorial congruence. -/
theorem wilson (p : ℕ) (hp : Chapter02.isPrime p) :
    ((p - 1).factorial : ℤ) ≡ -1 [ZMOD (p : ℤ)] := by
  classical

  have : Fact p.Prime := ⟨Nat.prime_def.mpr hp⟩

  have hpos : 0 < p := by
    have := hp.1
    omega

  have hprod : (∏ u : (ZMod p)ˣ, (u : ZMod p)) =
      ∏ k ∈ Finset.Ico 1 p, (k : ZMod p) := by

    apply Finset.prod_bij (fun (u : (ZMod p)ˣ) _ => (u : ZMod p).val)

    · intro u hu
      apply Finset.mem_Ico.mpr
      refine ⟨?_, ZMod.val_lt _⟩

      have hne : (u : ZMod p).val ≠ 0 := by
        intro hz
        apply Units.ne_zero u
        apply ZMod.val_injective p
        simpa only [ZMod.val_zero] using hz
      omega

    · intro u hu v hv h
      exact Units.ext (ZMod.val_injective p h)

    · intro k hk

      have hk' := Finset.mem_Ico.mp hk

      have hne : (k : ZMod p) ≠ 0 := by
        intro hz

        have hh := congrArg ZMod.val hz
        rw [ZMod.val_natCast_of_lt hk'.2, ZMod.val_zero] at hh
        omega

      exact ⟨Units.mk0 (k : ZMod p) hne, Finset.mem_univ _,
        ZMod.val_natCast_of_lt hk'.2⟩

    · intro u hu
      exact (ZMod.natCast_zmod_val _).symm

  have hf : (∏ k ∈ Finset.Ico 1 p, (k : ZMod p)) = ((p - 1).factorial : ZMod p) := by
    rw [← Nat.cast_prod, ← Finset.prod_Ico_id_eq_factorial]
    rw [Nat.sub_add_cancel hpos]

  apply (ZMod.intCast_eq_intCast_iff _ _ p).1
  simpa only [Int.cast_natCast, Int.cast_neg, Int.cast_one] using
    (hf.symm.trans (hprod.symm.trans (prod_units_eq_neg_one p)))

/-- Lemma: each positive integer at most n divides n!, by the product recursion. -/
private theorem dvd_factorial (d n : ℕ) (hd : 0 < d) (hle : d ≤ n) :
    d ∣ n.factorial := by
  induction n with
  | zero => omega

  | succ n ih =>
    rw [Nat.factorial_succ]
    by_cases he : d = n + 1

    · exact ⟨n.factorial, by rw [he]⟩

    · obtain ⟨k, hk⟩ := ih (by omega)
      exact ⟨(n + 1) * k, by
          rw [hk]
          ring⟩

/-- Theorem: Wilson's congruence implies primality. -/
theorem prime_of_wilson (n : ℕ) (hn : 1 < n)
    (h : ((n - 1).factorial : ℤ) ≡ -1 [ZMOD (n : ℤ)]) : Chapter02.isPrime n := by

  refine ⟨hn, ?_⟩
  intro d hd
  by_cases he : d = n

  · exact Or.inr he

  · have hdpos : 0 < d := by
      obtain ⟨k, hk⟩ := hd
      by_contra hh

      have hz : d = 0 := by
        omega
      rw [hz, zero_mul] at hk
      omega

    have hdle : d ≤ n := by
      obtain ⟨k, hk⟩ := hd

      have hkpos : 0 < k := by
        nlinarith
      nlinarith

    have hdf : (d : ℤ) ∣ (n - 1).factorial :=
      Int.natCast_dvd_natCast.mpr (dvd_factorial d (n - 1) hdpos (by omega))

    obtain ⟨u, hu⟩ := hdf
    obtain ⟨v, hv⟩ := Int.natCast_dvd_natCast.mpr hd
    obtain ⟨k, hk⟩ := (Chapter03.modEq_iff_dvd_sub _ _ _).1 h

    have hone : (1 : ℤ) = d * (v * k - u) := by
      rw [hu, hv] at hk
      nlinarith

    have hdz : (0 : ℤ) < d := by
      exact_mod_cast hdpos

    have hkp : 0 < v * k - u := by
      nlinarith
    left

    have : (d : ℤ) = 1 := by
      nlinarith
    exact_mod_cast this

/-- Corollary: Wilson's congruence is an exact primality criterion. -/
theorem prime_iff_wilson (n : ℕ) (hn : 1 < n) :
    Chapter02.isPrime n ↔ ((n - 1).factorial : ℤ) ≡ -1 [ZMOD (n : ℤ)] :=
  ⟨wilson n, prime_of_wilson n hn⟩

end ElementaryNumberTheory.Chapter04
