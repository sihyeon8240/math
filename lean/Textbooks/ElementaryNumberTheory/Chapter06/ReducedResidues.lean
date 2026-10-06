import Textbooks.ElementaryNumberTheory.Chapter06.Totient
import Mathlib.Data.ZMod.Basic

namespace ElementaryNumberTheory.Chapter06

/-- Lemma: a reduced representative is positive when the modulus exceeds one. -/
theorem reducedResidue_bounds (n a : ℕ) (hn : 1 < n) (ha : a ∈ reducedResidues n) :
    0 < a ∧ a < n := by
  obtain ⟨hlt, hc⟩ := Finset.mem_filter.mp ha
  have hlt' := Finset.mem_range.mp hlt
  have hpos : a ≠ 0 := by
    intro h
    subst a
    simp only [Nat.coprime_zero_right] at hc
    omega
  exact ⟨Nat.pos_of_ne_zero hpos, hlt'⟩

/-- Lemma: reflection in n/2 permutes the reduced representatives. -/
theorem reducedResidue_reflection (n a : ℕ) (hn : 1 < n)
    (ha : a ∈ reducedResidues n) : n - a ∈ reducedResidues n := by
  obtain ⟨hpos, hlt⟩ := reducedResidue_bounds n a hn ha
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
  have hlocal : Chapter01.gcd n (n - a : ℕ) = Chapter01.gcd n a := by
    rw [Nat.cast_sub (le_of_lt hlt)]
    apply Chapter01.gcd_eq_of_common_divisors
    intro d
    constructor

    · rintro ⟨hdn, hda⟩
      have h := dvd_sub hdn hda
      rw [sub_sub_cancel] at h
      exact ⟨hdn, h⟩

    · rintro ⟨hdn, hda⟩
      exact ⟨hdn, dvd_sub hdn hda⟩

  apply (coprime_iff_gcd_eq_one n (n - a) (by omega)).2
  rw [hlocal]
  exact (coprime_iff_gcd_eq_one n a (by omega)).1 (Finset.mem_filter.mp ha).2

/-- Lemma: reflection has no fixed reduced representative when n exceeds two. -/
theorem reducedResidue_reflection_ne (n a : ℕ) (hn : 2 < n)
    (ha : a ∈ reducedResidues n) : n - a ≠ a := by
  obtain ⟨hpos, hlt⟩ := reducedResidue_bounds n a (by omega) ha
  intro he
  have hn' : n = a * 2 := by omega
  have hc := (coprime_iff_gcd_eq_one n a (by omega)).1 (Finset.mem_filter.mp ha).2
  have hd := (Chapter01.gcd_spec n a (Or.inl (by omega))).2.2.2.2 a
    (Int.natCast_dvd_natCast.mpr ⟨2, hn'⟩) (dvd_refl _)
  rw [hc, Nat.cast_one] at hd
  have := Nat.eq_one_of_dvd_one (Int.natCast_dvd_natCast.mp hd)
  omega

/-- Theorem: phi is even for every modulus greater than two. -/
theorem totient_even (n : ℕ) (hn : 2 < n) : Even (Nat.totient n) := by
  have hsum : (∑ a ∈ reducedResidues n, (1 : ZMod 2)) = 0 := by
    apply Finset.sum_involution (fun a _ => n - a)
    · intro a ha
      decide
    · intro a ha hne
      exact reducedResidue_reflection_ne n a hn ha
    · intro a ha
      exact reducedResidue_reflection n a (by omega) ha
    · intro a ha
      have := (reducedResidue_bounds n a (by omega) ha).2
      omega

  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  apply even_iff_two_dvd.mpr
  exact (ZMod.natCast_eq_zero_iff _ _).1 hsum

/-- Theorem: twice the sum of the reduced representatives is n times phi(n). -/
theorem sum_reducedResidues (n : ℕ) (hn : 1 < n) :
    2 * (∑ a ∈ reducedResidues n, a) = n * Nat.totient n := by
  have hsum : (∑ a ∈ reducedResidues n, a) = ∑ a ∈ reducedResidues n, (n - a) := by
    apply Finset.sum_bij (fun a _ => n - a)
    · intro a ha
      exact reducedResidue_reflection n a hn ha
    · intro a ha b hb he
      have := (reducedResidue_bounds n a hn ha).2
      have := (reducedResidue_bounds n b hn hb).2
      omega
    · intro b hb
      refine ⟨n - b, reducedResidue_reflection n b hn hb, ?_⟩
      have := (reducedResidue_bounds n b hn hb).2
      omega
    · intro a ha
      have := (reducedResidue_bounds n a hn ha).2
      omega

  have hadd : (∑ a ∈ reducedResidues n, a) + (∑ a ∈ reducedResidues n, (n - a)) =
      n * Nat.totient n := by
    rw [← Finset.sum_add_distrib]
    have hterm : ∀ a ∈ reducedResidues n, a + (n - a) = n := by
      intro a ha
      have := (reducedResidue_bounds n a hn ha).2
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_comm]
    rfl

  omega

/-- Theorem: among moduli greater than one, maximal phi characterizes primes. -/
theorem totient_eq_sub_one_iff (n : ℕ) (hn : 1 < n) :
    Nat.totient n = n - 1 ↔ Chapter02.isPrime n := by
  constructor

  · intro h
    have hsubset : reducedResidues n ⊆ Finset.Ico 1 n := by
      intro a ha
      exact Finset.mem_Ico.mpr (reducedResidue_bounds n a hn ha)
    have hset : reducedResidues n = Finset.Ico 1 n := by
      apply Finset.eq_of_subset_of_card_le hsubset
      change (Finset.Ico 1 n).card ≤ Nat.totient n
      rw [Nat.card_Ico, h]

    refine ⟨hn, ?_⟩
    intro d hd
    by_cases he : d = n
    · exact Or.inr he
    · have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
      have hdlt : d < n := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hd) he
      have hc := (Finset.mem_filter.mp (hset.symm ▸ Finset.mem_Ico.mpr ⟨hdpos, hdlt⟩)).2
      have hcop := (coprime_iff_gcd_eq_one n d (by omega)).1 hc
      have hdiv := (Chapter01.gcd_spec n d (Or.inl (by omega))).2.2.2.2 d
        (Int.natCast_dvd_natCast.mpr hd) (dvd_refl _)
      rw [hcop, Nat.cast_one] at hdiv
      exact Or.inl (Nat.eq_one_of_dvd_one (Int.natCast_dvd_natCast.mp hdiv))

  · exact totient_prime n

end ElementaryNumberTheory.Chapter06
