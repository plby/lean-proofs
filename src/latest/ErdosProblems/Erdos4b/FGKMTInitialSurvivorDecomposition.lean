/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTInitialResidueSieve
import ErdosProblems.Erdos4b.FGKMTPinnedPrimeExpansion

/-! # Every nonsmooth initial survivor is a prime -/

namespace Erdos4b.FGKMT

noncomputable section

theorem initialResidueSurvivor_smooth_or_prime {x Y V Z n : ℕ} {r : ℕ → ℕ}
    (hVx : V ≤ x) (hY : Y ≤ (x / 2) * V) (hn : n ∈ initialResidueSurvivors x Y r)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ V → r p = 0)
    (hmedium : ∀ p : ℕ, p.Prime → Z < p → p ≤ x / 2 → r p = 0) :
    n ∈ Nat.smoothNumbersUpTo Y (Z + 1) ∨ n.Prime := by
  have hndata := (mem_initialResidueSurvivors x Y r n).mp hn
  by_cases hsmooth : n ∈ Nat.smoothNumbers (Z + 1)
  · exact Or.inl (Nat.mem_smoothNumbersUpTo.mpr ⟨hndata.2.1, hsmooth⟩)
  · right
    rw [Nat.mem_smoothNumbers'] at hsmooth
    push Not at hsmooth
    obtain ⟨p, hp, hpn, hpZ⟩ := hsmooth
    have hpbig : x / 2 < p := by
      by_contra hnot
      have hphalf : p ≤ x / 2 := Nat.le_of_not_gt hnot
      exact initialResidueSurvivors_not_dvd hn hp (hphalf.trans (Nat.div_le_self x 2))
        (hmedium p hp (by omega) hphalf) hpn
    obtain ⟨t, ht⟩ := hpn
    have htpos : 0 < t := by
      by_contra hnot
      have htzero : t = 0 := by omega
      simp only [htzero, mul_zero] at ht
      omega
    have htone : t = 1 := by
      by_contra hnot
      obtain ⟨q, hq, hqt⟩ := Nat.exists_prime_and_dvd hnot
      have hqn : q ∣ n := by rw [ht]; exact dvd_mul_of_dvd_right hqt p
      have hqbig : V < q := by
        by_contra hnot
        have hqV : q ≤ V := Nat.le_of_not_gt hnot
        exact initialResidueSurvivors_not_dvd hn hq (hqV.trans hVx) (hsmall q hq hqV) hqn
      have htle := Nat.le_of_dvd htpos hqt
      have hproduct := Nat.mul_le_mul (Nat.succ_le_of_lt hpbig)
        (Nat.succ_le_of_lt (hqbig.trans_le htle))
      nlinarith [hndata.2.1]
    rw [ht, htone, mul_one]
    exact hp

theorem commonPinnedPrimeSet_disjoint_of_le {A B C D : ℕ} (hBC : B ≤ C) :
    Disjoint (commonPinnedPrimeSet A B) (commonPinnedPrimeSet C D) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hpB := (mem_commonPinnedPrimeSet.mp hp).2.1
  have hCp := (mem_commonPinnedPrimeSet.mp hq).1
  omega

theorem initialResidueSurvivors_subset_smooth_union_prime {x Y V Z : ℕ}
    (hVZ : V ≤ Z) (hZx : Z ≤ x / 2) (hY : Y ≤ (x / 2) * V)
    (b : ResidueAssignment (commonPinnedPrimeSet V Z))
    (r : ResidueAssignment (commonPinnedPrimeSet (x / 2) x)) :
    initialResidueSurvivors x Y
        (zeroExtendedResidue (commonPinnedPrimeSet V Z) (commonPinnedPrimeSet (x / 2) x) b r) ⊆
      Nat.smoothNumbersUpTo Y (Z + 1) ∪
        naturalResidueSurvivors (commonPinnedPrimeSet (x / 2) x)
          (naturalResidueSurvivors (commonPinnedPrimeSet V Z) (commonPinnedPrimeSet x Y) b) r := by
  intro n hn
  let ρ := zeroExtendedResidue (commonPinnedPrimeSet V Z) (commonPinnedPrimeSet (x / 2) x) b r
  have hVx := hVZ.trans (hZx.trans (Nat.div_le_self x 2))
  have hsmall (p : ℕ) (_hp : p.Prime) (hpV : p ≤ V) : ρ p = 0 := by
    apply zeroExtendedResidue_zero
    · intro h
      have hlt := (mem_commonPinnedPrimeSet.mp h).1
      omega
    · intro h
      have hlt := (mem_commonPinnedPrimeSet.mp h).1
      omega
  have hmedium (p : ℕ) (_hp : p.Prime) (hZp : Z < p) (hpx : p ≤ x / 2) : ρ p = 0 := by
    apply zeroExtendedResidue_zero
    · intro h
      have hle := (mem_commonPinnedPrimeSet.mp h).2.1
      omega
    · intro h
      have hlt := (mem_commonPinnedPrimeSet.mp h).1
      omega
  rcases initialResidueSurvivor_smooth_or_prime hVx hY hn hsmall hmedium with hsm | hprime
  · exact Finset.mem_union_left _ hsm
  · apply Finset.mem_union_right
    apply (mem_naturalResidueSurvivors _ _ r n).mpr
    refine ⟨?_, initialResidueSurvivors_avoids hn _ r ?_ ?_⟩
    · apply (mem_naturalResidueSurvivors _ _ b n).mpr
      have hnd := (mem_initialResidueSurvivors x Y ρ n).mp hn
      refine ⟨mem_commonPinnedPrimeSet.mpr ⟨hnd.1, hnd.2.1, hprime⟩,
        initialResidueSurvivors_avoids hn _ b ?_ ?_⟩
      · intro p hp
        have hh := mem_commonPinnedPrimeSet.mp hp
        exact ⟨hh.2.2, hh.2.1.trans (hZx.trans (Nat.div_le_self x 2))⟩
      · exact zeroExtendedResidue_small _ _ b r
    · intro p hp
      have hh := mem_commonPinnedPrimeSet.mp hp
      exact ⟨hh.2.2, hh.2.1⟩
    · exact zeroExtendedResidue_large _ _ b r (commonPinnedPrimeSet_disjoint_of_le hZx)

end

end Erdos4b.FGKMT
