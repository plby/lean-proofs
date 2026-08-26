/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.SingularIntervals
import ErdosProblems.Erdos822.DeterminantChargeFubini

/-! # Relating the remaining singular primes to the proved first moment -/

namespace Erdos822

open scoped BigOperators Classical

theorem goodDeterminantPrimes_subset_admissible {N k r q m' h z U : ℕ}
    (hN : 2 ≤ N) (ht : (k, r, q) ∈ oddCofactorTriples N)
    (hh : h ∣ shiftedTotient m') :
    goodDeterminantPrimes (reducedTotientDet (k * r * q) m')
      (Nat.totient (k * r * q)) (shiftedTotient m') z U ⊆
        (smallDeterminantPrimes U z k r h).filter
          (fun p ↦ p ∣ reducedTotientDet (k * r * q) m') := by
  have hdata := mem_oddCofactorTriples_iff.mp ht
  have hsep := oddCofactorTriples_separated hN ht
  have hr := (mem_middlePrimes_iff.mp hdata.2.1).2.2
  have hq := (mem_largePrimes_iff.mp hdata.2.2).2.2
  have hφ := totient_mul_two_primes hr hq
    (Nat.not_dvd_of_pos_of_lt hsep.1 hsep.2.1)
    (Nat.not_dvd_of_pos_of_lt (mul_pos hsep.1 hr.pos) hsep.2.2)
  have hkdiv : Nat.totient k ∣ Nat.totient (k * r * q) := by
    refine ⟨(r - 1) * (q - 1), ?_⟩
    rw [hφ]
    ring
  have hrdiv : r - 1 ∣ Nat.totient (k * r * q) := by
    refine ⟨Nat.totient k * (q - 1), ?_⟩
    rw [hφ]
    ring
  intro p hp
  obtain ⟨hp, hpH, hpφ, hpF⟩ := Finset.mem_filter.mp hp
  have hprime := Erdos851.mem_sievePrimes.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨mem_smallDeterminantPrimes_iff.mpr ⟨hprime.1, hprime.2.1, hprime.2.2,
    (fun hpk ↦ hpφ (hpk.trans hkdiv)), (fun hpr ↦ hpφ (hpr.trans hrdiv)), ?_⟩, hpH⟩
  exact hprime.2.2.coprime_iff_not_dvd.mpr (fun hph ↦ hpF (hph.trans hh))

theorem goodDeterminantPrimeMass_le_smallDeterminantMass {N k r q m' h z U : ℕ}
    (hN : 2 ≤ N) (ht : (k, r, q) ∈ oddCofactorTriples N)
    (hh : h ∣ shiftedTotient m') :
    (∑ p ∈ goodDeterminantPrimes (reducedTotientDet (k * r * q) m')
      (Nat.totient (k * r * q)) (shiftedTotient m') z U, (1 : ℝ) / p) ≤
        smallDeterminantMass U z k r q m' h := by
  unfold smallDeterminantMass
  rw [← Finset.sum_filter]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (goodDeterminantPrimes_subset_admissible hN ht hh) (fun p hp hnot ↦ by positivity)

#print axioms goodDeterminantPrimeMass_le_smallDeterminantMass

end Erdos822
