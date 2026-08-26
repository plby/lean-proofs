/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.DeterminantChargeFubini
import ErdosProblems.Erdos822.SmallQuadraticMass

/-! # The determinant first moment over a fixed quadratic fiber -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

theorem exists_eventually_fixedPair_determinantCharge_bound (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (B : Finset ℕ) (k m' h U z cutoff : ℕ),
        B ⊆ squarefreeLargeGcdFreeOddCofactors N cutoff → m' ∈ B → k ∈ oddSmallFactors N →
        0 < h → h ≤ N ^ 3 → primeDivisorReciprocalMass h ≤ C → roughPart h cutoff = h →
        cutoff < N ^ 21 → U ≤ N → 2 ≤ z →
        (∑ rq ∈ fixedCommonDivisorPrimePairs B N (N ^ 60) k m' h,
          ((1 : ℝ) / (rq.1 * rq.2 : ℕ)) * smallDeterminantMass U z k rq.1 rq.2 m' h) ≤
          K * (4 : ℝ) ^ h.primeFactors.card / ((h : ℝ) ^ 2 * z * Real.log (z : ℝ)) := by
  obtain ⟨A, hA, hresidue⟩ := exists_eventually_small_primeResidueClasses_bound C
  obtain ⟨D, hD, hcharge⟩ := exists_eventually_sharp_smallDeterminantPrime_average C
  refine ⟨A * D, by positivity, ?_⟩
  filter_upwards [hresidue, hcharge, eventually_ge_atTop 2] with N hresidue hcharge hN
  intro B k m' h U z cutoff hB hm' hk hh hhN hmass hrough hcutoff hUN hz
  have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  by_cases hne : (fixedCommonDivisorPrimePairs B N (N ^ 60) k m' h).Nonempty
  · obtain ⟨r₀, q₀, hbase, hcover⟩ := exists_quadraticClasses_cover_fixedCommonDivisorPrimePairs
      hN rfl hcutoff hk hB hm' hne
    rw [hrough] at hcover
    let R := quadraticMiddlePrimeClasses N h (r₀ * q₀) (r₀ + q₀)
    have hsupport : ∀ p : ℕ, p.Prime → p ∣ h → cutoff < p := by
      intro p hp hpd
      apply prime_dvd_roughPart_gt hp
      rwa [hrough]
    have hbaseData := mem_fixedCommonDivisorPrimePairs_iff.mp hbase
    have hsq : Squarefree h := commonDivisor_squarefree_of_squarefreeLargeGcdFree
      (hB hbaseData.2.2.1) hbaseData.2.2.2.2 hsupport
    have hcard : ((quadraticAssignmentResidues (r₀ * q₀) (r₀ + q₀) h).card : ℝ) ≤
        (2 : ℝ) ^ h.primeFactors.card := by
      exact_mod_cast quadraticAssignmentResidues_card_le_two_pow hsq
    have hRmass : (∑ r ∈ R, (1 : ℝ) / r) ≤ (2 : ℝ) ^ h.primeFactors.card * (A / h) := by
      calc
        _ ≤ ∑ a ∈ quadraticAssignmentResidues (r₀ * q₀) (r₀ + q₀) h,
            ∑ r ∈ middlePrimeResidueClass N h a, (1 : ℝ) / r := by
          apply sum_biUnion_le_sum
          intro a ha r hr
          positivity
        _ ≤ ∑ _a ∈ quadraticAssignmentResidues (r₀ * q₀) (r₀ + q₀) h, A / h :=
          Finset.sum_le_sum fun a ha ↦ (hresidue h a cutoff hh hhN hmass).1
        _ = ((quadraticAssignmentResidues (r₀ * q₀) (r₀ + q₀) h).card : ℝ) * (A / h) := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
    have hBraw : B ⊆ oddRawCofactors N := hB.trans
      (squarefreeLargeGcdFreeOddCofactors_subset_oddRaw N cutoff)
    have hB4 := hB.trans (squarefreeLargeGcdFreeOddCofactors_subset_largeGcdFree N cutoff)
    have hlarge' : ∀ s ∈ outerPrimes (N ^ 60) m', m' < s :=
      fun s hs ↦ oddOuterPrime_large_of_mem hN (hBraw hm') hs
    have hslice (r : ℕ) (hr : r ∈ middlePrimes N) :
        (∑ q ∈ fixedCommonDivisorLargePrimes B N (N ^ 60) k r m' h,
          ((1 : ℝ) / q) * smallDeterminantMass U z k r q m' h) ≤
          if r ∈ R then D / ((h : ℝ) * z * Real.log (z : ℝ)) else 0 := by
      by_cases hrR : r ∈ R
      · rw [if_pos hrR, sum_smallDeterminantMass_fixedLargePrimes_eq]
        apply hcharge B (N ^ 60) k r m' h U z cutoff hk hr (oddRawCofactors_pos (hBraw hm'))
          _ hlarge' hB4 hsupport hh hhN hmass hUN hz
        intro q hq s hs
        apply oddOuterPrime_large_of_mem hN _ hs
        exact Finset.mem_image.mpr ⟨(k, r, q), mem_oddCofactorTriples_iff.mpr ⟨hk, hr, hq⟩, rfl⟩
      · have hempty : fixedCommonDivisorLargePrimes B N (N ^ 60) k r m' h = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.mp
          rintro ⟨q, hq⟩
          have hqdata := Finset.mem_filter.mp hq
          have hp : (r, q) ∈ fixedCommonDivisorPrimePairs B N (N ^ 60) k m' h :=
            mem_fixedCommonDivisorPrimePairs_iff.mpr ⟨hr, hqdata.1, hqdata.2⟩
          exact hrR (Finset.mem_product.mp (hcover hp)).1
        simp [hempty, hrR]
    have hsub : (middlePrimes N).filter (fun r ↦ r ∈ R) ⊆ R := by
      intro r hr
      exact (Finset.mem_filter.mp hr).2
    have htwofour : (2 : ℝ) ^ h.primeFactors.card ≤ (4 : ℝ) ^ h.primeFactors.card :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _
    rw [sum_smallDeterminantMass_fixedPairs_eq]
    calc
      _ ≤ ∑ r ∈ middlePrimes N, ((1 : ℝ) / r) *
          (if r ∈ R then D / ((h : ℝ) * z * Real.log (z : ℝ)) else 0) :=
        Finset.sum_le_sum fun r hr ↦ mul_le_mul_of_nonneg_left (hslice r hr) (by positivity)
      _ = (D / ((h : ℝ) * z * Real.log (z : ℝ))) *
          ∑ r ∈ (middlePrimes N).filter (fun r ↦ r ∈ R), (1 : ℝ) / r := by
        rw [Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro r hr
        split_ifs <;> ring
      _ ≤ (D / ((h : ℝ) * z * Real.log (z : ℝ))) *
          ((2 : ℝ) ^ h.primeFactors.card * (A / h)) :=
        mul_le_mul_of_nonneg_left
          ((Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r hr hnot ↦ by positivity)).trans hRmass)
          (by positivity)
      _ = (A * D / ((h : ℝ) ^ 2 * z * Real.log (z : ℝ))) * (2 : ℝ) ^ h.primeFactors.card := by ring
      _ ≤ (A * D / ((h : ℝ) ^ 2 * z * Real.log (z : ℝ))) * (4 : ℝ) ^ h.primeFactors.card :=
        mul_le_mul_of_nonneg_left htwofour (by positivity)
      _ = _ := by ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.sum_empty]
    positivity

#print axioms exists_eventually_fixedPair_determinantCharge_bound

end Erdos822
