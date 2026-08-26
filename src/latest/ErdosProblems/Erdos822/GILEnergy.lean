/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.SmallRangeKernel
import ErdosProblems.Erdos822.MediumRangeKernel
import ErdosProblems.Erdos822.LargeRangeKernel
import ErdosProblems.Erdos822.WeightedKernelAssembly
import ErdosProblems.Erdos822.GILInputSize

/-! # The unconditional linear collision-energy estimate -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

theorem exists_eventually_gil_supportedKernel_bound {S T : ℕ}
    (hS : 0 < S) (hT : 0 < T) (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      (Real.log (2 : ℝ) / Real.log (Nat.nthRoot (4 * T) N : ℝ)) ^ 2 *
        (∑ m ∈ gilCofactors N S C, ∑ m' ∈ (gilCofactors N S C).erase m,
          supportedGcdSingularKernel (N ^ 60) m m' 2 (Nat.nthRoot (4 * T) N)) ≤ K * (N ^ 60 : ℕ) := by
  obtain ⟨K₁, hK₁, hsmall⟩ := exists_eventually_smallWeightedCommonDivisorKernel_bound hS hT C
  obtain ⟨K₂, hK₂, hmedium⟩ := exists_eventually_mediumWeightedCommonDivisorKernel_bound S C
  obtain ⟨K₃, hK₃, hlarge⟩ := exists_eventually_largeWeightedCommonDivisorKernel_bound S C
  obtain ⟨D, hD, hsum⟩ := exists_logRatio_sq_mul_sum_supportedGcd_le_of_threeRangeBounds
  refine ⟨D ^ 2 + K₁ + K₂ + K₃, by positivity, ?_⟩
  filter_upwards [hsmall, hmedium, hlarge, eventually_ge_atTop 1,
    eventually_nthRoot_ge (4 * T) 2 (by omega)] with N hsmall hmedium hlarge hN hy
  exact hsum N 2 (Nat.nthRoot (4 * T) N) (gilCofactors N S C) K₁ K₂ K₃
    hN (by norm_num) hy (gilCofactors_subset_oddRaw N S C) hsmall
    (hmedium 2 _ (by norm_num) hy) (hlarge 2 _ (by norm_num) hy)

theorem shiftedTotientReciprocalMass_le_full {m z y : ℕ} (hm : 0 < m) :
    shiftedTotientReciprocalMass m z y ≤ primeDivisorReciprocalMass (shiftedTotient m) := by
  have hsne : shiftedTotient m ≠ 0 := by dsimp [shiftedTotient]; omega
  unfold shiftedTotientReciprocalMass
  rw [← Finset.sum_filter]
  exact sum_inv_primeFilter_dvd_le_full hsne (fun p hp ↦ (Erdos851.mem_sievePrimes.mp hp).2.2)

theorem eventually_gilCofactors_subset_massGood {S : ℕ} (hS : 0 < S) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ z y : ℕ,
      gilCofactors N S C ⊆ massGoodOddCofactors N z y (C + 2) := by
  filter_upwards [eventually_gilCofactors_full_primeMass_le hS C] with N hmass
  intro z y m hm
  have hmraw := gilCofactors_subset_oddRaw N S C hm
  exact mem_massGoodOddCofactors_iff.mpr ⟨hmraw,
    (shiftedTotientReciprocalMass_le_full (oddRawCofactors_pos hmraw)).trans (hmass m hm)⟩

theorem exists_eventually_gilOuterInputs_energy_linear {S : ℕ}
    (hS : 0 < S) {C : ℝ} (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      (collisionEnergy (gilOuterInputs N S C) shiftedTotient : ℝ) ≤ K * (N ^ 60 : ℕ) := by
  obtain ⟨A, M, hA, hM, henergy⟩ := exists_filteredOdd_collisionEnergy_le_of_supportedSymmetricB5Sum
  obtain ⟨T₀ : ℕ, hT₀⟩ := exists_nat_gt (99 * Real.log A / 4)
  let T := max 101 (T₀ + 100)
  have hT101 : 101 ≤ T := le_max_left _ _
  have hTpos : 0 < T := by omega
  have hlog : Real.log A ≤ 4 * (T - 100 : ℕ) / 99 := by
    have hle : T₀ ≤ T - 100 := by dsimp [T]; omega
    have hleR : (T₀ : ℝ) ≤ (T - 100 : ℕ) := by exact_mod_cast hle
    linarith only [hT₀, hleR]
  obtain ⟨K, hK, hkernel⟩ := exists_eventually_gil_supportedKernel_bound hS hTpos C
  let D := (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (T - 100)) *
    (M ^ 2 * Real.exp (12 * (C + 2)))
  obtain ⟨J : ℕ, hJ⟩ := exists_nat_gt (D * K)
  refine ⟨(J : ℝ) + 6, by positivity, ?_⟩
  filter_upwards [hkernel, eventually_gilCofactors_subset_massGood hS C,
    eventually_ge_atTop 2, eventually_nthRoot_ge (4 * T) 2 (by omega)]
    with N hkernel hmass hN hy
  have hmain := sum_supportedSymmetricB5Weight_le_of_logRatio_kernel_bound
    (A := A) (C := M) (C₀ := C + 2) (S := T) (by linarith only [hA])
    (fun m hm ↦ oddRawCofactors_pos (gilCofactors_subset_oddRaw N S C hm)) hkernel
  have hmain' : (∑ m ∈ gilCofactors N S C, ∑ m' ∈ (gilCofactors N S C).erase m,
      supportedSymmetricB5Weight A M (C + 2) (N ^ 60) m m' 2 (Nat.nthRoot (4 * T) N) T) ≤
        J * (N ^ 60 : ℕ) := by
    calc
      _ ≤ D * (K * (N ^ 60 : ℕ)) := hmain
      _ = (D * K) * (N ^ 60 : ℕ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hJ.le (by positivity)
  simpa only [gilOuterInputs] using henergy (C + 2) N T J (gilCofactors N S C)
    (by linarith only [hC]) (hmass 2 _) hN hTpos hT101 hy hlog hmain'

#print axioms exists_eventually_gilOuterInputs_energy_linear

end Erdos822
