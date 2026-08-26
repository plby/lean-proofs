/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.PredecessorPairMass
import ErdosProblems.Erdos822.SlowCutoffB4Mass
import ErdosProblems.Erdos822.PrimeReciprocalUpper
import ErdosProblems.Erdos822.SmoothB1Cofactors

/-! # Retaining B4 at the square-rich cutoff -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

theorem eventually_internalTotientBadSmallFactors_mass_small
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∑ k ∈ internalTotientBadSmallFactors N (b1DoubleLog N), (1 : ℝ) / k) ≤
        ε * Real.log (N : ℝ) := by
  filter_upwards [eventually_internalShiftedPrimeBadSmallFactors_mass_small
      (ε := ε / 2) (by positivity),
    (tendsto_natCast_atTop_atTop.comp tendsto_b1DoubleLog_atTop).eventually_ge_atTop (4 / ε),
    tendsto_b1DoubleLog_atTop.eventually_ge_atTop 2, eventually_ge_atTop 4]
    with N hshift hZlarge hZ hN
  have hZpos : (0 : ℝ) < b1DoubleLog N := by exact_mod_cast (show 0 < b1DoubleLog N by omega)
  have hlogN : 1 ≤ Real.log (N : ℝ) := BoundedGaps.Maynard.one_le_log_natCast hN
  have hH : (harmonic N : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    have := harmonic_le_one_add_log N
    linarith
  have hcoeff : 2 / (b1DoubleLog N : ℝ) ≤ ε / 2 := by
    apply (div_le_iff₀ hZpos).mpr
    have h := (div_le_iff₀ hε).mp hZlarge
    dsimp only [Function.comp_apply] at h
    nlinarith only [h]
  have hsquare : (∑ k ∈ internalSquareBadSmallFactors N (b1DoubleLog N), (1 : ℝ) / k) ≤
      ε / 2 * Real.log (N : ℝ) := by
    refine (sum_inv_internalSquareBadSmallFactors_le (by omega : 1 ≤ b1DoubleLog N)).trans ?_
    calc
      _ ≤ 2 * Real.log (N : ℝ) / b1DoubleLog N := div_le_div_of_nonneg_right hH hZpos.le
      _ = (2 / (b1DoubleLog N : ℝ)) * Real.log (N : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (by linarith)
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg
    (internalTotientBadSmallFactors_subset N (b1DoubleLog N))
    (f := fun k : ℕ ↦ (1 : ℝ) / k) (fun k hk hnot ↦ by positivity)
  have hunion := sum_union_le_add_sum (s := internalSquareBadSmallFactors N (b1DoubleLog N))
    (t := internalShiftedPrimeBadSmallFactors N (b1DoubleLog N))
    (f := fun k ↦ (1 : ℝ) / k) (fun k hk ↦ by positivity)
  linarith only [hsub, hunion, hsquare, hshift]

theorem eventually_slowInternalTotientCofactors_mass_small
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∑ m ∈ slowInternalTotientCofactors N (b1DoubleLog N), (1 : ℝ) / m) ≤
        ε * Real.log (N : ℝ) := by
  filter_upwards [eventually_internalTotientBadSmallFactors_mass_small hε,
    eventually_reciprocalPrimeIntervalSum_four_five_upper_one,
    eventually_reciprocalPrimeIntervalSum_twentyone_twentytwo_upper_one,
    eventually_ge_atTop 2] with N hsmall hR hQ hN
  have hR' : (∑ r ∈ middlePrimes N, (1 : ℝ) / r) ≤ 1 := by
    simpa [reciprocalPrimeIntervalSum, middlePrimes_eq_primesLE_sdiff] using hR
  have hQ' : (∑ q ∈ largePrimes N, (1 : ℝ) / q) ≤ 1 := by
    simpa [reciprocalPrimeIntervalSum, largePrimes_eq_primesLE_sdiff] using hQ
  have hmass : (∑ m ∈ slowInternalTotientCofactors N (b1DoubleLog N), (1 : ℝ) / m) =
      (∑ k ∈ internalTotientBadSmallFactors N (b1DoubleLog N), (1 : ℝ) / k) *
        (∑ r ∈ middlePrimes N, (1 : ℝ) / r) * (∑ q ∈ largePrimes N, (1 : ℝ) / q) := by
    rw [sum_inv_slowInternalTotientCofactors_eq hN]
    rw [mul_assoc]
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro q hq
    push_cast
    ring
  rw [hmass]
  calc
    _ ≤ (∑ k ∈ internalTotientBadSmallFactors N (b1DoubleLog N), (1 : ℝ) / k) * 1 * 1 := by
      gcongr
    _ ≤ ε * Real.log (N : ℝ) := by simpa using hsmall

theorem eventually_slowSmallMiddlePredCofactors_mass_small
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∑ m ∈ slowSmallMiddlePredCofactors N (b1DoubleLog N), (1 : ℝ) / m) ≤
        ε * Real.log (N : ℝ) := by
  filter_upwards [eventually_predecessor_common_prime_mass_small hε 5,
    eventually_reciprocalPrimeIntervalSum_twentyone_twentytwo_upper_one,
    eventually_ge_atTop 2] with N hsmall hQ hN
  have hQ' : (∑ q ∈ largePrimes N, (1 : ℝ) / q) ≤ 1 := by
    simpa [reciprocalPrimeIntervalSum, largePrimes_eq_primesLE_sdiff] using hQ
  have hA : middlePrimes N ⊆ Nat.primesLE (N ^ 5) := by
    intro r hr
    exact Nat.mem_primesLE.mpr (mem_middlePrimes_iff.mp hr).2
  have hsmall' := hsmall (middlePrimes N) hA
  change (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k *
    ∑ r ∈ slowSmallMiddlePredFiber N (b1DoubleLog N) k, (1 : ℝ) / r) ≤ _ at hsmall'
  have hmass : (∑ m ∈ slowSmallMiddlePredCofactors N (b1DoubleLog N), (1 : ℝ) / m) =
      (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k *
        ∑ r ∈ slowSmallMiddlePredFiber N (b1DoubleLog N) k, (1 : ℝ) / r) *
          (∑ q ∈ largePrimes N, (1 : ℝ) / q) := by
    rw [sum_inv_slowSmallMiddlePredCofactors_eq hN]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [mul_assoc]
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro q hq
    push_cast
    ring
  rw [hmass]
  calc
    _ ≤ (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k *
        ∑ r ∈ slowSmallMiddlePredFiber N (b1DoubleLog N) k, (1 : ℝ) / r) * 1 := by gcongr
    _ ≤ _ := by simpa using hsmall'

theorem eventually_slowSmallLargePredCofactors_mass_small
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∑ m ∈ slowSmallLargePredCofactors N (b1DoubleLog N), (1 : ℝ) / m) ≤
        ε * Real.log (N : ℝ) := by
  filter_upwards [eventually_predecessor_common_prime_mass_small hε 22,
    eventually_reciprocalPrimeIntervalSum_four_five_upper_one,
    eventually_ge_atTop 2] with N hsmall hR hN
  have hR' : (∑ r ∈ middlePrimes N, (1 : ℝ) / r) ≤ 1 := by
    simpa [reciprocalPrimeIntervalSum, middlePrimes_eq_primesLE_sdiff] using hR
  have hA : largePrimes N ⊆ Nat.primesLE (N ^ 22) := by
    intro q hq
    exact Nat.mem_primesLE.mpr (mem_largePrimes_iff.mp hq).2
  have hsmall' := hsmall (largePrimes N) hA
  change (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k *
    ∑ q ∈ slowSmallLargePredFiber N (b1DoubleLog N) k, (1 : ℝ) / q) ≤ _ at hsmall'
  have hmass : (∑ m ∈ slowSmallLargePredCofactors N (b1DoubleLog N), (1 : ℝ) / m) =
      (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k *
        ∑ q ∈ slowSmallLargePredFiber N (b1DoubleLog N) k, (1 : ℝ) / q) *
          (∑ r ∈ middlePrimes N, (1 : ℝ) / r) := by
    rw [sum_inv_slowSmallLargePredCofactors_eq hN]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [mul_assoc]
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro r hr
    push_cast
    ring
  rw [hmass]
  calc
    _ ≤ (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k *
        ∑ q ∈ slowSmallLargePredFiber N (b1DoubleLog N) k, (1 : ℝ) / q) * 1 := by gcongr
    _ ≤ _ := by simpa using hsmall'

theorem eventually_slowCutoffBadOddCofactors_doubleLog_mass_small
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∑ m ∈ slowCutoffBadOddCofactors N (b1DoubleLog N), (1 : ℝ) / m) ≤
        ε * Real.log (N : ℝ) := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_slowInternalTotientCofactors_mass_small (ε := ε / 4) (by positivity),
    eventually_slowSmallMiddlePredCofactors_mass_small (ε := ε / 4) (by positivity),
    eventually_slowSmallLargePredCofactors_mass_small (ε := ε / 4) (by positivity),
    hlog.eventually_ge_atTop (8 / ε), eventually_ge_atTop 2] with N hI hM hL hlogN hN
  have hfourth : (∑ m ∈ middlePredLargeCofactors N, (1 : ℝ) / m) ≤ 2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (middlePredLargeCofactors_subset_largeCutoffBad hN)
      (fun m hm hnot ↦ by positivity)).trans (sum_inv_largeCutoffBadOddCofactors_le_two hN)
  have hcoeff := (div_le_iff₀ hε).mp hlogN
  have hsum := sum_inv_slowCutoffBadOddCofactors_le_four_channels
    (y := b1DoubleLog N) hN
  linarith only [hI, hM, hL, hfourth, hcoeff, hsum]

/-- The prime gap built into B1 permits deleting only above the double log,
although the final B4 condition begins at its fourth root. -/
theorem smoothB1_bad_gcd_subset_doubleLog {N : ℕ} (hN : 2 ≤ N) :
    (smoothB1Cofactors N).filter (fun m ↦
      ∃ p, p.Prime ∧ b1Cutoff N < p ∧ p ∣ m ∧ p ∣ Nat.totient m) ⊆
        slowCutoffBadOddCofactors N (b1DoubleLog N) := by
  intro m hm
  obtain ⟨hm, p, hp, hyp, hpm, hpφ⟩ := Finset.mem_filter.mp hm
  have hpZ : b1DoubleLog N < p := by
    by_contra h
    exact b1Cofactors_no_intermediate_prime hN (smoothB1Cofactors_subset_b1 N hm)
      p hp hyp (by omega) hpm
  exact mem_slowCutoffBadOddCofactors_iff.mpr
    ⟨smoothB1Cofactors_subset_oddRaw N hm, p, hp, hpZ, hpm, hpφ⟩

noncomputable def gcdSmoothB1Cofactors (N : ℕ) : Finset ℕ :=
  (smoothB1Cofactors N).filter fun m ↦
    ∀ p, p.Prime → b1Cutoff N < p → p ∣ m → ¬ p ∣ Nat.totient m

theorem exists_eventually_sum_inv_gcdSmoothB1Cofactors_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * Real.log (N : ℝ) ≤ ∑ m ∈ gcdSmoothB1Cofactors N, (1 : ℝ) / m := by
  obtain ⟨c, hc, hmass⟩ := exists_eventually_sum_inv_smoothB1Cofactors_lower
  refine ⟨c / 2, by positivity, ?_⟩
  filter_upwards [hmass,
    eventually_slowCutoffBadOddCofactors_doubleLog_mass_small (ε := c / 2) (by positivity),
    eventually_ge_atTop 2] with N hmassN hbad hN
  let P : ℕ → Prop := fun m ↦ ∀ p, p.Prime → b1Cutoff N < p → p ∣ m → ¬ p ∣ Nat.totient m
  have hsplit := Finset.sum_filter_add_sum_filter_not (smoothB1Cofactors N) P (fun m ↦ (1 : ℝ) / m)
  have hsub : (smoothB1Cofactors N).filter (fun m ↦ ¬ P m) ⊆
      slowCutoffBadOddCofactors N (b1DoubleLog N) := by
    convert smoothB1_bad_gcd_subset_doubleLog hN using 1
    ext m
    simp [P]
  have hbad' := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun m : ℕ ↦ (1 : ℝ) / m) (fun m hm hnot ↦ by positivity)
  change (∑ m ∈ gcdSmoothB1Cofactors N, (1 : ℝ) / m) + _ = _ at hsplit
  linarith only [hmassN, hbad, hbad', hsplit]

theorem gcdSmoothB1Cofactors_preserving {N m : ℕ} (hN : 2 ≤ N)
    (hm : m ∈ gcdSmoothB1Cofactors N) : SmoothTotientPreserving m (b1Cutoff N) :=
  smoothB1Cofactors_preserving hN (Finset.mem_filter.mp hm).1

theorem gcdSmoothB1Cofactors_largeGcdFree {N m : ℕ}
    (hm : m ∈ gcdSmoothB1Cofactors N) : m ∈ largeGcdFreeOddCofactors N (b1Cutoff N) :=
  mem_largeGcdFreeOddCofactors_iff.mpr
    ⟨smoothB1Cofactors_subset_oddRaw N (Finset.mem_filter.mp hm).1,
      fun p hp hyp h ↦ (Finset.mem_filter.mp hm).2 p hp hyp h.1 h.2⟩

#print axioms exists_eventually_sum_inv_gcdSmoothB1Cofactors_lower

end Erdos822
