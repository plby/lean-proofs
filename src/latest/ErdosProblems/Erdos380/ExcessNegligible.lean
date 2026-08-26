import ErdosProblems.Erdos380.GlobalSieveScale
import ErdosProblems.Erdos380.LargeIntervalScale

/-! # The complete excess count is negligible -/

open Filter Asymptotics
open scoped Topology

namespace Erdos380

theorem exists_eventually_excess_relative_bound : ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
    ((excessPointsUpTo N).card : ℝ) ≤
      (8023 / (scaleBase N : ℝ) + K * neighborErrorFactor N) * (singletonBadUpTo N).card := by
  obtain ⟨K, hK, hshort⟩ := exists_eventually_shortExcess_relative_bound
  refine ⟨K, hK, ?_⟩
  filter_upwards [hshort, eventually_largeIntervalPrime_scale_bound,
    eventually_smoothRunStarts_scale_bound, eventually_singletonBadUpTo_scale_lower,
    eventually_ge_atTop 1,
    log_nat_tendsto_atTop.eventually (eventually_ge_atTop (2 : ℝ))]
      with N hshort hlarge hruns hA hN hL
  have hB : 2 ≤ logarithmicCeiling N := by
    have hLB := (logarithmicCeiling_bounds hN hL).1
    exact_mod_cast (show (2 : ℝ) ≤ logarithmicCeiling N by linarith)
  have hW2 : 2 ≤ shortWidth N := hB.trans (le_self_pow (by omega) (by decide : 20 ≠ 0))
  have hH : 0 < runWidth N := Nat.div_pos hW2 (by norm_num)
  have hHW : 2 * runWidth N ≤ shortWidth N + 1 := by
    have h := Nat.div_mul_le_self (shortWidth N) 2
    change runWidth N * 2 ≤ shortWidth N at h
    omega
  have hcover : ((excessPointsUpTo N).card : ℝ) ≤ (shortExcessPointsUpTo N (shortWidth N)).card +
      (badPointsWithLargeIntervalPrime N (largePrimeScale N)).card +
        2 * (smoothRunStarts N (runWidth N) (largePrimeScale N)).card := by
    exact_mod_cast excessPointsUpTo_card_le_short_large_runs (N := N) (T := largePrimeScale N) hH hHW
  have hruns' : ((smoothRunStarts N (runWidth N) (largePrimeScale N)).card : ℝ) ≤
      2 * N / (scaleBase N : ℝ) ^ 2002 := by
    apply hruns.trans
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left
      (scale_quotient_mono N (by decide : 2002 ≤ 2200)) (by norm_num : (0 : ℝ) ≤ 2)
  have hrest : ((excessPointsUpTo N).card : ℝ) ≤
      (shortExcessPointsUpTo N (shortWidth N)).card + 8004 * N / (scaleBase N : ℝ) ^ 2002 := by
    simp only [mul_div_assoc] at hlarge hruns' ⊢
    linarith
  have hSpos : (0 : ℝ) < scaleBase N := by exact_mod_cast
    (lt_of_lt_of_le Nat.zero_lt_one (one_le_scaleBase N))
  have hnorm : (N : ℝ) / (scaleBase N : ℝ) ^ 2002 ≤ (singletonBadUpTo N).card / (scaleBase N : ℝ) := by
    apply (le_div_iff₀ hSpos).mpr
    exact (scale_quotient_succ_mul N 2001).le.trans hA
  calc
    _ ≤ _ := hrest
    _ ≤ (19 / (scaleBase N : ℝ) + K * neighborErrorFactor N) * (singletonBadUpTo N).card +
        8004 * ((singletonBadUpTo N).card / (scaleBase N : ℝ)) := by
      simpa only [mul_div_assoc] using add_le_add hshort
        (mul_le_mul_of_nonneg_left hnorm (by norm_num : (0 : ℝ) ≤ 8004))
    _ = _ := by ring

theorem excessPointsUpTo_isLittleO_singletonCount :
    (fun N : ℕ => ((excessPointsUpTo N).card : ℝ)) =o[atTop]
      (fun N : ℕ => ((singletonBadUpTo N).card : ℝ)) := by
  obtain ⟨K, hK, hbound⟩ := exists_eventually_excess_relative_bound
  have hzero : Tendsto (fun N : ℕ => 8023 / (scaleBase N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp scaleBase_tendsto_atTop)
  have hmajor := hzero.add (neighborErrorFactor_tendsto_zero.const_mul K)
  simp only [mul_zero, add_zero] at hmajor
  have hrange : ∀ᶠ N : ℕ in atTop,
      0 ≤ ((excessPointsUpTo N).card : ℝ) / (singletonBadUpTo N).card ∧
      ((excessPointsUpTo N).card : ℝ) / (singletonBadUpTo N).card ≤
        8023 / (scaleBase N : ℝ) + K * neighborErrorFactor N := by
    filter_upwards [hbound, eventually_singletonBadUpTo_card_pos] with N hN hA
    exact ⟨div_nonneg (Nat.cast_nonneg _) hA.le, (div_le_iff₀ hA).mpr hN⟩
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [eventually_singletonBadUpTo_card_pos] with N hN
    exact fun h => (hN.ne' h).elim
  · exact squeeze_zero' (hrange.mono fun _ h => h.1) (hrange.mono fun _ h => h.2) hmajor

theorem excessCount_isLittleO_A : excessCount =o[atTop] A := by
  exact excessPointsUpTo_isLittleO_singletonCount.comp_tendsto
    (tendsto_nat_floor_atTop : Tendsto (fun x : ℝ => ⌊x⌋₊) atTop atTop)

end Erdos380
