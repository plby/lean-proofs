import ErdosProblems.Erdos380.SaddleParameters

/-! # Growth estimates for the probability parameters -/

open Filter
open scoped Topology

namespace Erdos380

theorem eventually_logarithmicCeiling_pow_le_scaleBase (a : ℕ) :
    ∀ᶠ N : ℕ in atTop, logarithmicCeiling N ^ a ≤ scaleBase N := by
  filter_upwards [eventually_log_pow_le_scaleBase (a + 1), eventually_ge_atTop 1,
    log_nat_tendsto_atTop.eventually (eventually_ge_atTop (2 : ℝ)),
    log_nat_tendsto_atTop.eventually (eventually_ge_atTop ((2 : ℝ) ^ a))] with N hpow hN hL hbig
  have hB := (logarithmicCeiling_bounds hN hL).2
  have hL0 : 0 ≤ Real.log (N : ℝ) := by linarith
  have h : (logarithmicCeiling N : ℝ) ^ a ≤ scaleBase N := by
    calc
      (logarithmicCeiling N : ℝ) ^ a ≤ (2 * Real.log N) ^ a :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hB a
      _ = (2 : ℝ) ^ a * Real.log N ^ a := mul_pow _ _ _
      _ ≤ Real.log N * Real.log N ^ a := mul_le_mul_of_nonneg_right hbig (pow_nonneg hL0 a)
      _ = Real.log N ^ (a + 1) := (pow_succ' _ _).symm
      _ ≤ scaleBase N := hpow
  exact_mod_cast h

theorem probabilityParameter_tendsto_atTop : Tendsto probabilityParameter atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  let c := max b 1
  have hc : 0 < c := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hε : 0 < 1 / (10000 * c) := by positivity
  filter_upwards [log_scaleBase_div_log_tendsto_zero.eventually (gt_mem_nhds hε),
    log_nat_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    log_scaleBase_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with N hratio hL hS
  have hcross := (div_le_div_iff₀ hL (show 0 < 10000 * c by positivity)).mp hratio.le
  apply (le_max_left b 1).trans
  change c ≤ Real.log (N : ℝ) / (10000 * Real.log (scaleBase N : ℝ))
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith

theorem eventually_probabilityParameter_sq_lower : ∀ᶠ N : ℕ in atTop,
    Real.log (N : ℝ) / (200 * Real.log (Real.log N)) ≤ probabilityParameter N ^ 2 := by
  filter_upwards [log_scaleBase_div_saddleLog_tendsto_one.eventually
      (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)),
    saddleLog_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    log_scaleBase_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    log_nat_tendsto_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with N hratio hf hS hN
  have hL : 0 < Real.log (N : ℝ) := by linarith
  have hll : 0 < Real.log (Real.log (N : ℝ)) := Real.log_pos hN
  have hSle : Real.log (scaleBase N : ℝ) ≤ 2 * saddleLog N := (div_le_iff₀ hf).mp hratio.le
  have hSsq := pow_le_pow_left₀ hS.le hSle 2
  rw [mul_pow, saddleLog_sq hL.le hll.le] at hSsq
  unfold probabilityParameter
  rw [div_pow]
  apply (div_le_div_iff₀ (by positivity) (pow_pos (show 0 < 10000 * Real.log (scaleBase N : ℝ) by positivity) 2)).mpr
  have hmul := mul_le_mul_of_nonneg_left hSsq hL.le
  nlinarith

theorem eventually_shortWidth_le_probabilityParameter_pow :
    ∀ᶠ N : ℕ in atTop, (shortWidth N : ℝ) ≤ probabilityParameter N ^ 48 := by
  have hraw := (isLittleO_log_rpow_rpow_atTop (s := 4) 24 (by norm_num)).tendsto_div_nhds_zero.comp
    log_nat_tendsto_atTop
  have hslow : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) ^ 24 / Real.log N ^ 4)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_ofNat] using hraw
  let C : ℝ := 2 ^ 20 * 200 ^ 24
  have hc := hslow.const_mul C
  simp only [mul_zero] at hc
  filter_upwards [eventually_probabilityParameter_sq_lower,
    hc.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)), eventually_ge_atTop 1,
    log_nat_tendsto_atTop.eventually (eventually_ge_atTop (2 : ℝ))] with N hU hsmall hN hL2
  have hL : 0 < Real.log (N : ℝ) := by linarith
  have hll : 0 < Real.log (Real.log (N : ℝ)) := Real.log_pos (by linarith)
  have hnum : C * Real.log (Real.log (N : ℝ)) ^ 24 ≤ Real.log N ^ 4 := by
    have h' : (C * Real.log (Real.log (N : ℝ)) ^ 24) / Real.log N ^ 4 ≤ 1 := by
      simpa only [mul_div_assoc] using hsmall.le
    simpa only [one_mul] using (div_le_iff₀ (pow_pos hL 4)).mp h'
  have hB := (logarithmicCeiling_bounds hN hL2).2
  have hmain : (2 * Real.log (N : ℝ)) ^ 20 ≤
      (Real.log (N : ℝ) / (200 * Real.log (Real.log N))) ^ 24 := by
    rw [div_pow]
    apply (le_div_iff₀ (pow_pos (show 0 < 200 * Real.log (Real.log (N : ℝ)) by positivity) 24)).mpr
    calc
      (2 * Real.log (N : ℝ)) ^ 20 * (200 * Real.log (Real.log N)) ^ 24 =
          Real.log N ^ 20 * (C * Real.log (Real.log N) ^ 24) := by dsimp [C]; ring
      _ ≤ Real.log N ^ 20 * Real.log N ^ 4 := mul_le_mul_of_nonneg_left hnum (by positivity)
      _ = Real.log N ^ 24 := by rw [← pow_add]
  calc
    (shortWidth N : ℝ) ≤ (2 * Real.log (N : ℝ)) ^ 20 := by
      rw [shortWidth, Nat.cast_pow]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hB 20
    _ ≤ (Real.log (N : ℝ) / (200 * Real.log (Real.log N))) ^ 24 := hmain
    _ ≤ (probabilityParameter N ^ 2) ^ 24 := pow_le_pow_left₀ (by positivity) hU 24
    _ = probabilityParameter N ^ 48 := by rw [← pow_mul]

end Erdos380
