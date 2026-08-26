import ErdosProblems.Erdos1164.UpperScaleBounds

/-! # The upper in-probability order with all eventual quantifiers -/

open Filter MeasureTheory
open scoped Topology

namespace Erdos1164

private theorem exists_small_exp (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℕ, 1 ≤ t ∧ Real.exp (-(t : ℝ)) < ε / 2 := by
  let t := ⌈4 / ε⌉₊ + 1
  have ht : 1 ≤ t := by dsimp [t]; omega
  have htR : 4 / ε < (t : ℝ) := by
    have h := Nat.le_ceil (4 / ε)
    dsimp only [t]
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hprod := (div_lt_iff₀ hε).mp htR
  have hexp := Real.add_one_le_exp (t : ℝ)
  have hmul := mul_le_mul_of_nonneg_right hexp hε.le
  refine ⟨t, ht, ?_⟩
  rw [Real.exp_neg]
  apply (inv_lt_iff_one_lt_mul₀ (Real.exp_pos (t : ℝ))).mpr
  nlinarith

private theorem large_scale_for_floor {b : ℝ} (hb : 0 < b) {n : ℕ}
    (hbig : 8 ≤ b * sqrtLogTime n)
    (hpay : 2000 * potentialError / (potentialSlope * Real.log 2) ≤ b * sqrtLogTime n) :
    LargeTargetScale (2 ^ ⌊b * sqrtLogTime n⌋₊) := by
  have hj := (floor_scale_bounds hb (by linarith : 2 ≤ b * sqrtLogTime n)).1
  have hj4 : (4 : ℝ) ≤ (⌊b * sqrtLogTime n⌋₊ : ℝ) := by linarith
  apply dyadic_largeTargetScale (by exact_mod_cast hj4)
  have hpos := mul_pos potentialSlope_pos log_two_pos
  have hpay' := (div_le_iff₀ hpos).mp hpay
  have hmul := mul_le_mul_of_nonneg_right hj hpos.le
  nlinarith

private theorem floor_half_gain_ge {b : ℝ} (hb : 0 < b) {n t : ℕ}
    (hbig : 2 ≤ b * sqrtLogTime n)
    (hpay : 4 * (t : ℝ) / (coveringGain * Real.log 2) ≤ b * sqrtLogTime n) :
    (t : ℝ) ≤ coveringGain * (harmonic (2 ^ ⌊b * sqrtLogTime n⌋₊) : ℝ) / 2 := by
  have hj := (floor_scale_bounds hb hbig).1
  have hH := harmonic_dyadic_lower ⌊b * sqrtLogTime n⌋₊
  have hpos := mul_pos coveringGain_pos log_two_pos
  have hpay' := (div_le_iff₀ hpos).mp hpay
  have hmul := mul_le_mul_of_nonneg_right hj hpos.le
  have hh := mul_le_mul_of_nonneg_left hH coveringGain_pos.le
  nlinarith

/-- The upper tail is small at every sufficiently large deterministic time,
with a coefficient depending only on the requested error probability. -/
theorem logRadius_upper_in_probability (ε : ℝ) (hε : 0 < ε) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ n : ℕ in atTop,
      walkLaw.real {s | b * sqrtLogTime n < logRadius s n} < ε := by
  obtain ⟨t, ht, heps⟩ := exists_small_exp ε hε
  let D := potentialSlope * coveringGain * Real.log 2 ^ 2
  have hD : 0 < D := by
    dsimp only [D]
    exact mul_pos (mul_pos potentialSlope_pos coveringGain_pos) (sq_pos_of_pos log_two_pos)
  have htR : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  let b := Real.sqrt (12800 * (t : ℝ) / D)
  have hb : 0 < b := Real.sqrt_pos.mpr (by positivity)
  have hb2 : b ^ 2 * D = 12800 * (t : ℝ) := by
    rw [show b ^ 2 = 12800 * (t : ℝ) / D from Real.sq_sqrt (by positivity),
      div_mul_cancel₀ _ hD.ne']
  have hcoef : potentialSlope * coveringGain * b ^ 2 * Real.log 2 ^ 2 = 12800 * (t : ℝ) := by
    dsimp only [D] at hb2
    nlinarith
  refine ⟨3 * b * Real.log 2, mul_pos (mul_pos (by norm_num) hb) log_two_pos, ?_⟩
  have hlim : Tendsto (fun n : ℕ ↦ b * sqrtLogTime n) atTop atTop :=
    sqrtLogTime_tendsto.const_mul_atTop hb
  filter_upwards [eventually_ge_atTop 2, eventually_sqrtLogTime_ge 1,
    hlim.eventually (eventually_ge_atTop 8),
    hlim.eventually (eventually_ge_atTop (2000 * potentialError / (potentialSlope * Real.log 2))),
    hlim.eventually (eventually_ge_atTop (4 * (t : ℝ) / (coveringGain * Real.log 2)))]
    with n hn hu hbig hlarge hgain
  let j := ⌊b * sqrtLogTime n⌋₊
  let m := 2 ^ j
  let K := upperClockSplit t n
  have hscale : 2 ≤ b * sqrtLogTime n := by linarith
  have hm : LargeTargetScale m := large_scale_for_floor hb hbig hlarge
  have hK : 2 ≤ K := upperClockSplit_ge_two ht n
  have hlog : 1 ≤ Real.log (n : ℝ) := by
    rw [← sqrtLogTime_sq (by omega : 1 ≤ n)]
    nlinarith
  have hKbound : (K : ℝ) ≤ 400 * (t : ℝ) * Real.log (n : ℝ) := upperClockSplit_le ht hn hlog
  have hproduct := dyadic_cover_cost_product hb (by omega : 1 ≤ n) hscale
  rw [hcoef] at hproduct
  have hKcost : (K : ℝ) ≤ (targetVisitCost m : ℝ) * coveringGain * (harmonic m : ℝ) / 2 := by
    change 12800 * (t : ℝ) * Real.log (n : ℝ) / 16 ≤
      (targetVisitCost m : ℝ) * coveringGain * (harmonic m : ℝ) / 2 at hproduct
    have hnon : 0 ≤ (t : ℝ) * Real.log (n : ℝ) := mul_nonneg htR.le (by linarith)
    nlinarith
  have hell : 0 < (targetVisitCost m : ℝ) := by exact_mod_cast targetVisitCost_pos m
  have hnormalized : (K : ℝ) / (targetVisitCost m : ℝ) ≤ coveringGain * (harmonic m : ℝ) / 2 := by
    apply (div_le_iff₀ hell).mpr
    nlinarith
  have hpaid : (t : ℝ) ≤ coveringGain * (harmonic m : ℝ) / 2 := floor_half_gain_ge hb hscale hgain
  have hfirst : (K : ℝ) / (targetVisitCost m : ℝ) -
      (1 - targetCostDiscount) * (harmonic m : ℝ) ≤ -(t : ℝ) := by
    change (K : ℝ) / (targetVisitCost m : ℝ) - coveringGain * (harmonic m : ℝ) ≤ -(t : ℝ)
    linarith
  have hsecond := upperClockSplit_tail_exponent ht n
  have htail := radius_upper_tail_real hm hK (n := n)
  have hsum :
      Real.exp ((K : ℝ) / (targetVisitCost m : ℝ) - (1 - targetCostDiscount) * (harmonic m : ℝ)) +
        Real.exp (-((K - 1 : ℕ) : ℝ) / (100 * Real.log ((n + 2 : ℕ) : ℝ))) ≤
          Real.exp (-(t : ℝ)) + Real.exp (-(t : ℝ)) :=
    add_le_add (Real.exp_le_exp.mpr hfirst) (Real.exp_le_exp.mpr hsecond)
  have hr : 1 ≤ 2 * m ^ 2 := by
    have hmpos : 0 < m := by dsimp [m]; positivity
    have hp : 0 < 2 * m ^ 2 := by positivity
    omega
  have hthreshold : Real.log (((2 * m ^ 2 : ℕ) : ℝ)) ≤
      (3 * b * Real.log 2) * sqrtLogTime n := log_selected_radius_upper hb hscale
  have hsub := logRadius_upper_event_subset n (2 * m ^ 2) hr
    ((3 * b * Real.log 2) * sqrtLogTime n) hthreshold
  have hmeasure := measureReal_mono (μ := walkLaw) hsub (by finiteness)
  exact (hmeasure.trans (htail.trans hsum)).trans_lt (by linarith)

end Erdos1164
