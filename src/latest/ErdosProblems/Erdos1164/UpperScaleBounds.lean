import ErdosProblems.Erdos1164.DyadicScales

/-! # Quantitative scale inequalities for the upper probability tail -/

namespace Erdos1164

noncomputable def coveringGain : ℝ := 1 - targetCostDiscount

theorem coveringGain_pos : 0 < coveringGain := sub_pos.mpr targetCostDiscount_lt_one

/-- A visit threshold proportional to the logarithm of time. -/
noncomputable def upperClockSplit (t n : ℕ) : ℕ :=
  ⌈100 * (t : ℝ) * Real.log ((n + 2 : ℕ) : ℝ)⌉₊ + 1

theorem upperClockSplit_ge_two {t : ℕ} (ht : 1 ≤ t) (n : ℕ) : 2 ≤ upperClockSplit t n := by
  have hlog : 0 < Real.log ((n + 2 : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n + 2))
  have htpos : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hceil : 1 ≤ ⌈100 * (t : ℝ) * Real.log ((n + 2 : ℕ) : ℝ)⌉₊ :=
    Nat.one_le_ceil_iff.mpr (by positivity)
  unfold upperClockSplit
  omega

theorem upperClockSplit_tail_exponent {t : ℕ} (ht : 1 ≤ t) (n : ℕ) :
    -((upperClockSplit t n - 1 : ℕ) : ℝ) / (100 * Real.log ((n + 2 : ℕ) : ℝ)) ≤ -(t : ℝ) := by
  have hlog : 0 < Real.log ((n + 2 : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n + 2))
  have hceil := Nat.le_ceil (100 * (t : ℝ) * Real.log ((n + 2 : ℕ) : ℝ))
  simp only [upperClockSplit, Nat.add_sub_cancel]
  apply (div_le_iff₀ (by positivity : 0 < 100 * Real.log ((n + 2 : ℕ) : ℝ))).mpr
  nlinarith

theorem log_time_add_two_le {n : ℕ} (hn : 2 ≤ n) :
    Real.log ((n + 2 : ℕ) : ℝ) ≤ 2 * Real.log (n : ℝ) := by
  have hnat : n + 2 ≤ n ^ 2 := by nlinarith
  have h := Real.log_le_log (by positivity : (0 : ℝ) < ((n + 2 : ℕ) : ℝ))
    (show ((n + 2 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 by exact_mod_cast hnat)
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

theorem upperClockSplit_le {t n : ℕ} (ht : 1 ≤ t) (hn : 2 ≤ n)
    (hlog : 1 ≤ Real.log (n : ℝ)) :
    (upperClockSplit t n : ℝ) ≤ 400 * (t : ℝ) * Real.log (n : ℝ) := by
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hlog2 : 0 ≤ Real.log ((n + 2 : ℕ) : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n + 2))
  have hceil := Nat.ceil_lt_add_one
    (by positivity : 0 ≤ 100 * (t : ℝ) * Real.log ((n + 2 : ℕ) : ℝ))
  have hlogs := mul_le_mul_of_nonneg_left (log_time_add_two_le hn) (by positivity : (0 : ℝ) ≤ 100 * t)
  have hprod : 1 ≤ (t : ℝ) * Real.log (n : ℝ) := one_le_mul_of_one_le_of_one_le htR hlog
  unfold upperClockSplit
  rw [Nat.cast_add, Nat.cast_one]
  nlinarith

theorem floor_scale_bounds {b : ℝ} (hb : 0 < b) {n : ℕ} (hscale : 2 ≤ b * sqrtLogTime n) :
    b * sqrtLogTime n / 2 ≤ (⌊b * sqrtLogTime n⌋₊ : ℝ) ∧
      (⌊b * sqrtLogTime n⌋₊ : ℝ) ≤ b * sqrtLogTime n := by
  have hfloor := Nat.lt_floor_add_one (b * sqrtLogTime n)
  exact ⟨by linarith, Nat.floor_le (by positivity)⟩

theorem harmonic_dyadic_lower (j : ℕ) : (j : ℝ) * Real.log 2 ≤ (harmonic (2 ^ j) : ℝ) := by
  rw [← log_dyadic]
  have hlog : Real.log ((2 ^ j : ℕ) : ℝ) ≤ Real.log (((2 ^ j + 1 : ℕ) : ℝ)) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (Nat.le_succ (2 ^ j)))
  exact hlog.trans (log_add_one_le_harmonic (2 ^ j))

theorem dyadic_largeTargetScale {j : ℕ} (hj : 4 ≤ j)
    (hs : 1000 * potentialError ≤ potentialSlope * (j : ℝ) * Real.log 2) :
    LargeTargetScale (2 ^ j) := by
  refine ⟨(by omega : 4 ≤ j + 1).trans (dyadic_ge_index j), ?_⟩
  unfold spatialLogScale
  rw [log_dyadic]
  nlinarith

/-- A dyadic selected set provides a squared-logarithmic total cost scale. -/
theorem dyadic_cover_cost_product {b : ℝ} (hb : 0 < b) {n : ℕ} (hn : 1 ≤ n)
    (hscale : 2 ≤ b * sqrtLogTime n) :
    potentialSlope * coveringGain * b ^ 2 * Real.log 2 ^ 2 * Real.log (n : ℝ) / 16 ≤
      (targetVisitCost (2 ^ ⌊b * sqrtLogTime n⌋₊) : ℝ) * coveringGain *
        (harmonic (2 ^ ⌊b * sqrtLogTime n⌋₊) : ℝ) / 2 := by
  let j := ⌊b * sqrtLogTime n⌋₊
  let v : ℝ := (j : ℝ) * Real.log 2
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hj := (floor_scale_bounds hb hscale).1
  have hvl : b * sqrtLogTime n * Real.log 2 / 2 ≤ v := by
    have h := mul_le_mul_of_nonneg_right hj log_two_pos.le
    dsimp only [v, j]
    nlinarith
  have hsq : (b * sqrtLogTime n * Real.log 2 / 2) ^ 2 ≤ v ^ 2 := by
    have hnon : 0 ≤ b * sqrtLogTime n * Real.log 2 / 2 := by positivity
    nlinarith
  have hell := targetVisitCost_lower (2 ^ j)
  have hH := harmonic_dyadic_lower j
  have hell' : potentialSlope * v / 2 ≤ (targetVisitCost (2 ^ j) : ℝ) := by
    simpa only [spatialLogScale, log_dyadic, v, mul_assoc] using hell
  have hprod : (potentialSlope * v / 2) * v ≤
      (targetVisitCost (2 ^ j) : ℝ) * (harmonic (2 ^ j) : ℝ) :=
    mul_le_mul hell' hH hv (by positivity)
  have hmult := mul_le_mul_of_nonneg_left hprod (show 0 ≤ coveringGain / 2 by exact div_nonneg coveringGain_pos.le (by norm_num))
  have hsqmult := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ potentialSlope * coveringGain / 4 by exact div_nonneg (mul_nonneg potentialSlope_pos.le coveringGain_pos.le) (by norm_num))
  have heq : (potentialSlope * coveringGain / 4) *
      (b * sqrtLogTime n * Real.log 2 / 2) ^ 2 =
      potentialSlope * coveringGain * b ^ 2 * Real.log 2 ^ 2 * Real.log (n : ℝ) / 16 := by
    rw [show (b * sqrtLogTime n * Real.log 2 / 2) ^ 2 =
      b ^ 2 * Real.log 2 ^ 2 * sqrtLogTime n ^ 2 / 4 by ring, sqrtLogTime_sq hn]
    ring
  rw [heq] at hsqmult
  change _ ≤ (targetVisitCost (2 ^ j) : ℝ) * coveringGain * (harmonic (2 ^ j) : ℝ) / 2
  nlinarith

theorem log_selected_radius_upper {b : ℝ} (hb : 0 < b) {n : ℕ}
    (hscale : 2 ≤ b * sqrtLogTime n) :
    Real.log (((2 * (2 ^ ⌊b * sqrtLogTime n⌋₊) ^ 2 : ℕ) : ℝ)) ≤
      (3 * b * Real.log 2) * sqrtLogTime n := by
  let j := ⌊b * sqrtLogTime n⌋₊
  have hj := (floor_scale_bounds hb hscale).2
  have heq : (2 * (2 ^ j) ^ 2 : ℕ) = 2 ^ (j * 2 + 1) := by
    rw [pow_add, pow_mul, pow_one]
    ac_rfl
  change Real.log (((2 * (2 ^ j) ^ 2 : ℕ) : ℝ)) ≤ _
  rw [heq, log_dyadic]
  push_cast
  have hmul := mul_le_mul_of_nonneg_right
    (by nlinarith : 2 * (j : ℝ) + 1 ≤ 3 * b * sqrtLogTime n) log_two_pos.le
  nlinarith

end Erdos1164
