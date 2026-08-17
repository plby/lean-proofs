/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Elementary asymptotics for Erdős Problem 54

This file collects the rounding and dyadic estimates used when robust finite
blocks are assembled into one Ramsey-complete set.  Keeping these estimates
separate makes all conversions between real logarithms, natural ceilings,
dyadic scales, and finite sums explicit.
-/

open scoped BigOperators

open Filter

namespace Erdos54

/-! ## The rounded logarithmic block parameter -/

/-- The integer parameter `ceil (6 * log x)` used in the robust-block proof. -/
noncomputable def ceilSixLog (x : ℕ) : ℕ :=
  Nat.ceil (6 * Real.log (x : ℝ))

theorem six_log_le_ceilSixLog (x : ℕ) :
    6 * Real.log (x : ℝ) ≤ (ceilSixLog x : ℝ) := by
  exact Nat.le_ceil _

theorem ceilSixLog_lt_add_one {x : ℕ} (hx : 1 ≤ x) :
    (ceilSixLog x : ℝ) < 6 * Real.log (x : ℝ) + 1 := by
  apply Nat.ceil_lt_add_one
  have hxreal : (1 : ℝ) ≤ x := by exact_mod_cast hx
  exact mul_nonneg (by norm_num) (Real.log_nonneg hxreal)

theorem ceilSixLog_le_floor_add_one {x : ℕ} (hx : 1 ≤ x) :
    ceilSixLog x ≤ Nat.floor (6 * Real.log (x : ℝ)) + 1 := by
  apply Nat.ceil_le.mpr
  have hfloor : 6 * Real.log (x : ℝ) <
      (Nat.floor (6 * Real.log (x : ℝ)) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hxreal : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have _hnonneg : 0 ≤ 6 * Real.log (x : ℝ) :=
    mul_nonneg (by norm_num) (Real.log_nonneg hxreal)
  norm_num only [Nat.cast_add, Nat.cast_one]
  exact hfloor.le

theorem floor_six_log_le_ceilSixLog (x : ℕ) :
    Nat.floor (6 * Real.log (x : ℝ)) ≤ ceilSixLog x := by
  by_cases hx : x = 0
  · simp [hx, ceilSixLog]
  · have hxpos : 0 < x := Nat.pos_of_ne_zero hx
    have hnonneg : 0 ≤ 6 * Real.log (x : ℝ) := by
      have : (1 : ℝ) ≤ x := by exact_mod_cast hxpos
      positivity
    have hfloor : (Nat.floor (6 * Real.log (x : ℝ)) : ℝ) ≤
        6 * Real.log (x : ℝ) := Nat.floor_le hnonneg
    exact_mod_cast hfloor.trans (six_log_le_ceilSixLog x)

theorem ceilSixLog_pos {x : ℕ} (hx : 2 ≤ x) : 0 < ceilSixLog x := by
  apply Nat.ceil_pos.mpr
  have hreal : (1 : ℝ) < x := by exact_mod_cast hx
  exact mul_pos (by norm_num) (Real.log_pos hreal)

theorem one_le_ceilSixLog {x : ℕ} (hx : 2 ≤ x) : 1 ≤ ceilSixLog x :=
  ceilSixLog_pos hx

/-! ## Scaling by two and overlap -/

theorem log_two_le_one : Real.log (2 : ℝ) ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at h ⊢
  linarith

theorem ceilSixLog_two_mul_lt {x : ℕ} (hx : 1 ≤ x) :
    (ceilSixLog (2 * x) : ℝ) < 6 * Real.log (x : ℝ) + 7 := by
  calc
    (ceilSixLog (2 * x) : ℝ) <
        6 * Real.log ((2 * x : ℕ) : ℝ) + 1 :=
      ceilSixLog_lt_add_one (by omega)
    _ = 6 * (Real.log 2 + Real.log (x : ℝ)) + 1 := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) (by positivity)]
    _ ≤ 6 * Real.log (x : ℝ) + 7 := by
      linarith [log_two_le_one]

/-- The exact overlap inequality used for consecutive robust blocks. -/
theorem ceilSixLog_overlap {x : ℕ} (hx : 1 ≤ x)
    (hlog : 2 ≤ Real.log (x : ℝ)) :
    320 * ceilSixLog (2 * x) ≤ 560 * ceilSixLog x := by
  have hupper := ceilSixLog_two_mul_lt hx
  have hlower := six_log_le_ceilSixLog x
  have hreal : (320 : ℝ) * (ceilSixLog (2 * x) : ℝ) <
      560 * (ceilSixLog x : ℝ) := by
    nlinarith
  exact_mod_cast hreal.le

theorem eventually_ceilSixLog_overlap :
    ∀ᶠ x : ℕ in atTop,
      320 * ceilSixLog (2 * x) ≤ 560 * ceilSixLog x := by
  filter_upwards
    [eventually_ge_atTop 1,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (2 : ℝ))]
      with x hx hlog
  exact ceilSixLog_overlap hx hlog

/-! ## Dyadic logarithms and linear size estimates -/

theorem log_two_pow (k : ℕ) :
    Real.log (((2 : ℕ) ^ k : ℕ) : ℝ) = k * Real.log 2 := by
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

theorem log_two_pow_mul {x₀ k : ℕ} (hx₀ : 0 < x₀) :
    Real.log ((((2 : ℕ) ^ k) * x₀ : ℕ) : ℝ) =
      k * Real.log 2 + Real.log (x₀ : ℝ) := by
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Real.log_mul (by positivity) (by exact_mod_cast hx₀.ne'), Real.log_pow]

theorem ceilSixLog_two_pow_le (k : ℕ) :
    ceilSixLog (2 ^ k) ≤ 6 * k := by
  apply Nat.ceil_le.mpr
  rw [log_two_pow]
  push_cast
  have hk : (0 : ℝ) ≤ k := by positivity
  nlinarith [log_two_le_one]

theorem ceilSixLog_two_pow_ge (k : ℕ) :
    4 * k ≤ ceilSixLog (2 ^ k) := by
  have hk : (0 : ℝ) ≤ k := by positivity
  have hreal : ((4 * k : ℕ) : ℝ) ≤
      6 * Real.log (((2 : ℕ) ^ k : ℕ) : ℝ) := by
    rw [log_two_pow]
    push_cast
    nlinarith [Real.log_two_gt_d9]
  exact_mod_cast hreal.trans (six_log_le_ceilSixLog (2 ^ k))

theorem ceilSixLog_two_pow_mul_le {x₀ k : ℕ} (hx₀ : 0 < x₀) :
    ceilSixLog (2 ^ k * x₀) ≤ ceilSixLog x₀ + 6 * k := by
  apply Nat.ceil_le.mpr
  rw [log_two_pow_mul hx₀]
  have hbase := six_log_le_ceilSixLog x₀
  have hk : (0 : ℝ) ≤ k := by positivity
  push_cast
  nlinarith [log_two_le_one]

/-- A floor-safe form convenient when a real logarithmic cutoff is first
converted to a natural dyadic index. -/
theorem floor_log_two_pow_le (k : ℕ) :
    Nat.floor (6 * Real.log (((2 : ℕ) ^ k : ℕ) : ℝ)) ≤ 6 * k := by
  let y : ℝ := 6 * Real.log (((2 : ℕ) ^ k : ℕ) : ℝ)
  have hnonneg : 0 ≤ y := by
    dsimp [y]
    positivity
  have hfloor : (Nat.floor y : ℝ) ≤ y := Nat.floor_le hnonneg
  have hupper : y ≤ ((6 * k : ℕ) : ℝ) := by
    dsimp [y]
    rw [log_two_pow]
    push_cast
    have hk : (0 : ℝ) ≤ k := by positivity
    nlinarith [log_two_le_one]
  exact_mod_cast hfloor.trans hupper

/-- A family of block sizes bounded by `d * (c + 6*k)` has a quadratic
prefix bound.  No disjointness hypothesis is needed for this arithmetic
estimate. -/
theorem sum_linear_block_sizes_le_sq
    (d c m : ℕ) (f : ℕ → ℕ)
    (hf : ∀ k ∈ Finset.range (m + 1), f k ≤ d * (c + 6 * k)) :
    ∑ k ∈ Finset.range (m + 1), f k ≤
      d * (c + 6) * (m + 1) ^ 2 := by
  calc
    ∑ k ∈ Finset.range (m + 1), f k ≤
        ∑ k ∈ Finset.range (m + 1), d * (c + 6 * k) := by
      exact Finset.sum_le_sum hf
    _ ≤ ∑ _k ∈ Finset.range (m + 1), d * (c + 6 * m) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkm : k ≤ m := by
        have := Finset.mem_range.mp hk
        omega
      exact Nat.mul_le_mul_left d (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hkm) c)
    _ ≤ d * (c + 6) * (m + 1) ^ 2 := by
      rw [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
      have hc : c ≤ c * (m + 1) := by
        calc
          c = c * 1 := by simp
          _ ≤ c * (m + 1) :=
            Nat.mul_le_mul_left c (Nat.succ_le_succ (Nat.zero_le m))
      have hcm : c + 6 * m ≤ (c + 6) * (m + 1) := by
        calc
          c + 6 * m ≤ c * (m + 1) + 6 * m := Nat.add_le_add_right hc _
          _ ≤ c * (m + 1) + 6 * (m + 1) :=
            Nat.add_le_add_left (Nat.mul_le_mul_left 6 (Nat.le_succ m)) _
          _ = (c + 6) * (m + 1) := by ring
      calc
        (m + 1) * (d * (c + 6 * m)) = d * (m + 1) * (c + 6 * m) := by ring
        _ ≤ d * (m + 1) * ((c + 6) * (m + 1)) :=
          Nat.mul_le_mul_left (d * (m + 1)) hcm
        _ = d * (c + 6) * (m + 1) ^ 2 := by ring

theorem sum_ceilSixLog_dyadic_le_sq (x₀ d m : ℕ) (hx₀ : 0 < x₀) :
    ∑ k ∈ Finset.range (m + 1), d * ceilSixLog (2 ^ k * x₀) ≤
      d * (ceilSixLog x₀ + 6) * (m + 1) ^ 2 := by
  apply sum_linear_block_sizes_le_sq d (ceilSixLog x₀) m
      (fun k ↦ d * ceilSixLog (2 ^ k * x₀))
  intro k hk
  exact Nat.mul_le_mul_left d (ceilSixLog_two_pow_mul_le hx₀)

/-! ## Endpoints tend to infinity -/

theorem ceilSixLog_eventually_one_le :
    ∀ᶠ x : ℕ in atTop, 1 ≤ ceilSixLog x := by
  filter_upwards [eventually_ge_atTop 2] with x hx
  exact one_le_ceilSixLog hx

theorem lowerEndpoint_tendsto_atTop :
    Tendsto (fun x : ℕ ↦ 160 * ceilSixLog x * x) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ tendsto_id
  filter_upwards [ceilSixLog_eventually_one_le] with x hx
  calc
    x = 1 * x := by simp
    _ ≤ (160 * ceilSixLog x) * x :=
      Nat.mul_le_mul_right x (by nlinarith)
    _ = 160 * ceilSixLog x * x := by ring

theorem dyadicLowerEndpoint_tendsto_atTop (x₀ : ℕ) (hx₀ : 0 < x₀) :
    Tendsto (fun k : ℕ ↦ 160 * ceilSixLog (2 ^ k * x₀) * (2 ^ k * x₀))
      atTop atTop := by
  have hpow : Tendsto (fun k : ℕ ↦ 2 ^ k * x₀) atTop atTop := by
    exact (tendsto_pow_atTop_atTop_of_one_lt
      (by norm_num : 1 < (2 : ℕ))).atTop_mul_const' hx₀
  exact lowerEndpoint_tendsto_atTop.comp hpow

end Erdos54
