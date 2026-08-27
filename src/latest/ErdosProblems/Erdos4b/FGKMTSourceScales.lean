/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTGrowingDimension

/-! # The actual source interval dominates every allowed shift -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

def sourceIntervalLength (c : ℝ) (x : ℕ) : ℝ :=
  c * x * Real.log (x : ℝ) * Real.log (Real.log (Real.log (x : ℝ))) /
    Real.log (Real.log (x : ℝ))

theorem eventually_sourceIntervalLength_bounds {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) ≤ sourceIntervalLength c x ∧
      sourceIntervalLength c x ≤ (x : ℝ) * Real.log (x : ℝ) ^ 2 ∧
      (∀ k : ℕ, (k : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) →
        2 * (k : ℝ) ^ 2 * (x : ℝ) ≤ sourceIntervalLength c x) := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  have hlogloglog := Real.tendsto_log_atTop.comp hloglog
  have hsmall := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto
    hlog).def (by positivity : (0 : ℝ) < c / 2)
  filter_upwards [hsmall, hlog.eventually (eventually_ge_atTop (max 1 c)),
    hloglog.eventually (eventually_ge_atTop (1 : ℝ)),
    hlogloglog.eventually (eventually_ge_atTop (1 : ℝ))] with x hs hL hv hw
  let L := Real.log (x : ℝ)
  let v := Real.log L
  let w := Real.log v
  change 1 ≤ v at hv
  change 1 ≤ w at hw
  change ‖v‖ ≤ (c / 2) * ‖L ^ (1 / 2 : ℝ)‖ at hs
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hcL : c ≤ L := (le_max_right _ _).trans hL
  have hLpos : 0 < L := by linarith
  have hvpos : 0 < v := by linarith
  have hsmall' : v ≤ (c / 2) * Real.sqrt L := by
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos hvpos,
      abs_of_nonneg (Real.rpow_nonneg hLpos.le (1 / 2 : ℝ)), Real.sqrt_eq_rpow] using hs
  have hdim {k : ℕ} (hk : (k : ℝ) ≤ L ^ (1 / 10 : ℝ)) :
      (k : ℝ) ^ 2 ≤ Real.sqrt L := by
    calc
      _ ≤ (L ^ (1 / 10 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg k) hk 2
      _ = L ^ (1 / 5 : ℝ) := by
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hLpos.le]
        norm_num
      _ ≤ L ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = _ := Real.sqrt_eq_rpow L |>.symm
  have hshift (k : ℕ) (hk : (k : ℝ) ≤ L ^ (1 / 10 : ℝ)) :
      2 * (k : ℝ) ^ 2 * (x : ℝ) ≤ sourceIntervalLength c x := by
    have hsquare : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt hLpos.le
    have hmul := mul_le_mul (hdim hk) hsmall' hvpos.le (Real.sqrt_nonneg L)
    have hw' : 1 ≤ w := hw
    have hbudget : 2 * (k : ℝ) ^ 2 * v ≤ c * L * w := by
      have hcw : c * L ≤ c * L * w :=
        le_mul_of_one_le_right (mul_nonneg hc.le hLpos.le) hw'
      nlinarith
    change 2 * (k : ℝ) ^ 2 * (x : ℝ) ≤ c * x * L * w / v
    apply (le_div_iff₀ hvpos).mpr
    nlinarith [mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg x)]
  have hone : (1 : ℝ) ≤ L ^ (1 / 10 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hlower : (x : ℝ) ≤ sourceIntervalLength c x := by
    have hh := hshift 1 (by simpa using hone)
    norm_num at hh
    linarith [show (0 : ℝ) ≤ x from Nat.cast_nonneg x]
  have hupper : sourceIntervalLength c x ≤ (x : ℝ) * L ^ 2 := by
    have hwv : w ≤ v := (Real.log_le_sub_one_of_pos hvpos).trans (by linarith)
    change c * x * L * w / v ≤ (x : ℝ) * L ^ 2
    apply (div_le_iff₀ hvpos).mpr
    have h1 := mul_le_mul_of_nonneg_left hwv
      (by positivity : 0 ≤ c * (x : ℝ) * L)
    have h2 := mul_le_mul_of_nonneg_right hcL
      (by positivity : 0 ≤ (x : ℝ) * L * v)
    nlinarith
  exact ⟨hlower, hupper, hshift⟩

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.eventually_sourceIntervalLength_bounds
