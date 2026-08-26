/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import ErdosProblems.Erdos730.Mertens
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Erdős 730: reciprocal-prime bands

This file isolates the Mertens component of the first-power argument.  It
contains no digit or Fourier counting: only reciprocal-prime sums over the
fixed-depth bands and over the transition band.
-/

open Filter Finset
open scoped Topology

namespace Erdos730.FullDensity

/-- Lower endpoint `X^(1/(r+2))` of the depth-`r` prime band. -/
noncomputable def fixedDepthPrimeBandLower (r : ℕ) (X : ℝ) : ℝ :=
  X ^ (((r + 2 : ℕ) : ℝ)⁻¹)

/-- Upper endpoint `X^(1/(r+1))` of the depth-`r` prime band. -/
noncomputable def fixedDepthPrimeBandUpper (r : ℕ) (X : ℝ) : ℝ :=
  X ^ (((r + 1 : ℕ) : ℝ)⁻¹)

/-- Reciprocal-prime mass in the depth-`r` band.  The real-cutoff sum uses
natural floors, so this is exactly the sum over
`X^(1/(r+2)) < p ≤ X^(1/(r+1))`. -/
noncomputable def fixedDepthReciprocalPrimeBand (r : ℕ) (X : ℝ) : ℝ :=
  reciprocalPrimeSumReal (fixedDepthPrimeBandUpper r X) -
    reciprocalPrimeSumReal (fixedDepthPrimeBandLower r X)

/-- The limiting reciprocal-prime mass of the depth-`r` band. -/
noncomputable def fixedDepthPrimeBandMainTerm (r : ℕ) : ℝ :=
  Real.log (((r + 2 : ℕ) : ℝ) / ((r + 1 : ℕ) : ℝ))

lemma fixedDepthPrimeBandLower_pos (r : ℕ) {X : ℝ} (hX : 0 < X) :
    0 < fixedDepthPrimeBandLower r X := by
  exact Real.rpow_pos_of_pos hX _

lemma fixedDepthPrimeBandUpper_pos (r : ℕ) {X : ℝ} (hX : 0 < X) :
    0 < fixedDepthPrimeBandUpper r X := by
  exact Real.rpow_pos_of_pos hX _

lemma log_fixedDepthPrimeBandLower (r : ℕ) {X : ℝ} (hX : 0 < X) :
    Real.log (fixedDepthPrimeBandLower r X) =
      (((r + 2 : ℕ) : ℝ)⁻¹) * Real.log X := by
  exact Real.log_rpow hX _

lemma log_fixedDepthPrimeBandUpper (r : ℕ) {X : ℝ} (hX : 0 < X) :
    Real.log (fixedDepthPrimeBandUpper r X) =
      (((r + 1 : ℕ) : ℝ)⁻¹) * Real.log X := by
  exact Real.log_rpow hX _

lemma fixedDepthPrimeBandLower_le_upper (r : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    fixedDepthPrimeBandLower r X ≤ fixedDepthPrimeBandUpper r X := by
  apply Real.rpow_le_rpow_of_exponent_le hX
  apply (inv_le_inv₀ (by positivity) (by positivity)).2
  norm_num

/-- The logarithmic main terms telescope to the paper's band constant. -/
theorem fixedDepthPrimeBand_loglog_sub_eq (r : ℕ) {X : ℝ} (hX : 1 < X) :
    Real.log (Real.log (fixedDepthPrimeBandUpper r X)) -
        Real.log (Real.log (fixedDepthPrimeBandLower r X)) =
      fixedDepthPrimeBandMainTerm r := by
  rw [log_fixedDepthPrimeBandUpper r (zero_lt_one.trans hX),
    log_fixedDepthPrimeBandLower r (zero_lt_one.trans hX)]
  have hlog : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  have hr1 : (((r + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hr2 : (((r + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [← Real.log_div (mul_ne_zero (inv_ne_zero hr1) hlog)
    (mul_ne_zero (inv_ne_zero hr2) hlog)]
  unfold fixedDepthPrimeBandMainTerm
  congr 1
  field_simp

/-- Quantitative fixed-depth band estimate from an arbitrary reciprocal-prime
Mertens coefficient `C`.  The factor `2r+3` is the exact sum of the two
endpoint factors `r+1` and `r+2`. -/
theorem fixedDepthReciprocalPrimeBand_sub_main_abs_le_of_bound
    (r : ℕ) {M C X : ℝ} (hX : 1 < X)
    (hlower : 2 ≤ fixedDepthPrimeBandLower r X)
    (hMertens : ∀ x : ℝ, 2 ≤ x →
      |reciprocalPrimeSumReal x - Real.log (Real.log x) - M| ≤
        C / Real.log x) :
    |fixedDepthReciprocalPrimeBand r X -
        fixedDepthPrimeBandMainTerm r| ≤
      C * (((2 * r + 3 : ℕ) : ℝ)) / Real.log X := by
  have hupper : 2 ≤ fixedDepthPrimeBandUpper r X :=
    hlower.trans (fixedDepthPrimeBandLower_le_upper r hX.le)
  have hlowError := hMertens (fixedDepthPrimeBandLower r X) hlower
  have huppError := hMertens (fixedDepthPrimeBandUpper r X) hupper
  have hlog : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  have hr1 : (((r + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hr2 : (((r + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hrewrite :
      fixedDepthReciprocalPrimeBand r X -
          fixedDepthPrimeBandMainTerm r =
        (reciprocalPrimeSumReal (fixedDepthPrimeBandUpper r X) -
            Real.log (Real.log (fixedDepthPrimeBandUpper r X)) - M) -
          (reciprocalPrimeSumReal (fixedDepthPrimeBandLower r X) -
            Real.log (Real.log (fixedDepthPrimeBandLower r X)) - M) := by
    unfold fixedDepthReciprocalPrimeBand
    rw [← fixedDepthPrimeBand_loglog_sub_eq r hX]
    ring
  rw [hrewrite]
  calc
    |(reciprocalPrimeSumReal (fixedDepthPrimeBandUpper r X) -
          Real.log (Real.log (fixedDepthPrimeBandUpper r X)) - M) -
        (reciprocalPrimeSumReal (fixedDepthPrimeBandLower r X) -
          Real.log (Real.log (fixedDepthPrimeBandLower r X)) - M)| ≤
        |reciprocalPrimeSumReal (fixedDepthPrimeBandUpper r X) -
          Real.log (Real.log (fixedDepthPrimeBandUpper r X)) - M| +
        |reciprocalPrimeSumReal (fixedDepthPrimeBandLower r X) -
          Real.log (Real.log (fixedDepthPrimeBandLower r X)) - M| :=
      abs_sub _ _
    _ ≤ C / Real.log (fixedDepthPrimeBandUpper r X) +
        C / Real.log (fixedDepthPrimeBandLower r X) :=
      add_le_add huppError hlowError
    _ = C * (((2 * r + 3 : ℕ) : ℝ)) / Real.log X := by
      rw [log_fixedDepthPrimeBandUpper r (zero_lt_one.trans hX),
        log_fixedDepthPrimeBandLower r (zero_lt_one.trans hX)]
      field_simp
      push_cast
      ring

/-- Uniform upper bound in the rounded form used in equation (44): replacing
the paper's numerical Mertens coefficient `4` by an arbitrary positive `C`
replaces `8(r+2)/log X` by `2C(r+2)/log X`. -/
theorem fixedDepthReciprocalPrimeBand_le_of_bound
    (r : ℕ) {M C X : ℝ} (hC : 0 ≤ C) (hX : 1 < X)
    (hlower : 2 ≤ fixedDepthPrimeBandLower r X)
    (hMertens : ∀ x : ℝ, 2 ≤ x →
      |reciprocalPrimeSumReal x - Real.log (Real.log x) - M| ≤
        C / Real.log x) :
    fixedDepthReciprocalPrimeBand r X ≤
      fixedDepthPrimeBandMainTerm r +
        2 * C * (((r + 2 : ℕ) : ℝ)) / Real.log X := by
  have habs := fixedDepthReciprocalPrimeBand_sub_main_abs_le_of_bound
    r hX hlower hMertens
  have hsub := (le_abs_self
    (fixedDepthReciprocalPrimeBand r X -
      fixedDepthPrimeBandMainTerm r)).trans habs
  have hlog : 0 < Real.log X := Real.log_pos hX
  have hcoeff :
      C * (((2 * r + 3 : ℕ) : ℝ)) / Real.log X ≤
        2 * C * (((r + 2 : ℕ) : ℝ)) / Real.log X := by
    apply div_le_div_of_nonneg_right _ hlog.le
    push_cast
    nlinarith
  linarith

/-- Unconditional quantitative form of the fixed-depth band estimate. -/
theorem fixedDepthReciprocalPrimeBand_le
    (r : ℕ) {X : ℝ} (hX : 1 < X)
    (hlower : 2 ≤ fixedDepthPrimeBandLower r X) :
    fixedDepthReciprocalPrimeBand r X ≤
      fixedDepthPrimeBandMainTerm r +
        2 * reciprocalPrimeMertensErrorConstant *
          (((r + 2 : ℕ) : ℝ)) / Real.log X := by
  refine fixedDepthReciprocalPrimeBand_le_of_bound
    (M := reciprocalPrimeMertensConstant)
    (C := reciprocalPrimeMertensErrorConstant) r
    reciprocalPrimeMertensErrorConstant_pos.le hX hlower ?_
  intro x hx
  simpa only [reciprocalPrimeMertensError] using
    reciprocalPrimeMertensError_abs_le hx

/-- The Mertens error itself tends to zero. -/
theorem tendsto_reciprocalPrimeMertensError_atTop :
    Tendsto reciprocalPrimeMertensError atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall fun X ↦ abs_nonneg _
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
    exact reciprocalPrimeMertensError_abs_le hX
  · simpa [div_eq_mul_inv] using
      Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul
        reciprocalPrimeMertensErrorConstant

/-- Fixed-depth Mertens component of equation (42). -/
theorem tendsto_fixedDepthReciprocalPrimeBand (r : ℕ) :
    Tendsto (fixedDepthReciprocalPrimeBand r) atTop
      (𝓝 (fixedDepthPrimeBandMainTerm r)) := by
  have hlowerTop : Tendsto (fixedDepthPrimeBandLower r) atTop atTop := by
    exact tendsto_rpow_atTop (by positivity)
  have hupperTop : Tendsto (fixedDepthPrimeBandUpper r) atTop atTop := by
    exact tendsto_rpow_atTop (by positivity)
  have hlowerError := tendsto_reciprocalPrimeMertensError_atTop.comp hlowerTop
  have hupperError := tendsto_reciprocalPrimeMertensError_atTop.comp hupperTop
  have hlim := (hupperError.sub hlowerError).add
    (tendsto_const_nhds : Tendsto
      (fun _ : ℝ ↦ fixedDepthPrimeBandMainTerm r) atTop
      (𝓝 (fixedDepthPrimeBandMainTerm r)))
  have hlim' : Tendsto
      (fun X : ℝ ↦
        reciprocalPrimeMertensError (fixedDepthPrimeBandUpper r X) -
          reciprocalPrimeMertensError (fixedDepthPrimeBandLower r X) +
            fixedDepthPrimeBandMainTerm r)
      atTop (𝓝 (fixedDepthPrimeBandMainTerm r)) := by
    simpa only [Function.comp_apply, sub_zero, zero_add] using hlim
  apply hlim'.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  unfold fixedDepthReciprocalPrimeBand reciprocalPrimeMertensError
  rw [← fixedDepthPrimeBand_loglog_sub_eq r hX]
  ring

/-- Natural-parameter form of the fixed-depth band limit. -/
theorem tendsto_fixedDepthReciprocalPrimeBand_nat (r : ℕ) :
    Tendsto (fun X : ℕ ↦ fixedDepthReciprocalPrimeBand r (X : ℝ))
      atTop (𝓝 (fixedDepthPrimeBandMainTerm r)) :=
  (tendsto_fixedDepthReciprocalPrimeBand r).comp
    tendsto_natCast_atTop_atTop

/-! ## Transition band -/

/-- Lower endpoint `sqrt X` of the transition band. -/
noncomputable def transitionPrimeBandLower (X : ℝ) : ℝ :=
  Real.sqrt X

/-- Upper endpoint `Y = sqrt X * (log X)^2` of the transition band. -/
noncomputable def transitionPrimeBandUpper (X : ℝ) : ℝ :=
  Real.sqrt X * Real.log X ^ 2

/-- Reciprocal-prime mass in `sqrt X < p ≤ sqrt X * (log X)^2`. -/
noncomputable def transitionReciprocalPrimeBand (X : ℝ) : ℝ :=
  reciprocalPrimeSumReal (transitionPrimeBandUpper X) -
    reciprocalPrimeSumReal (transitionPrimeBandLower X)

lemma log_transitionPrimeBandLower {X : ℝ} (hX : 0 ≤ X) :
    Real.log (transitionPrimeBandLower X) = Real.log X / 2 := by
  exact Real.log_sqrt hX

lemma log_transitionPrimeBandUpper {X : ℝ} (hX : 1 < X) :
    Real.log (transitionPrimeBandUpper X) =
      Real.log X / 2 + 2 * Real.log (Real.log X) := by
  have hsqrt : Real.sqrt X ≠ 0 := (Real.sqrt_pos.2 (zero_lt_one.trans hX)).ne'
  have hlog : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  rw [transitionPrimeBandUpper, Real.log_mul hsqrt (pow_ne_zero 2 hlog),
    Real.log_sqrt (zero_lt_one.trans hX).le, Real.log_pow]
  norm_num

/-- Exact transition-band logarithmic ratio, stated in the eventual range
where both inner logarithms are positive. -/
theorem transitionPrimeBand_loglog_sub_eq {X : ℝ}
    (hX : Real.exp 1 < X) :
    Real.log (Real.log (transitionPrimeBandUpper X)) -
        Real.log (Real.log (transitionPrimeBandLower X)) =
      Real.log
        (1 + 4 * Real.log (Real.log X) / Real.log X) := by
  have hexp : 1 < Real.exp 1 := by
    simpa only [Real.exp_zero] using
      (Real.exp_lt_exp.mpr (zero_lt_one : (0 : ℝ) < 1))
  have hX1 : 1 < X := hexp.trans hX
  have hlog : 0 < Real.log X := Real.log_pos hX1
  have honeLog : 1 < Real.log X := by
    apply Real.exp_lt_exp.mp
    simpa [Real.exp_log (zero_lt_one.trans hX1)] using hX
  have hlowerLog : 0 < Real.log (transitionPrimeBandLower X) := by
    rw [log_transitionPrimeBandLower (zero_lt_one.trans hX1).le]
    positivity
  have hupperLog : 0 < Real.log (transitionPrimeBandUpper X) := by
    rw [log_transitionPrimeBandUpper hX1]
    have hloglog : 0 < Real.log (Real.log X) := Real.log_pos honeLog
    positivity
  rw [← Real.log_div hupperLog.ne' hlowerLog.ne',
    log_transitionPrimeBandUpper hX1,
    log_transitionPrimeBandLower (zero_lt_one.trans hX1).le]
  congr 1
  field_simp [hlog.ne']
  ring

private theorem tendsto_log_log_div_log_atTop :
    Tendsto (fun X : ℝ ↦ Real.log (Real.log X) / Real.log X)
      atTop (𝓝 0) := by
  simpa using!
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      Real.tendsto_log_atTop

/-- The logarithmic main term of the transition band tends to zero. -/
theorem tendsto_transitionPrimeBand_loglog_sub :
    Tendsto (fun X : ℝ ↦
      Real.log (Real.log (transitionPrimeBandUpper X)) -
        Real.log (Real.log (transitionPrimeBandLower X)))
      atTop (𝓝 0) := by
  have hinside : Tendsto
      (fun X : ℝ ↦
        1 + 4 * Real.log (Real.log X) / Real.log X)
      atTop (𝓝 1) := by
    simpa only [mul_div_assoc, mul_zero, add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (𝓝 1)).add
        (tendsto_log_log_div_log_atTop.const_mul 4)
  have hlog : Tendsto
      (fun X : ℝ ↦
        Real.log (1 + 4 * Real.log (Real.log X) / Real.log X))
      atTop (𝓝 0) := by
    simpa using! (Real.continuousAt_log one_ne_zero).tendsto.comp hinside
  apply hlog.congr'
  filter_upwards [eventually_gt_atTop (Real.exp 1)] with X hX
  exact (transitionPrimeBand_loglog_sub_eq hX).symm

/-- The reciprocal-prime transition band for
`Y = sqrt X * (log X)^2` has asymptotically zero mass. -/
theorem tendsto_transitionReciprocalPrimeBand :
    Tendsto transitionReciprocalPrimeBand atTop (𝓝 0) := by
  have hlowerTop : Tendsto transitionPrimeBandLower atTop atTop := by
    exact Real.tendsto_sqrt_atTop
  have hlogSqTop : Tendsto (fun X : ℝ ↦ Real.log X ^ 2)
      atTop atTop := by
    exact (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      Real.tendsto_log_atTop
  have hupperTop : Tendsto transitionPrimeBandUpper atTop atTop := by
    exact hlowerTop.atTop_mul_atTop₀ hlogSqTop
  have hlowerError := tendsto_reciprocalPrimeMertensError_atTop.comp hlowerTop
  have hupperError := tendsto_reciprocalPrimeMertensError_atTop.comp hupperTop
  have hlim := (hupperError.sub hlowerError).add
    tendsto_transitionPrimeBand_loglog_sub
  have hlim' : Tendsto
      (fun X : ℝ ↦
        reciprocalPrimeMertensError (transitionPrimeBandUpper X) -
          reciprocalPrimeMertensError (transitionPrimeBandLower X) +
            (Real.log (Real.log (transitionPrimeBandUpper X)) -
              Real.log (Real.log (transitionPrimeBandLower X))))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_zero, zero_add] using hlim
  apply hlim'.congr'
  filter_upwards with X
  unfold transitionReciprocalPrimeBand reciprocalPrimeMertensError
  ring

/-- Natural-parameter transition-band limit used by the counting argument. -/
theorem tendsto_transitionReciprocalPrimeBand_nat :
    Tendsto (fun X : ℕ ↦ transitionReciprocalPrimeBand (X : ℝ))
      atTop (𝓝 0) :=
  tendsto_transitionReciprocalPrimeBand.comp tendsto_natCast_atTop_atTop

end Erdos730.FullDensity
