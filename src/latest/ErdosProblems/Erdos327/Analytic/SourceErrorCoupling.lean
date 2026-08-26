import ErdosProblems.Erdos327.Analytic.SourceSupportedReduction
import ErdosProblems.Erdos327.Analytic.PowerTail

/-!
# Coupling the source sieve-error tail to the roughness cutoff

The final source construction chooses the roughness cutoff just beyond
the killed dyadic prefix.  The polynomial schedule-error tail then
decays like `J⁻⁵`, while the rough density is bounded below on the scale
`J⁻¹`.  This file makes that compatible choice explicit.
-/

namespace Erdos327.Analytic

open Filter Finset Real Topology

noncomputable section

/-- Roughness cutoff attached to the killed dyadic prefix. -/
def sourceCoupledCutoff (J : ℕ) : ℕ :=
  8 * dyadicScale J + 1

theorem eight_dyadicScale_lt_sourceCoupledCutoff (J : ℕ) :
    8 * dyadicScale J < sourceCoupledCutoff J := by
  unfold sourceCoupledCutoff
  omega

theorem three_le_sourceCoupledCutoff (J : ℕ) :
    3 ≤ sourceCoupledCutoff J := by
  have hpos := dyadicScale_pos J
  unfold sourceCoupledCutoff
  omega

theorem index_le_dyadicScale (J : ℕ) :
    J ≤ dyadicScale J := by
  induction J with
  | zero =>
      simp [dyadicScale]
  | succ J ih =>
      rw [dyadicScale, pow_succ]
      have hpow : 1 ≤ 2 ^ J :=
        Nat.one_le_pow J 2 (by norm_num)
      have ih' : J ≤ 2 ^ J := by
        simpa [dyadicScale] using ih
      omega

theorem tendsto_sourceCoupledCutoff_atTop :
    Tendsto sourceCoupledCutoff atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [eventually_ge_atTop b] with J hJ
  have hpos := dyadicScale_pos J
  have hindex := index_le_dyadicScale J
  unfold sourceCoupledCutoff
  omega

/-- Explicit pointwise `j⁻⁶` majorant for the normalized source
schedule-error profile. -/
theorem sourceScheduledErrorProfile_le_rpow
    (j : ℕ) :
    (((j + 3 : ℕ) : ℝ) ^ 2) /
        (((j + 1 : ℕ) : ℝ) ^ 8) ≤
      9 * (((j + 1 : ℕ) : ℝ) ^ (-6 : ℝ)) := by
  have hx : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  have hnum :
      (((j + 3 : ℕ) : ℝ) ^ 2) ≤
        9 * (((j + 1 : ℕ) : ℝ) ^ 2) := by
    have hlinear :
        ((j + 3 : ℕ) : ℝ) ≤
          3 * ((j + 1 : ℕ) : ℝ) := by
      push_cast
      nlinarith
    nlinarith [sq_nonneg
      (((j + 3 : ℕ) : ℝ) -
        3 * ((j + 1 : ℕ) : ℝ))]
  calc
    (((j + 3 : ℕ) : ℝ) ^ 2) /
          (((j + 1 : ℕ) : ℝ) ^ 8)
        ≤
      (9 * (((j + 1 : ℕ) : ℝ) ^ 2)) /
        (((j + 1 : ℕ) : ℝ) ^ 8) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = 9 * (((j + 1 : ℕ) : ℝ) ^ (-6 : ℝ)) := by
      rw [Real.rpow_neg hx.le]
      norm_num
      field_simp [hx.ne']

/-- Constant in the explicit source schedule-error tail. -/
def sourceErrorTailConstant (K : ℝ) : ℝ :=
  162 * sourceBudgetConstant K * powerTailConstant (-6)

theorem sourceErrorTailConstant_pos (K : ℝ) :
    0 < sourceErrorTailConstant K := by
  unfold sourceErrorTailConstant sourceBudgetConstant
  positivity [powerTailConstant_pos (by norm_num : (-6 : ℝ) < -1)]

/-- Uniform explicit tail bound for the actual source error blocks. -/
theorem sum_sourceScheduledErrorBlockBound_le_rpow
    {J M N : ℕ} {K : ℝ} (hJ : 1 ≤ J) :
    (∑ j ∈ Ico J M,
      sourceScheduledErrorBlockBound N K j) ≤
        sourceErrorTailConstant K * (N : ℝ) *
          (J : ℝ) ^ (-5 : ℝ) := by
  have hprofile :
      (∑ j ∈ Ico J M,
        (((j + 3 : ℕ) : ℝ) ^ 2) /
          (((j + 1 : ℕ) : ℝ) ^ 8)) ≤
        9 * powerTailConstant (-6) *
          (J : ℝ) ^ (-5 : ℝ) := by
    calc
      (∑ j ∈ Ico J M,
          (((j + 3 : ℕ) : ℝ) ^ 2) /
            (((j + 1 : ℕ) : ℝ) ^ 8))
          ≤
        ∑ j ∈ Ico J M,
          9 * (((j + 1 : ℕ) : ℝ) ^ (-6 : ℝ)) := by
            apply sum_le_sum
            intro j hj
            exact sourceScheduledErrorProfile_le_rpow j
      _ =
        9 * (∑ j ∈ Ico J M,
          (((j + 1 : ℕ) : ℝ) ^ (-6 : ℝ))) := by
            rw [mul_sum]
      _ ≤
        9 * (powerTailConstant (-6) *
          (J : ℝ) ^ ((-6 : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left
          (sum_Ico_add_one_rpow_le
            (by norm_num : (-6 : ℝ) < -1) hJ)
          (by norm_num)
      _ =
        9 * powerTailConstant (-6) *
          (J : ℝ) ^ (-5 : ℝ) := by
        norm_num
        ring
  have hfactor0 :
      0 ≤ 18 * (N : ℝ) * sourceBudgetConstant K := by
    unfold sourceBudgetConstant
    positivity
  calc
    (∑ j ∈ Ico J M,
        sourceScheduledErrorBlockBound N K j) =
      (18 * (N : ℝ) * sourceBudgetConstant K) *
        (∑ j ∈ Ico J M,
          (((j + 3 : ℕ) : ℝ) ^ 2) /
            (((j + 1 : ℕ) : ℝ) ^ 8)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      unfold sourceScheduledErrorBlockBound
      ring
    _ ≤
      (18 * (N : ℝ) * sourceBudgetConstant K) *
        (9 * powerTailConstant (-6) *
          (J : ℝ) ^ (-5 : ℝ)) :=
      mul_le_mul_of_nonneg_left hprofile hfactor0
    _ =
      sourceErrorTailConstant K * (N : ℝ) *
        (J : ℝ) ^ (-5 : ℝ) := by
      unfold sourceErrorTailConstant
      ring

/-- The logarithm of the coupled cutoff is at most `(J+4) log 2`. -/
theorem log_sourceCoupledCutoff_le
    (J : ℕ) :
    log (sourceCoupledCutoff J : ℝ) ≤
      ((J + 4 : ℕ) : ℝ) * log 2 := by
  have hupper :
      sourceCoupledCutoff J ≤ 16 * dyadicScale J := by
    unfold sourceCoupledCutoff
    have hpos := dyadicScale_pos J
    omega
  have hleftPos :
      (0 : ℝ) < sourceCoupledCutoff J := by
    exact_mod_cast
      (show 0 < sourceCoupledCutoff J by
        have := three_le_sourceCoupledCutoff J
        omega)
  have hrightPos :
      (0 : ℝ) < 16 * dyadicScale J := by
    exact_mod_cast
      (show 0 < 16 * dyadicScale J by
        have := dyadicScale_pos J
        positivity)
  have hlog :=
    Real.strictMonoOn_log.monotoneOn
      (by simpa only [Set.mem_Ioi] using hleftPos)
      (by simpa only [Set.mem_Ioi] using hrightPos)
      (by exact_mod_cast hupper)
  calc
    log (sourceCoupledCutoff J : ℝ)
        ≤ log (16 * (dyadicScale J : ℝ)) := by
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlog
    _ = ((J + 4 : ℕ) : ℝ) * log 2 := by
      rw [show (16 : ℝ) * (dyadicScale J : ℝ) =
          (2 : ℝ) ^ (J + 4) by
        simp [dyadicScale, pow_add, mul_comm]
        norm_num]
      simp [Real.log_pow]

/-- The explicit error coefficient times the logarithm of the coupled
cutoff tends to zero. -/
theorem tendsto_sourceErrorCoupledProfile (K : ℝ) :
    Tendsto
      (fun J : ℕ ↦
        sourceErrorTailConstant K *
          (J : ℝ) ^ (-5 : ℝ) *
          log (sourceCoupledCutoff J : ℝ))
      atTop (𝓝 0) := by
  have hcast :
      Tendsto (fun J : ℕ ↦ (J : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hrpow :
      Tendsto (fun J : ℕ ↦ (J : ℝ) ^ (-4 : ℝ))
        atTop (𝓝 0) := by
    have h :=
      (tendsto_rpow_neg_atTop (y := (4 : ℝ)) (by norm_num)).comp hcast
    convert h using 1
    funext J
    congr 1
  have hmajor :
      ∀ᶠ J : ℕ in atTop,
        sourceErrorTailConstant K *
            (J : ℝ) ^ (-5 : ℝ) *
            log (sourceCoupledCutoff J : ℝ) ≤
          (5 * log 2 * sourceErrorTailConstant K) *
            (J : ℝ) ^ (-4 : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with J hJ
    have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
    have hlog := log_sourceCoupledCutoff_le J
    have hJ4 :
        ((J + 4 : ℕ) : ℝ) ≤ 5 * (J : ℝ) := by
      exact_mod_cast (show J + 4 ≤ 5 * J by omega)
    have hlog' :
        log (sourceCoupledCutoff J : ℝ) ≤
          5 * (J : ℝ) * log 2 := by
      exact hlog.trans
        (mul_le_mul_of_nonneg_right hJ4
          (log_pos (by norm_num : (1 : ℝ) < 2)).le)
    have hcoef0 :
        0 ≤ sourceErrorTailConstant K * (J : ℝ) ^ (-5 : ℝ) :=
      mul_nonneg (sourceErrorTailConstant_pos K).le
        (Real.rpow_nonneg hJpos.le _)
    have hpowers :
        (J : ℝ) ^ (-5 : ℝ) * (J : ℝ) =
          (J : ℝ) ^ (-4 : ℝ) := by
      calc
        (J : ℝ) ^ (-5 : ℝ) * (J : ℝ) =
            (J : ℝ) ^ (-5 : ℝ) *
              (J : ℝ) ^ (1 : ℝ) := by
                rw [Real.rpow_one]
        _ = (J : ℝ) ^ ((-5 : ℝ) + 1) := by
          rw [Real.rpow_add hJpos]
        _ = (J : ℝ) ^ (-4 : ℝ) := by norm_num
    calc
      sourceErrorTailConstant K *
            (J : ℝ) ^ (-5 : ℝ) *
            log (sourceCoupledCutoff J : ℝ)
          ≤
        sourceErrorTailConstant K *
            (J : ℝ) ^ (-5 : ℝ) *
            (5 * (J : ℝ) * log 2) :=
        mul_le_mul_of_nonneg_left hlog' hcoef0
      _ =
        (5 * log 2 * sourceErrorTailConstant K) *
          (J : ℝ) ^ (-4 : ℝ) := by
        rw [show
          sourceErrorTailConstant K *
                (J : ℝ) ^ (-5 : ℝ) *
                (5 * (J : ℝ) * log 2) =
              (5 * log 2 * sourceErrorTailConstant K) *
                ((J : ℝ) ^ (-5 : ℝ) * (J : ℝ)) by ring,
          hpowers]
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 1] with J hJ
    exact mul_nonneg
      (mul_nonneg (sourceErrorTailConstant_pos K).le
        (Real.rpow_nonneg (by positivity) _))
      (log_nonneg
        (by
          exact_mod_cast
            (show 1 ≤ sourceCoupledCutoff J by
              unfold sourceCoupledCutoff
              omega)))
  · exact hmajor
  · simpa using
      (hrpow.const_mul
        (5 * log 2 * sourceErrorTailConstant K))

/-- For all sufficiently late killed prefixes, the complete schedule
error tail fits its source rough-density allocation at the coupled
cutoff. -/
theorem eventually_sourceScheduledErrorTail_le_roughDensity
    (K : ℝ) :
    ∀ᶠ J : ℕ in atTop, ∀ N M : ℕ,
      (∑ j ∈ Ico J M,
        sourceScheduledErrorBlockBound N K j) ≤
        (N : ℝ) * Erdos327.roughDensity
          (sourceCoupledCutoff J) / 128 := by
  have hthreshold :
      0 < mertensLowerConstant / 128 := by
    positivity [mertensLowerConstant_pos]
  have hsmallStrict :
      ∀ᶠ J : ℕ in atTop,
        sourceErrorTailConstant K *
            (J : ℝ) ^ (-5 : ℝ) *
            log (sourceCoupledCutoff J : ℝ) <
          mertensLowerConstant / 128 :=
    (tendsto_order.1 (tendsto_sourceErrorCoupledProfile K)).2
      _ hthreshold
  have hsmall :
      ∀ᶠ J : ℕ in atTop,
        sourceErrorTailConstant K *
            (J : ℝ) ^ (-5 : ℝ) *
            log (sourceCoupledCutoff J : ℝ) ≤
          mertensLowerConstant / 128 := by
    filter_upwards [hsmallStrict] with J hJ
    exact hJ.le
  filter_upwards [hsmall, eventually_ge_atTop 1] with J hsmallJ hJ
  intro N M
  have hcutoff : 3 ≤ sourceCoupledCutoff J :=
    three_le_sourceCoupledCutoff J
  have hlog :
      0 < log (sourceCoupledCutoff J : ℝ) :=
    log_pos (by
      exact_mod_cast
        (show 1 < sourceCoupledCutoff J by
          have := three_le_sourceCoupledCutoff J
          omega))
  have hcoefficient :
      sourceErrorTailConstant K * (J : ℝ) ^ (-5 : ℝ) ≤
        (mertensLowerConstant /
          log (sourceCoupledCutoff J : ℝ)) / 128 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 128)).2
    apply (le_div_iff₀ hlog).2
    calc
      sourceErrorTailConstant K * (J : ℝ) ^ (-5 : ℝ) *
            128 * log (sourceCoupledCutoff J : ℝ) =
          128 *
            (sourceErrorTailConstant K * (J : ℝ) ^ (-5 : ℝ) *
              log (sourceCoupledCutoff J : ℝ)) := by ring
      _ ≤ 128 * (mertensLowerConstant / 128) :=
        mul_le_mul_of_nonneg_left hsmallJ (by norm_num)
      _ = mertensLowerConstant := by ring
  have hmertens :=
    mertensLowerConstant_div_log_le_roughDensity hcutoff
  calc
    (∑ j ∈ Ico J M,
        sourceScheduledErrorBlockBound N K j)
        ≤
      sourceErrorTailConstant K * (N : ℝ) *
        (J : ℝ) ^ (-5 : ℝ) :=
      sum_sourceScheduledErrorBlockBound_le_rpow hJ
    _ =
      (N : ℝ) *
        (sourceErrorTailConstant K *
          (J : ℝ) ^ (-5 : ℝ)) := by ring
    _ ≤
      (N : ℝ) *
        ((mertensLowerConstant /
          log (sourceCoupledCutoff J : ℝ)) / 128) :=
      mul_le_mul_of_nonneg_left hcoefficient (Nat.cast_nonneg N)
    _ ≤
      (N : ℝ) *
        (Erdos327.roughDensity (sourceCoupledCutoff J) / 128) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hmertens (by norm_num))
        (Nat.cast_nonneg N)
    _ =
      (N : ℝ) *
        Erdos327.roughDensity (sourceCoupledCutoff J) / 128 := by
      ring

end

end Erdos327.Analytic
