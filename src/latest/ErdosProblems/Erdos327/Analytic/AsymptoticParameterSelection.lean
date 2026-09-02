import ErdosProblems.Erdos327.Analytic.LogPowerAsymptotics
import ErdosProblems.Erdos327.Analytic.ScheduledReduction
import ErdosProblems.Erdos327.Analytic.RoughCount

/-!
# Asymptotic parameter selection

This file formalizes the order of choices used in the paper.  The key
input is the explicit lower Mertens bound
`mertensLowerConstant / log L ≤ roughDensity L`.
-/

namespace Erdos327.Analytic

open Filter Real Topology

noncomputable section

/-- Slope of the odd regularity intercept as a function of the roughness
cutoff. -/
def oddBudgetSlope : ℝ := 3.3912

/-- The real-valued odd regularity intercept.  Using a real intercept avoids
an irrelevant ceiling loss. -/
def oddBudget (L : ℕ) : ℝ :=
  oddBudgetSlope * log (log L)

/-- A general selection lemma: any fixed multiple of
`(log L)^(-η) (log log L)^m` is eventually smaller than the rough density
provided `η > 1`. -/
theorem eventually_const_mul_log_rpow_neg_mul_loglog_rpow_le_roughDensity
    {C D η m : ℝ} (_hC : 0 ≤ C) (hD : 0 < D) (hη : 1 < η) :
    ∀ᶠ L : ℕ in atTop,
      C * log (L : ℝ) ^ (-η) * log (log (L : ℝ)) ^ m ≤
        Erdos327.roughDensity L / D := by
  have hgap : 0 < η - 1 := sub_pos.mpr hη
  have htReal :=
    (tendsto_log_rpow_neg_mul_loglog_rpow_atTop hgap m).const_mul
      (D * C)
  have hcast :
      Tendsto (fun L : ℕ ↦ (L : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have htComp := htReal.comp hcast
  have hsmallComp :
      ∀ᶠ L : ℕ in atTop,
        ((fun x : ℝ ↦
          (D * C) * (log x ^ (-(η - 1)) *
            log (log x) ^ m)) ∘
          (fun L : ℕ ↦ (L : ℝ))) L <
            mertensLowerConstant :=
    (tendsto_order.1 htComp).2 _
      (by simpa using mertensLowerConstant_pos)
  have hsmall :
      ∀ᶠ L : ℕ in atTop,
        (D * C) * (log (L : ℝ) ^ (1 - η) *
          log (log (L : ℝ)) ^ m) <
            mertensLowerConstant := by
    simpa only [Function.comp_apply, neg_sub] using hsmallComp
  filter_upwards [hsmall, eventually_ge_atTop 3] with L hsmallL hL
  have hlog : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hmertens :=
    mertensLowerConstant_div_log_le_roughDensity hL
  have hpower :
      log (L : ℝ) ^ (-η) * log (L : ℝ) =
        log (L : ℝ) ^ (1 - η) := by
    rw [← Real.rpow_add_one hlog.ne' (-η)]
    congr 1
    ring
  have hfirst :
      C * log (L : ℝ) ^ (-η) *
          log (log (L : ℝ)) ^ m ≤
        (mertensLowerConstant / log (L : ℝ)) / D := by
    rw [div_div]
    apply (le_div_iff₀ (mul_pos hlog hD)).2
    calc
      C * log (L : ℝ) ^ (-η) *
            log (log (L : ℝ)) ^ m *
            (log (L : ℝ) * D) =
          (D * C) *
            (log (L : ℝ) ^ (1 - η) *
              log (log (L : ℝ)) ^ m) := by
        rw [← hpower]
        ring
      _ ≤ mertensLowerConstant := hsmallL.le
  exact hfirst.trans
    (div_le_div_of_nonneg_right hmertens hD.le)

/-- The certified deletion slope beats one full power of `log L`. -/
theorem oddBudgetSlope_mul_log_tailBase_gt_one :
    1 < oddBudgetSlope * log oddTailBase := by
  simpa [oddBudgetSlope, oddTailBase] using
    Erdos327.odd_deletion_exponent_gt_one

/-- The certified mixed prefactor slope is smaller than one power of
`log L`. -/
theorem oddBudgetSlope_mul_log_mixedBase_lt_one :
    oddBudgetSlope * log mixedOddWeightBase < 1 := by
  simpa [oddBudgetSlope, mixedOddWeightBase] using
    Erdos327.odd_cross_exponent_lt_one

/-- The odd regularity intercept selected at slope `3.3912` eventually
meets the canonical odd-tail budget. -/
theorem eventually_oddBudget_meets_tail :
    ∀ᶠ L : ℕ in atTop,
      2 * unrestrictedCenteredTailConstant
          oddAnatomySlope oddTailBase *
          oddTailBase ^ (-oddBudget L) ≤
        Erdos327.roughDensity L / 64 := by
  have hbase :=
    eventually_const_mul_log_rpow_neg_mul_loglog_rpow_le_roughDensity
      (C := 2 * unrestrictedCenteredTailConstant
        oddAnatomySlope oddTailBase)
      (D := 64)
      (η := oddBudgetSlope * log oddTailBase)
      (m := 0)
      (by
        have := unrestrictedCenteredTailConstant_nonneg oddTail_gap
        positivity)
      (by norm_num)
      oddBudgetSlope_mul_log_tailBase_gt_one
  filter_upwards [hbase, eventually_ge_atTop 3] with L hbound hL
  have hLreal : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  rw [oddBudget, base_rpow_neg_mul_loglog
    (by linarith [oddTailBase_gt_one]) hLreal]
  simpa using hbound

/-- Uniform comparison needed for the main mixed term: for every fixed
nonnegative constant, the growing factor `q_o^Ko` is still absorbed by
`(log L)^(-2)` and the six schedule-height losses. -/
theorem eventually_mixedBudget_main_le_roughDensity
    {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ L : ℕ in atTop,
      C * mixedOddWeightBase ^ oddBudget L *
          log (L : ℝ) ^ (-2 : ℝ) *
          log (log (L : ℝ)) ^ (6 : ℝ) ≤
        Erdos327.roughDensity L / 64 := by
  let η : ℝ := 2 - oddBudgetSlope * log mixedOddWeightBase
  have hη : 1 < η := by
    dsimp [η]
    linarith [oddBudgetSlope_mul_log_mixedBase_lt_one]
  have hbase :=
    eventually_const_mul_log_rpow_neg_mul_loglog_rpow_le_roughDensity
      (C := C) (D := 64) (η := η) (m := 6)
      hC (by norm_num) hη
  filter_upwards [hbase, eventually_ge_atTop 3] with L hbound hL
  have hLreal : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have hlog : 0 < log (L : ℝ) := log_pos hLreal
  rw [oddBudget, base_rpow_mul_loglog
    (by linarith [mixedOddWeightBase_gt_one]) hLreal]
  have hcombine :
      log (L : ℝ) ^
            (oddBudgetSlope * log mixedOddWeightBase) *
          log (L : ℝ) ^ (-2 : ℝ) =
        log (L : ℝ) ^ (-η) := by
    rw [← Real.rpow_add hlog]
    congr 1
    dsimp [η]
    ring
  calc
    C * log (L : ℝ) ^
            (oddBudgetSlope * log mixedOddWeightBase) *
          log (L : ℝ) ^ (-2 : ℝ) *
          log (log (L : ℝ)) ^ (6 : ℝ) =
        C *
          (log (L : ℝ) ^
              (oddBudgetSlope * log mixedOddWeightBase) *
            log (L : ℝ) ^ (-2 : ℝ)) *
          log (log (L : ℝ)) ^ (6 : ℝ) := by ring
    _ = C * log (L : ℝ) ^ (-η) *
          log (log (L : ℝ)) ^ (6 : ℝ) := by rw [hcombine]
    _ ≤ Erdos327.roughDensity L / 64 := hbound

end

end Erdos327.Analytic
