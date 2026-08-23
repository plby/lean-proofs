/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166HLOZExitTail
import ErdosProblems.Erdos1166.Erdos1166HLOZTimeChange

/-!
# Appendix A to the near-critical HLOZ horizon

This module joins the checked Appendix-A interpolation and independent-block
amplification to the rounded horizon used later in HLOZ Section 4.  The sole
remaining input is the successful-point estimate (A.1); the exit-time tail,
integer rounding, time interpolation, block amplification, and summability
at the Section-4 horizons are all discharged here.
-/

namespace Erdos1166.HLOZProp13FromAppendix

open Filter MeasureTheory Set
open scoped ENNReal

open HLOZAppendixA HLOZExitTail HLOZNearCriticalBridge HLOZTimeChange

/-- We take `4 ε = 1/25`, the lower-deviation exponent used by the corrected
near-critical horizon in Section 4. -/
noncomputable def appendixEpsilon : ℝ := 1 / 100

theorem appendixEpsilon_pos : 0 < appendixEpsilon := by
  norm_num [appendixEpsilon]

theorem appendixEpsilon_lt_two_fifteenths :
    appendixEpsilon < (2 : ℝ) / 15 := by
  norm_num [appendixEpsilon]

theorem four_mul_appendixEpsilon_eq_lowerTailDelta :
    4 * appendixEpsilon = lowerTailDelta := by
  norm_num [appendixEpsilon, lowerTailDelta_eq]

/-- The rounded Section-4 horizons tend to infinity. -/
theorem tendsto_nearCriticalHorizon :
    Tendsto nearCriticalHorizon atTop atTop := by
  apply tendsto_atTop.2
  intro N
  have hsqrt : Tendsto (fun m : ℕ ↦ Real.sqrt (m : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hcoeff : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hleading : Tendsto
      (fun m : ℕ ↦ Real.sqrt Real.pi * Real.sqrt (m : ℝ)) atTop atTop :=
    hsqrt.const_mul_atTop hcoeff
  filter_upwards [hleading.eventually (eventually_ge_atTop (N : ℝ))] with m hm
  have hcorrection : 0 ≤
      horizonCoefficient * (m : ℝ) ^ horizonExponent :=
    mul_nonneg horizonCoefficient_pos.le
      (Real.rpow_nonneg (Nat.cast_nonneg m) _)
  have hlog : (N : ℝ) ≤ nearCriticalLogHorizon m := by
    rw [nearCriticalLogHorizon]
    linarith
  have hexp : nearCriticalLogHorizon m ≤
      Real.exp (nearCriticalLogHorizon m) := by
    linarith [Real.add_one_le_exp (nearCriticalLogHorizon m)]
  have hceil : Real.exp (nearCriticalLogHorizon m) ≤
      (nearCriticalHorizon m : ℝ) := by
    exact Nat.le_ceil _
  exact_mod_cast hlog.trans (hexp.trans hceil)

/-- The exact remaining Appendix-A input, specialized to the exponent used
later in the HLOZ screening argument. -/
def AppendixDiskEstimate : Prop :=
  ∀ᶠ j : ℕ in atTop,
    ENNReal.ofReal
        (Real.exp
          (-((j : ℝ) ^ (3 / 5 + appendixEpsilon / 3 : ℝ)))) <
      incrementLaw
        (diskGood
          (fun ω n ↦ maxLocalTime (simpleRandomWalk ω) n)
          exitTime appendixEpsilon j)

/-- Appendix A supplies the exact Proposition-1.3 event used by the
near-critical bridge, sampled at its rounded horizons and dominated by a
summable exponential sequence. -/
theorem eventually_nearCritical_prop13_bound
    (hdisk : AppendixDiskEstimate) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalkLaw
          (proposition13LowerTailEvent (nearCriticalHorizon m)) ≤
        ENNReal.ofReal (Real.exp (-(m : ℝ))) := by
  have hglobal := eventually_prop13_lower_deviation_of_disk
    appendixEpsilon_pos appendixEpsilon_lt_two_fifteenths hdisk
  have hsample := tendsto_nearCriticalHorizon.eventually hglobal
  have htail := eventually_nearCritical_prop13_tail_le_exp_neg_level
    1 (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hsample, htail] with m hsamplem htailm
  have hevent :
      proposition13LowerTailEvent (nearCriticalHorizon m) =
        {s | (maxLocalTime s (nearCriticalHorizon m) : ℝ) <
          1 / Real.pi * Real.log (nearCriticalHorizon m : ℝ) ^ 2 -
            Real.log (nearCriticalHorizon m : ℝ) ^
              (8 / 5 + 4 * appendixEpsilon : ℝ)} := by
    ext s
    simp only [HLOZNearCriticalBridge.proposition13LowerTailEvent,
      Set.mem_setOf_eq, HLOZNearCriticalBridge.proposition13Threshold]
    rw [show lowerTailExponent = 8 / 5 + 4 * appendixEpsilon by
      rw [lowerTailExponent, four_mul_appendixEpsilon_eq_lowerTailDelta]]
    ring
  calc
    simpleRandomWalkLaw
        (proposition13LowerTailEvent (nearCriticalHorizon m)) =
        simpleRandomWalkLaw
          {s | (maxLocalTime s (nearCriticalHorizon m) : ℝ) <
            1 / Real.pi * Real.log (nearCriticalHorizon m : ℝ) ^ 2 -
              Real.log (nearCriticalHorizon m : ℝ) ^
                (8 / 5 + 4 * appendixEpsilon : ℝ)} := by rw [hevent]
    _ ≤ ENNReal.ofReal
          (Real.exp
            (-Real.exp
              (Real.log (nearCriticalHorizon m : ℝ) ^ (3 / 5 : ℝ)))) :=
      hsamplem
    _ ≤ ENNReal.ofReal (Real.exp (-(m : ℝ))) := by
      apply ENNReal.ofReal_le_ofReal
      simpa using htailm

/-- Consequently the late-horizon contribution for every one of the six
pairings is summable. -/
theorem pairingLate_tsum_ne_top (hdisk : AppendixDiskEstimate) (i : Fin 6) :
    (∑' m : ℕ,
      simpleRandomWalkLaw
        (pairingLateHorizonEvent nearCriticalHorizon m i)) ≠ ∞ := by
  exact tsum_pairingLate_nearCritical_of_eventually_prop13_bound i
    (fun m ↦ ENNReal.ofReal (Real.exp (-(m : ℝ))))
    (eventually_nearCritical_prop13_bound hdisk)
    Real.summable_exp_neg_nat.tsum_ofReal_ne_top

/-- The same Appendix-A estimate supplies the almost-sure finite-horizon
cutoff used by Propositions 4.5--4.9. -/
theorem ae_eventually_fourth_threshold_le_horizon
    (hdisk : AppendixDiskEstimate) :
    ∀ᵐ s ∂simpleRandomWalkLaw, ∀ᶠ m : ℕ in atTop,
      s ∈ hlozThresholdTimeEvent m →
        firstKSitesReachLevel m 4 s ≤
          (nearCriticalHorizon m : WithTop ℕ) := by
  simpa only [thresholdTimeEventK_four] using
    ae_eventually_threshold_le_nearCriticalHorizon_of_eventually_prop13_bound
      4 (fun m ↦ ENNReal.ofReal (Real.exp (-(m : ℝ))))
      (eventually_nearCritical_prop13_bound hdisk)
      Real.summable_exp_neg_nat.tsum_ofReal_ne_top

end Erdos1166.HLOZProp13FromAppendix
