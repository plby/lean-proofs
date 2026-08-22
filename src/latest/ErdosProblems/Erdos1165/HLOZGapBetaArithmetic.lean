/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos1165.HLOZGapFixedPair
import ErdosProblems.Erdos1165.HLOZProposition48Candidates

/-!
# Beta-band arithmetic for HLOZ Lemma 4.10

The decisive identity is

`beta_(j+1) - kappaOne = beta_j - alpha - meshDelta`.

Thus the return exponent `beta_j-alpha` exceeds the logarithmic candidate
count exponent `beta_(j+1)-kappaOne` by exactly the positive mesh width.
The final theorem below is the reusable ENNReal conversion: once this strict
power advantage has supplied the displayed real logarithmic domination, the
candidate budget times the geometric return cost is absorbed into one
negative exponential.
-/

open MeasureTheory Real
open scoped ENNReal

namespace Erdos1165.HLOZGapBetaArithmetic

open HLOZProposition48Candidates

noncomputable section

/-- Exact exponent separation used between two adjacent deficit bands. -/
theorem deficitExponent48_succ_sub_kappaOne (alpha : ℝ) (j : ℕ) :
    deficitExponent48 alpha (j + 1) - ScreeningInstantiation.kappaOne =
      deficitExponent48 alpha j - alpha - ScreeningInstantiation.meshDelta := by
  unfold deficitExponent48
  push_cast
  ring

/-- Equivalent form emphasizing the extra positive mesh-width power in the
return exponent. -/
theorem deficitExponent48_sub_alpha (alpha : ℝ) (j : ℕ) :
    deficitExponent48 alpha j - alpha =
      (deficitExponent48 alpha (j + 1) -
        ScreeningInstantiation.kappaOne) +
          ScreeningInstantiation.meshDelta := by
  rw [deficitExponent48_succ_sub_kappaOne]
  ring

/-- The number of strict post-past returns certified by a lower deficit
threshold `m^beta`, with the extra first hit removed. -/
def requiredReturns48 (m : ℕ) (beta : ℝ) : ℕ :=
  Nat.ceil ((m : ℝ) ^ beta) - 1

lemma requiredReturns48_add_one
    {m : ℕ} {beta : ℝ} (hpos : 0 < (m : ℝ) ^ beta) :
    requiredReturns48 m beta + 1 = Nat.ceil ((m : ℝ) ^ beta) := by
  unfold requiredReturns48
  have hceil : 0 < Nat.ceil ((m : ℝ) ^ beta) := by
    exact Nat.ceil_pos.mpr hpos
  omega

/-- A strict real deficit lower bound supplies the natural visit count used
by `StoppedCandidateLocalTimeWitness`. -/
theorem requiredReturns48_add_one_le_of_rpow_lt_nat
    {m deficit : ℕ} {beta : ℝ} (hm : 0 < m)
    (hdeficit : (m : ℝ) ^ beta < deficit) :
    requiredReturns48 m beta + 1 ≤ deficit := by
  rw [requiredReturns48_add_one (Real.rpow_pos_of_pos (by exact_mod_cast hm) _)]
  exact_mod_cast Nat.ceil_le.mpr hdeficit.le

/-- One beta-band candidate factor is absorbed by a target exponential once
the return exponent dominates the logarithm of the explicit Proposition 4.8
budget plus that target. -/
theorem candidateBudget48_mul_geometricReturnCost_le_exp_neg
    {m : ℕ} {beta escapeChance target : ℝ} {returns : ℕ}
    (hbudget : 0 < candidateBudget48 m beta)
    (hzero : 0 ≤ escapeChance) (hone : escapeChance ≤ 1)
    (hdominates :
      Real.log (candidateBudget48 m beta) + target ≤
        escapeChance * returns) :
    (candidateBudget48 m beta : ℝ≥0∞) *
        Gap.geometricReturnCost escapeChance returns ≤
      ENNReal.ofReal (Real.exp (-target)) := by
  calc
    (candidateBudget48 m beta : ℝ≥0∞) *
        Gap.geometricReturnCost escapeChance returns ≤
        (candidateBudget48 m beta : ℝ≥0∞) *
          Gap.exponentialReturnCost escapeChance returns := by
      gcongr
      exact Gap.geometricReturnCost_le_exponentialReturnCost
        hzero hone returns
    _ ≤ ENNReal.ofReal (Real.exp (-target)) :=
      Gap.ennreal_nat_mul_exp_neg_le_exp_neg hbudget hdominates

/-- The explicit Proposition 4.8 slot budget is positive above level one. -/
theorem candidateBudget48_pos {m : ℕ} {beta : ℝ} (hm : 1 < m) :
    0 < candidateBudget48 m beta := by
  unfold candidateBudget48
  apply Nat.ceil_pos.mpr
  unfold candidateBudgetReal48
  have hlog : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm)
  positivity

/-- Fully specialized one-band geometric-cost absorption.  Positivity of
the candidate budget and both probability side conditions are discharged
from the concrete HLOZ definitions; only the decisive logarithmic power
comparison remains. -/
theorem candidateBudget48_mul_meshGeometricReturnCost_le_exp_neg
    {m : ℕ} {beta target : ℝ} {returns : ℕ} (hm : 1 < m)
    (a : HLOZPathEvents.GapScale)
    (hdominates :
      Real.log (candidateBudget48 m beta) + target ≤
        HLOZGapMeshEscape.meshPointEscapeChance m a * returns) :
    (candidateBudget48 m beta : ℝ≥0∞) *
        Gap.geometricReturnCost
          (HLOZGapMeshEscape.meshPointEscapeChance m a) returns ≤
      ENNReal.ofReal (Real.exp (-target)) := by
  exact candidateBudget48_mul_geometricReturnCost_le_exp_neg
    (candidateBudget48_pos hm)
    (HLOZGapMeshEscape.meshPointEscapeChance_pos m a).le
    (HLOZGapMeshEscape.meshPointEscapeChance_le_one m a) hdominates

end

end Erdos1165.HLOZGapBetaArithmetic
