/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZDominantStoppedCandidatePartition
import ErdosProblems.Erdos1165.HLOZGapBetaNumerics
import ErdosProblems.Erdos1165.HLOZMeshCandidateFutureFactor

/-!
# Numerical closure for the prefix-correct low-mesh candidate factor

The canonical and transported-opposite rows each use the quarter-size
dominant-source budget.  Their sum is therefore bounded by the original
Proposition 4.8 candidate budget.  The all-cell spatial factor is at most
one, including the first mesh cell where it is definitionally one.  Hence
the existing adjacent-beta-band geometric-return estimate controls the new
prefix-correct factor without any further probabilistic input.
-/

open Filter
open scoped ENNReal

namespace Erdos1165.HLOZMeshCandidateNumerics

open HLOZDominantStoppedCandidatePartition HLOZGapBetaArithmetic
open HLOZGapBetaNumerics HLOZGapMeshEscape HLOZMeshCandidateFutureFactor
open HLOZMeshSpatialTransitionFactor HLOZPathEvents
open HLOZProposition48Candidates ScreeningInstantiation
open TerminalParameterBounds

noncomputable section

/-- The future spatial factor is a genuine probability.  The first mesh
cell is covered by its unit normalization. -/
theorem meshEscapeCost_le_one (m : ℕ) (a : GapScale) :
    meshEscapeCost m a ≤ 1 := by
  by_cases ha : a.1 = 0
  · simp [meshEscapeCost, ha]
  · rw [meshEscapeCost, if_neg ha, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal
      (literalEscapeProbability_le_one (meshLowerSpatialRadius m a))

/-- The two normalized dominant-source candidate budgets cost no more than
the single unnormalized Proposition 4.8 budget. -/
theorem two_dominantSourceCandidateBudget48_le
    (m : ℕ) (beta : ℝ) :
    dominantSourceCandidateBudget48 m beta +
        dominantSourceCandidateBudget48 m beta ≤
      candidateBudget48 m beta := by
  unfold dominantSourceCandidateBudget48
  omega

/-- Pointwise reduction of the new prefix-correct low factor to the old
adjacent-band geometric-return term.  The only quantitative hypothesis is
the literal chosen-window ratio bound that the negative-binomial window
constructor must supply. -/
theorem two_dominant_mul_ratio_mul_meshEscapeCost_le_adjacent
    {m : ℕ} (hm : 1 ≤ m) (a : GapScale) (j : ℕ)
    {candidateRatio : ℝ≥0∞} {betaReal : ℝ} {returns : ℕ}
    (hbeta : betaReal ≤
      deficitExponent48 (meshExponent a) (j + 1))
    (hreturns : requiredReturns48 m
        (deficitExponent48 (meshExponent a) j) ≤ returns)
    (hratio : candidateRatio ≤
      Gap.geometricReturnCost (meshPointEscapeChance m a) returns) :
    ((dominantSourceCandidateBudget48 m betaReal +
          dominantSourceCandidateBudget48 m betaReal : ℕ) : ℝ≥0∞) *
        candidateRatio * meshEscapeCost m a ≤
      ((candidateBudget48 m
          (deficitExponent48 (meshExponent a) (j + 1)) : ℕ) : ℝ≥0∞) *
        Gap.geometricReturnCost (meshPointEscapeChance m a)
          (requiredReturns48 m
            (deficitExponent48 (meshExponent a) j)) := by
  have hbudgetNat :
      dominantSourceCandidateBudget48 m betaReal +
          dominantSourceCandidateBudget48 m betaReal ≤
        candidateBudget48 m
          (deficitExponent48 (meshExponent a) (j + 1)) :=
    (two_dominantSourceCandidateBudget48_le m betaReal).trans
      (candidateBudget48_mono_beta hm hbeta)
  have hbudget :
      ((dominantSourceCandidateBudget48 m betaReal +
          dominantSourceCandidateBudget48 m betaReal : ℕ) : ℝ≥0∞) ≤
        ((candidateBudget48 m
          (deficitExponent48 (meshExponent a) (j + 1)) : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hbudgetNat
  have hratio' : candidateRatio ≤
      Gap.geometricReturnCost (meshPointEscapeChance m a)
        (requiredReturns48 m
          (deficitExponent48 (meshExponent a) j)) :=
    hratio.trans (geometricReturnCost_anti_returns
      (meshPointEscapeChance_pos m a).le
      (meshPointEscapeChance_le_one m a) hreturns)
  calc
    ((dominantSourceCandidateBudget48 m betaReal +
          dominantSourceCandidateBudget48 m betaReal : ℕ) : ℝ≥0∞) *
        candidateRatio * meshEscapeCost m a ≤
      ((dominantSourceCandidateBudget48 m betaReal +
          dominantSourceCandidateBudget48 m betaReal : ℕ) : ℝ≥0∞) *
        candidateRatio * 1 := by gcongr; exact meshEscapeCost_le_one m a
    _ = ((dominantSourceCandidateBudget48 m betaReal +
          dominantSourceCandidateBudget48 m betaReal : ℕ) : ℝ≥0∞) *
        candidateRatio := by simp
    _ ≤ ((candidateBudget48 m
          (deficitExponent48 (meshExponent a) (j + 1)) : ℕ) : ℝ≥0∞) *
        Gap.geometricReturnCost (meshPointEscapeChance m a)
          (requiredReturns48 m
            (deficitExponent48 (meshExponent a) j)) := by
      exact mul_le_mul hbudget hratio' bot_le bot_le

/-- A positive stretched-logarithmic envelope is eventually below the
canonical one-transition shifted `p`-series envelope. -/
theorem eventually_exp_neg_log_sq_le_hlozTransitionCost
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ m : ℕ in atTop,
      ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) ≤
        UpperCanonical.hlozTransitionCost 1 m := by
  have hlog : Tendsto (fun m : ℕ ↦ Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge := hlog.eventually
    (eventually_ge_atTop
      (max 1 ((ScreeningInstantiation.kappa + 1) / c)))
  filter_upwards [hlarge, eventually_ge_atTop 1] with m hlargeM hm
  have hmPos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlogOne : 1 ≤ Real.log (m : ℝ) :=
    (le_max_left _ _).trans hlargeM
  have hlogRatio : (ScreeningInstantiation.kappa + 1) / c ≤
      Real.log (m : ℝ) := (le_max_right _ _).trans hlargeM
  have hcLog : ScreeningInstantiation.kappa + 1 ≤
      c * Real.log (m : ℝ) := by
    rw [div_le_iff₀ hc] at hlogRatio
    simpa only [mul_comm] using hlogRatio
  have hshift : Real.log ((m : ℝ) + 1) ≤ Real.log (m : ℝ) + 1 := by
    have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hsum : (m : ℝ) + 1 ≤ Real.exp 1 * m := by
      have hexp : 2 ≤ Real.exp 1 := by
        exact Real.exp_one_gt_two.le
      nlinarith
    calc
      Real.log ((m : ℝ) + 1) ≤ Real.log (Real.exp 1 * m) :=
        Real.log_le_log (by positivity) hsum
      _ = Real.log (Real.exp 1) + Real.log (m : ℝ) := by
        rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hmPos)]
      _ = Real.log (m : ℝ) + 1 := by rw [Real.log_exp]; ring
  have hexponent :
      -c * Real.log (m : ℝ) ^ 2 ≤
        -ScreeningInstantiation.kappa * Real.log ((m : ℝ) + 1) := by
    have hkappa : 0 ≤ ScreeningInstantiation.kappa := by
      norm_num [ScreeningInstantiation.kappa,
        ScreeningInstantiation.kappaTwo, ScreeningInstantiation.meshDelta]
    have hmain : ScreeningInstantiation.kappa *
        (Real.log (m : ℝ) + 1) ≤
          c * Real.log (m : ℝ) ^ 2 := by
      have hlogNonneg : 0 ≤ Real.log (m : ℝ) :=
        zero_le_one.trans hlogOne
      have hkappaLeOne : ScreeningInstantiation.kappa ≤ 1 := by
        norm_num [ScreeningInstantiation.kappa,
          ScreeningInstantiation.kappaTwo, ScreeningInstantiation.meshDelta]
      have hleft : ScreeningInstantiation.kappa *
          (Real.log (m : ℝ) + 1) ≤
            (ScreeningInstantiation.kappa + 1) * Real.log (m : ℝ) := by
        nlinarith
      have hright : (ScreeningInstantiation.kappa + 1) *
          Real.log (m : ℝ) ≤
            (c * Real.log (m : ℝ)) * Real.log (m : ℝ) :=
        mul_le_mul_of_nonneg_right hcLog hlogNonneg
      calc
        ScreeningInstantiation.kappa * (Real.log (m : ℝ) + 1) ≤
            (ScreeningInstantiation.kappa + 1) * Real.log (m : ℝ) := hleft
        _ ≤ (c * Real.log (m : ℝ)) * Real.log (m : ℝ) := hright
        _ = c * Real.log (m : ℝ) ^ 2 := by ring
    have := mul_le_mul_of_nonneg_left hshift hkappa
    linarith
  have hexp : Real.exp (-c * Real.log (m : ℝ) ^ 2) ≤
      1 / |(m : ℝ) + 1| ^ ScreeningInstantiation.kappa := by
    rw [abs_of_pos (by positivity : (0 : ℝ) < (m : ℝ) + 1), one_div]
    calc
      Real.exp (-c * Real.log (m : ℝ) ^ 2) ≤
          Real.exp (-ScreeningInstantiation.kappa *
            Real.log ((m : ℝ) + 1)) := Real.exp_le_exp.mpr hexponent
      _ = (((m : ℝ) + 1) ^ ScreeningInstantiation.kappa)⁻¹ := by
        rw [Real.rpow_def_of_pos
          (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
        rw [← Real.exp_neg]
        congr 2
        ring
  unfold UpperCanonical.hlozTransitionCost UpperAssembly.pSeriesWeight
  simp only [ENNReal.coe_one, one_mul]
  exact ENNReal.ofReal_le_ofReal hexp

/-- Eventual numerical closure for the new low candidate factor.  It accepts
the concrete chosen-window ratio comparison and discharges the two-source
budget, all-cell spatial factor, and final HLOZ envelope internally. -/
theorem eventually_two_dominant_mul_ratio_mul_meshEscapeCost_le_hloz
    (a : GapScale) (j : ℕ) {c : ℝ} (hc : 0 < c)
    (hscale : meshExponent a + meshDelta ≤ kappaOne) :
    ∀ᶠ m : ℕ in atTop, ∀ {betaReal : ℝ} {returns : ℕ}
      {candidateRatio : ℝ≥0∞},
      betaReal ≤ deficitExponent48 (meshExponent a) (j + 1) →
      requiredReturns48 m
          (deficitExponent48 (meshExponent a) j) ≤ returns →
      candidateRatio ≤
          Gap.geometricReturnCost (meshPointEscapeChance m a) returns →
      ((dominantSourceCandidateBudget48 m betaReal +
            dominantSourceCandidateBudget48 m betaReal : ℕ) : ℝ≥0∞) *
          candidateRatio * meshEscapeCost m a ≤
        UpperCanonical.hlozTransitionCost 1 m := by
  have hadjacent :=
    eventually_candidateBudget48_mul_meshGeometricReturnCost_le_exp_neg
      a j c hscale hc.le
  have henvelope := eventually_exp_neg_log_sq_le_hlozTransitionCost hc
  filter_upwards [hadjacent, henvelope, eventually_ge_atTop 1] with
      m hadjacentM henvelopeM hm betaReal returns candidateRatio
      hbeta hreturns hratio
  apply (two_dominant_mul_ratio_mul_meshEscapeCost_le_adjacent
    hm a j hbeta hreturns hratio).trans
  exact hadjacentM.trans henvelopeM

end

end Erdos1165.HLOZMeshCandidateNumerics
