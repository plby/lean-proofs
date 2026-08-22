/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZGapBetaNumerics
import ErdosProblems.Erdos1165.HLOZMeshCandidateFutureFactor
import ErdosProblems.Erdos1165.HLOZProposition48Candidates

/-!
# Polynomial Proposition 4.9 candidate numerics

The low candidate screen uses the fixed first-strip budget `initialBudget48`,
not a deficit-band candidate budget.  On mesh cell `a`, Proposition 4.9 gives
the conditional coordinate ratio

`C * m^(meshExponent a + meshDelta - kappaOne)`.

For a positive cell the future walk contributes the lower-edge escape factor
`O(m^(-(meshExponent a - meshDelta)))`; the first cell has unit escape cost.
In both cases the product is `O(log^2 m * m^(-(kappaOne-2*meshDelta)))`, which
is summably smaller than the canonical `m^(-kappa)` transition envelope.
-/

open Filter
open scoped ENNReal

namespace Erdos1165.HLOZMeshCandidatePolynomialNumerics

open HLOZGapBetaNumerics HLOZHighSpatialTransitionFactor
open HLOZMeshCandidateFutureFactor HLOZMeshSpatialTransitionFactor
open HLOZPathEvents HLOZProposition48Candidates ScreeningInstantiation
open BoundaryVisitRegeneration
open TerminalParameterBounds

noncomputable section

/-- The polynomial conditional-ratio envelope supplied by Proposition 4.9
on mesh cell `a`. -/
def prop49CandidateRatioEnvelope (C : ℝ) (m : ℕ) (a : GapScale) : ℝ≥0∞ :=
  ENNReal.ofReal
    (C * (m : ℝ) ^ (meshExponent a + meshDelta - kappaOne))

@[simp] theorem prop49CandidateRatioEnvelope_ne_top
    (C : ℝ) (m : ℕ) (a : GapScale) :
    prop49CandidateRatioEnvelope C m a ≠ ∞ := by
  simp [prop49CandidateRatioEnvelope]

@[simp] theorem prop49CandidateRatioEnvelope_toReal
    {C : ℝ} (hC : 0 ≤ C) (m : ℕ) (a : GapScale) :
    (prop49CandidateRatioEnvelope C m a).toReal =
      C * (m : ℝ) ^ (meshExponent a + meshDelta - kappaOne) := by
  rw [prop49CandidateRatioEnvelope, ENNReal.toReal_ofReal]
  exact mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- The natural lower-edge radius of a positive mesh cell contains the full
exponential-third radius used by the potential-kernel estimate. -/
lemma exponentialThirdRadius_le_meshLowerSpatialRadius
    (m : ℕ) (a : GapScale) (ha : 0 < a.1) :
    Real.exp ((m : ℝ) ^ meshExponent (a.1 - 1)) / 3 ≤
      (meshLowerSpatialRadius m a : ℝ) := by
  rw [meshLowerSpatialRadius_of_pos m a ha]
  unfold meshRadius
  exact Nat.le_ceil _

/-- At a positive mesh cell the predecessor exponent is one mesh step below
the current exponent. -/
lemma meshExponent_pred_eq_sub_meshDelta
    (a : GapScale) (ha : 0 < a.1) :
    meshExponent (a.1 - 1) = meshExponent a - meshDelta := by
  unfold meshExponent
  rw [Nat.cast_sub (by omega : 1 ≤ a.1)]
  ring

/-- The fixed first-strip budget is at most three logarithmic squares once
that logarithmic square is at least one. -/
lemma initialBudget48_cast_le_three_log_sq
    {m : ℕ} (hlog : 1 ≤ Real.log (m : ℝ) ^ 2) :
    (initialBudget48 m : ℝ) ≤ 3 * Real.log (m : ℝ) ^ 2 := by
  have hceil := Nat.ceil_lt_add_one (sq_nonneg (Real.log (m : ℝ)))
  unfold initialBudget48
  push_cast
  linarith

/-- Literal future escape at the lower edge of any fixed positive mesh cell.
This is the potential-kernel argument used for the high spatial screen, with
the cell's predecessor exponent in place of `kappaTwo`. -/
theorem eventually_literalEscapeProbability_meshLowerSpatialRadius_le
    (a : GapScale) (ha : 0 < a.1) :
    ∀ᶠ m : ℕ in atTop,
      literalEscapeProbability (meshLowerSpatialRadius m a) ≤
        2 * Real.pi / (m : ℝ) ^ (meshExponent a - meshDelta) := by
  have hgamma : 0 < meshExponent (a.1 - 1) := by
    unfold meshExponent meshDelta
    positivity
  have htend := ScreeningInstantiation.tendsto_nat_rpow_atTop hgamma
  have herror := htend.eventually (eventually_ge_atTop
    (2 * Real.pi * highSpatialPotentialError + Real.log 3))
  have hlogThree := htend.eventually
    (eventually_ge_atTop (2 * Real.log 3))
  have hfive := htend.eventually (eventually_ge_atTop (Real.log 15))
  filter_upwards [herror, hlogThree, hfive, eventually_ge_atTop 1] with
      m herrorM hlogThreeM hfiveM hm
  have hmPowPos : 0 < (m : ℝ) ^ meshExponent (a.1 - 1) := by positivity
  have hRlower := exponentialThirdRadius_le_meshLowerSpatialRadius m a ha
  have hRpos : (0 : ℝ) < meshLowerSpatialRadius m a := by
    exact_mod_cast meshLowerSpatialRadius_pos ha
  have hscalePos : 0 <
      Real.exp ((m : ℝ) ^ meshExponent (a.1 - 1)) / 3 := by positivity
  have hlogLower :
      (m : ℝ) ^ meshExponent (a.1 - 1) - Real.log 3 ≤
        Real.log (meshLowerSpatialRadius m a : ℝ) := by
    have hlog := Real.log_le_log hscalePos hRlower
    rw [Real.log_div (Real.exp_ne_zero _) (by norm_num : (3 : ℝ) ≠ 0),
      Real.log_exp] at hlog
    exact hlog
  have hRfive : 5 ≤ meshLowerSpatialRadius m a := by
    have hexp15 : (15 : ℝ) ≤
        Real.exp ((m : ℝ) ^ meshExponent (a.1 - 1)) := by
      calc
        (15 : ℝ) = Real.exp (Real.log 15) := by
          rw [Real.exp_log (by norm_num : (0 : ℝ) < 15)]
        _ ≤ _ := Real.exp_le_exp.mpr hfiveM
    have : (5 : ℝ) ≤ (meshLowerSpatialRadius m a : ℝ) := by
      linarith
    exact_mod_cast this
  have hlarge : highSpatialPotentialError ≤
      (1 / Real.pi) * Real.log (meshLowerSpatialRadius m a : ℝ) := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have hfromError : highSpatialPotentialError ≤
        (1 / Real.pi) *
          ((m : ℝ) ^ meshExponent (a.1 - 1) - Real.log 3) := by
      rw [one_div_mul_eq_div, le_div_iff₀ hpi]
      linarith
    exact hfromError.trans
      (mul_le_mul_of_nonneg_left hlogLower (one_div_nonneg.mpr hpi.le))
  have hescape := literalEscapeProbability_le_pi_div_log hRfive hlarge
  have hhalf : (m : ℝ) ^ meshExponent (a.1 - 1) / 2 ≤
      Real.log (meshLowerSpatialRadius m a : ℝ) := by linarith
  have hhalfPos : 0 < (m : ℝ) ^ meshExponent (a.1 - 1) / 2 := by
    positivity
  rw [← meshExponent_pred_eq_sub_meshDelta a ha]
  calc
    literalEscapeProbability (meshLowerSpatialRadius m a) ≤
        Real.pi / Real.log (meshLowerSpatialRadius m a : ℝ) := hescape
    _ ≤ Real.pi / ((m : ℝ) ^ meshExponent (a.1 - 1) / 2) := by
      exact div_le_div_of_nonneg_left Real.pi_pos.le hhalfPos hhalf
    _ = 2 * Real.pi / (m : ℝ) ^ meshExponent (a.1 - 1) := by
      field_simp

/-! ## The fixed-first-strip polynomial product -/

/-- The exponent left after multiplying the Proposition 4.9 ratio by the
lower-edge spatial escape. -/
lemma prop49_decay_exponent_sub_kappa :
    (kappaOne - 2 * meshDelta) - kappa = kappaOne - kappaTwo := by
  unfold kappa
  ring

/-- The power gap between the Proposition 4.9 product and the canonical
transition envelope is strictly positive. -/
lemma prop49_decay_gap_pos : 0 < kappaOne - kappaTwo := by
  norm_num [kappaOne, kappaTwo]

/-- The first mesh cell has exactly the common Proposition 4.9 decay
exponent: its conditional ratio already contributes the full decay and its
future factor is one. -/
lemma meshExponent_zero_add_delta_sub_kappaOne :
    meshExponent (⟨0, by simp [meshSteps]⟩ : GapScale) + meshDelta - kappaOne =
      -(kappaOne - 2 * meshDelta) := by
  norm_num [meshExponent, meshDelta]

private lemma meshExponent_eq_meshDelta_of_val_eq_zero
    (a : GapScale) (ha : a.1 = 0) :
    meshExponent a = meshDelta := by
  unfold meshExponent
  rw [ha]
  norm_num

/-- A real-valued version of the fixed-first-strip product estimate.  It is
kept separate from `ENNReal` coercions so the exponent cancellation remains
transparent. -/
theorem eventually_initialBudget48_mul_prop49Ratio_mul_escape_real_le
    (C : ℝ) (hC : 0 ≤ C) (a : GapScale) :
    ∀ᶠ m : ℕ in atTop,
      (initialBudget48 m : ℝ) *
          (C * (m : ℝ) ^
            (meshExponent a + meshDelta - kappaOne)) *
          (if a.1 = 0 then 1
            else literalEscapeProbability (meshLowerSpatialRadius m a)) ≤
        1 / |(m : ℝ) + 1| ^ kappa := by
  have hpower := eventually_const_mul_log_sq_le_nat_rpow
    (12 * C * (Real.pi + 1)) (kappaOne - kappaTwo)
      prop49_decay_gap_pos
  have hlog : Tendsto (fun m : ℕ ↦ Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogOne := hlog.eventually (eventually_ge_atTop 1)
  by_cases ha : a.1 = 0
  · filter_upwards [hpower, hlogOne, eventually_ge_atTop 1] with
        m hpowerM hlogOneM hm
    have hmPos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hbudget := initialBudget48_cast_le_three_log_sq
      (by nlinarith [hlogOneM] : 1 ≤ Real.log (m : ℝ) ^ 2)
    have hkappaNonneg : 0 ≤ kappa := by
      norm_num [kappa, kappaTwo, meshDelta]
    have hkappaLeOne : kappa ≤ 1 := by
      norm_num [kappa, kappaTwo, meshDelta]
    have hbase : (m + 1 : ℝ) ≤ 2 * m := by linarith
    have hshiftPow : (m + 1 : ℝ) ^ kappa ≤
        2 * (m : ℝ) ^ kappa := by
      calc
        (m + 1 : ℝ) ^ kappa ≤ (2 * m : ℝ) ^ kappa :=
          Real.rpow_le_rpow (by positivity) hbase hkappaNonneg
        _ = (2 : ℝ) ^ kappa * (m : ℝ) ^ kappa := by
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hmPos.le]
        _ ≤ 2 * (m : ℝ) ^ kappa := by
          gcongr
          simpa using Real.rpow_le_rpow_of_exponent_le
            (by norm_num : (1 : ℝ) ≤ 2) hkappaLeOne
    have hconst : 6 * C ≤ 12 * C * (Real.pi + 1) := by
      nlinarith [Real.pi_pos]
    have hsmall :
        6 * C * Real.log (m : ℝ) ^ 2 ≤
          (m : ℝ) ^ (kappaOne - kappaTwo) :=
      (mul_le_mul_of_nonneg_right hconst (sq_nonneg _)).trans hpowerM
    have hdecay :
        (initialBudget48 m : ℝ) * C *
            (m : ℝ) ^ (-(kappaOne - 2 * meshDelta)) *
            (m + 1 : ℝ) ^ kappa ≤ 1 := by
      have hpowAdd :
          (m : ℝ) ^ (-(kappaOne - 2 * meshDelta)) *
              (m : ℝ) ^ kappa =
            (m : ℝ) ^ (-(kappaOne - kappaTwo)) := by
        rw [← Real.rpow_add hmPos]
        congr 1
        rw [← prop49_decay_exponent_sub_kappa]
        ring
      have hpowInv :
          (m : ℝ) ^ (-(kappaOne - kappaTwo)) =
            ((m : ℝ) ^ (kappaOne - kappaTwo))⁻¹ := by
        exact Real.rpow_neg hmPos.le _
      calc
        (initialBudget48 m : ℝ) * C *
              (m : ℝ) ^ (-(kappaOne - 2 * meshDelta)) *
              (m + 1 : ℝ) ^ kappa ≤
            3 * Real.log (m : ℝ) ^ 2 * C *
              (m : ℝ) ^ (-(kappaOne - 2 * meshDelta)) *
              (2 * (m : ℝ) ^ kappa) := by gcongr
        _ = 6 * C * Real.log (m : ℝ) ^ 2 *
              ((m : ℝ) ^ (-(kappaOne - 2 * meshDelta)) *
                (m : ℝ) ^ kappa) := by ring
        _ = (6 * C * Real.log (m : ℝ) ^ 2) /
              (m : ℝ) ^ (kappaOne - kappaTwo) := by
          rw [hpowAdd, hpowInv]
          ring
        _ ≤ 1 := by
          exact (div_le_one (Real.rpow_pos_of_pos hmPos _)).2 hsmall
    rw [if_pos ha, meshExponent_eq_meshDelta_of_val_eq_zero a ha]
    have hrpow :
        (m : ℝ) ^ (meshDelta + meshDelta - kappaOne) =
          (m : ℝ) ^ (-(kappaOne - 2 * meshDelta)) := by
      congr 1
      ring
    rw [hrpow, abs_of_pos (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
    rw [le_div_iff₀ (Real.rpow_pos_of_pos (by positivity) _)]
    simpa [mul_assoc] using hdecay
  · have hapos : 0 < a.1 := Nat.pos_of_ne_zero ha
    have hescape :=
      eventually_literalEscapeProbability_meshLowerSpatialRadius_le a hapos
    filter_upwards [hpower, hlogOne, hescape, eventually_ge_atTop 1] with
        m hpowerM hlogOneM hescapeM hm
    have hmPos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hbudget := initialBudget48_cast_le_three_log_sq
      (by nlinarith [hlogOneM] : 1 ≤ Real.log (m : ℝ) ^ 2)
    have hkappaNonneg : 0 ≤ kappa := by
      norm_num [kappa, kappaTwo, meshDelta]
    have hkappaLeOne : kappa ≤ 1 := by
      norm_num [kappa, kappaTwo, meshDelta]
    have hbase : (m + 1 : ℝ) ≤ 2 * m := by linarith
    have hshiftPow : (m + 1 : ℝ) ^ kappa ≤
        2 * (m : ℝ) ^ kappa := by
      calc
        (m + 1 : ℝ) ^ kappa ≤ (2 * m : ℝ) ^ kappa :=
          Real.rpow_le_rpow (by positivity) hbase hkappaNonneg
        _ = (2 : ℝ) ^ kappa * (m : ℝ) ^ kappa := by
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hmPos.le]
        _ ≤ 2 * (m : ℝ) ^ kappa := by
          gcongr
          simpa using Real.rpow_le_rpow_of_exponent_le
            (by norm_num : (1 : ℝ) ≤ 2) hkappaLeOne
    have hsmall :
        12 * C * (Real.pi + 1) * Real.log (m : ℝ) ^ 2 ≤
          (m : ℝ) ^ (kappaOne - kappaTwo) := hpowerM
    rw [if_neg ha, abs_of_pos (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
    rw [le_div_iff₀ (Real.rpow_pos_of_pos (by positivity) _)]
    calc
      (initialBudget48 m : ℝ) *
            (C * (m : ℝ) ^ (meshExponent a + meshDelta - kappaOne)) *
            literalEscapeProbability (meshLowerSpatialRadius m a) *
            (m + 1 : ℝ) ^ kappa ≤
          3 * Real.log (m : ℝ) ^ 2 *
            (C * (m : ℝ) ^ (meshExponent a + meshDelta - kappaOne)) *
            (2 * Real.pi / (m : ℝ) ^ (meshExponent a - meshDelta)) *
            (2 * (m : ℝ) ^ kappa) := by
          gcongr
          exact literalEscapeProbability_nonneg _
      _ = 12 * C * Real.pi * Real.log (m : ℝ) ^ 2 /
            (m : ℝ) ^ (kappaOne - kappaTwo) := by
        have hpowCancel :
            (m : ℝ) ^ (meshExponent a + meshDelta - kappaOne) *
                ((m : ℝ) ^ (meshExponent a - meshDelta))⁻¹ *
                (m : ℝ) ^ kappa =
              ((m : ℝ) ^ (kappaOne - kappaTwo))⁻¹ := by
          rw [← Real.rpow_neg hmPos.le,
            ← Real.rpow_add hmPos, ← Real.rpow_add hmPos]
          rw [← Real.rpow_neg hmPos.le]
          congr 1
          unfold kappa
          ring
        rw [div_eq_mul_inv]
        calc
          3 * Real.log (m : ℝ) ^ 2 *
                (C * (m : ℝ) ^
                  (meshExponent a + meshDelta - kappaOne)) *
                (2 * Real.pi *
                  ((m : ℝ) ^ (meshExponent a - meshDelta))⁻¹) *
                (2 * (m : ℝ) ^ kappa) =
              12 * C * Real.pi * Real.log (m : ℝ) ^ 2 *
                ((m : ℝ) ^
                    (meshExponent a + meshDelta - kappaOne) *
                  ((m : ℝ) ^ (meshExponent a - meshDelta))⁻¹ *
                  (m : ℝ) ^ kappa) := by ring
          _ = 12 * C * Real.pi * Real.log (m : ℝ) ^ 2 *
                ((m : ℝ) ^ (kappaOne - kappaTwo))⁻¹ := by rw [hpowCancel]
      _ ≤ 1 := by
        have hpi : 12 * C * Real.pi ≤ 12 * C * (Real.pi + 1) := by
          nlinarith
        apply (div_le_one (Real.rpow_pos_of_pos hmPos _)).2
        exact (mul_le_mul_of_nonneg_right hpi (sq_nonneg _)).trans hsmall

/-- The source-correct fixed-first-strip low factor.  This is the numerical
endpoint consumed by `FirstStripLowTransitionData`: no deficit-band candidate
budget and no geometric-return comparison appears in its hypotheses. -/
theorem eventually_initialBudget48_mul_prop49CandidateRatioEnvelope_mul_meshEscapeCost_le
    (C : ℝ) (hC : 0 ≤ C) (a : GapScale) :
    ∀ᶠ m : ℕ in atTop,
      (initialBudget48 m : ℝ≥0∞) *
          prop49CandidateRatioEnvelope C m a * meshEscapeCost m a ≤
        UpperCanonical.hlozTransitionCost 1 m := by
  filter_upwards
      [eventually_initialBudget48_mul_prop49Ratio_mul_escape_real_le C hC a]
      with m hreal
  let escape : ℝ := if a.1 = 0 then 1
    else literalEscapeProbability (meshLowerSpatialRadius m a)
  have hescape : 0 ≤ escape := by
    dsimp only [escape]
    split_ifs
    · norm_num
    · exact literalEscapeProbability_nonneg _
  have hcost : meshEscapeCost m a = ENNReal.ofReal escape := by
    dsimp only [escape]
    by_cases ha : a.1 = 0
    · simp [meshEscapeCost, ha]
    · simp [meshEscapeCost, ha]
  have hratio : 0 ≤
      C * (m : ℝ) ^ (meshExponent a + meshDelta - kappaOne) :=
    mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rw [hcost]
  unfold prop49CandidateRatioEnvelope
  rw [← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul
      (mul_nonneg (Nat.cast_nonneg _) hratio)]
  unfold UpperCanonical.hlozTransitionCost UpperAssembly.pSeriesWeight
  simp only [ENNReal.coe_one, one_mul]
  exact ENNReal.ofReal_le_ofReal (by simpa only [escape] using hreal)

/-- Monotone consumer form for a concrete candidate family whose normalized
budget and ratio are bounded by the fixed-first-strip Proposition 4.9 data. -/
theorem eventually_budget_mul_candidateRatio_mul_meshEscapeCost_le
    (C : ℝ) (hC : 0 ≤ C) (a : GapScale) :
    ∀ᶠ m : ℕ in atTop, ∀ {budget : ℕ} {candidateRatio : ℝ≥0∞},
      budget ≤ initialBudget48 m →
      candidateRatio ≤ prop49CandidateRatioEnvelope C m a →
      (budget : ℝ≥0∞) * candidateRatio * meshEscapeCost m a ≤
        UpperCanonical.hlozTransitionCost 1 m := by
  filter_upwards
      [eventually_initialBudget48_mul_prop49CandidateRatioEnvelope_mul_meshEscapeCost_le
        C hC a]
      with m hmain budget candidateRatio hbudget hratio
  calc
    (budget : ℝ≥0∞) * candidateRatio * meshEscapeCost m a ≤
        (initialBudget48 m : ℝ≥0∞) *
          prop49CandidateRatioEnvelope C m a * meshEscapeCost m a := by
      gcongr
    _ ≤ UpperCanonical.hlozTransitionCost 1 m := hmain

end

end Erdos1165.HLOZMeshCandidatePolynomialNumerics
