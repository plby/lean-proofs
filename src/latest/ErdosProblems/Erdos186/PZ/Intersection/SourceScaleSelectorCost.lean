/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Reduction.CoreFraction
import ErdosProblems.Erdos186.PZ.Intersection.SourceFrozenParameterAsymptotics

/-!
# Loss and reserve cost of the canonical scale selector

The canonical scale has a squared logarithm in its denominator.  After the
CFP loss consumes one logarithm, the sum of loss and reserve is bounded by a
fixed rank-dependent constant times `card / log₂ card`, plus one.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- Exact logarithmic cost bound for one canonical-scale selected input. -/
theorem scaleSelector_loss_add_reserveBound_le
    {beta eta exponent : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    {r : ℕ} (X : Finset (LatticePoint r))
    (hX : (context.scaleSelector exponent).Eligible X)
    (hcard : 2 ≤ X.card) :
    ((((context.scaleSelector exponent).chosen X hX).loss +
          ((context.scaleSelector exponent).chosen X hX).reserveBound : ℕ) : ℝ) ≤
      ((context.lossConstant r : ℝ) + 1) * (X.card : ℝ) /
          Real.logb 2 (X.card : ℝ) + 1 := by
  let I := (context.scaleSelector exponent).input X hX
  let logX := Real.logb 2 (X.card : ℝ)
  have hcardReal : (2 : ℝ) ≤ (X.card : ℝ) := by exact_mod_cast hcard
  have hlogPos : 0 < logX := by
    dsimp only [logX]
    exact Real.logb_pos (by norm_num) (one_lt_two.trans_le hcardReal)
  have hlogOne : 1 ≤ logX := by
    dsimp only [logX, Real.logb]
    rw [le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    simpa only [one_mul] using Real.strictMonoOn_log.monotoneOn
      (by norm_num : (0 : ℝ) < 2)
      (zero_lt_two.trans_le hcardReal) hcardReal
  have hdenPos : 0 < (context.scaleDen r : ℝ) * logX ^ 2 :=
    mul_pos (by exact_mod_cast context.scaleDen_pos r) (sq_pos_of_pos hlogPos)
  have hcanonical :
      (Reduction.canonicalScale context r X.card : ℝ) ≤
        Reduction.canonicalScaleReal context r X.card :=
    Nat.floor_le (div_nonneg (Nat.cast_nonneg _) hdenPos.le)
  have hscaleCanonical : I.scale =
      Reduction.canonicalScale context r X.card := by
    exact context.scaleSelector_input_scale hX
  have hscale : (I.scale : ℝ) ≤ (X.card : ℝ) / logX ^ 2 := by
    rw [hscaleCanonical]
    rw [Reduction.canonicalScaleReal] at hcanonical
    have hdenOne : (1 : ℝ) ≤ context.scaleDen r := by
      exact_mod_cast context.scaleDen_pos r
    calc
      (Reduction.canonicalScale context r X.card : ℝ) ≤
          (X.card : ℝ) /
            ((context.scaleDen r : ℝ) * logX ^ 2) := by
        simpa only [logX] using hcanonical
      _ ≤ (X.card : ℝ) / logX ^ 2 := by
        apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
          (sq_pos_of_pos hlogPos)
        nlinarith [sq_pos_of_pos hlogPos]
  have hloss := I.selectedCFP_loss_le
  have hscaleLog : (I.scale : ℝ) * logX ≤
      (X.card : ℝ) / logX := by
    calc
      (I.scale : ℝ) * logX ≤
          ((X.card : ℝ) / logX ^ 2) * logX :=
        mul_le_mul_of_nonneg_right hscale hlogPos.le
      _ = (X.card : ℝ) / logX := by
        field_simp [hlogPos.ne']
  have hreserveLog : (I.scale : ℝ) ≤ (I.scale : ℝ) * logX := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hlogOne (Nat.cast_nonneg I.scale)
  have hcost : (I.selectedCFP.loss : ℝ) + (I.scale : ℝ) ≤
      ((context.lossConstant r : ℝ) + 1) *
          ((X.card : ℝ) / logX) + 1 := by
    calc
      (I.selectedCFP.loss : ℝ) + (I.scale : ℝ) ≤
          (context.lossConstant r : ℝ) * (I.scale : ℝ) * logX +
            1 + (I.scale : ℝ) := by
        dsimp only [logX]
        linarith [hloss]
      _ ≤ (context.lossConstant r : ℝ) * (I.scale : ℝ) * logX +
            1 + (I.scale : ℝ) * logX := by linarith
      _ = ((context.lossConstant r : ℝ) + 1) *
            ((I.scale : ℝ) * logX) + 1 := by ring
      _ ≤ ((context.lossConstant r : ℝ) + 1) *
            ((X.card : ℝ) / logX) + 1 := by
        gcongr
  simpa only [Reduction.BoundedCFPSelector.chosen,
    Reduction.EligibleInput.selectedCFP, Nat.cast_add, I, logX,
    mul_div_assoc] using hcost

end

end Erdos186.PZ.Intersection
