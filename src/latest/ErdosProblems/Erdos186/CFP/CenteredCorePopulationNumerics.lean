/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredPreprocessingSource
import ErdosProblems.Erdos186.CFP.IntegerTheoremLogLossTerminal

/-!
# A populated retained core from the public scale inequality

The deterministic centered preprocessing deletes at most
`(6 * D * H + 1) * s * (log₂ m + 1)` points.  If the final fixed scale
denominator dominates four times one more than this coefficient, the
source-facing real scale inequality leaves at least `s + 1` points in the
retained stable core.  This is the exact population lower bound used by the
sharp colouring stage.
-/

namespace Erdos186.CFP

noncomputable section

set_option autoImplicit false

/-- A sufficiently large final denominator turns the public scale bound
into a linear lower bound for the retained centered core. -/
theorem centeredPreprocessingCore_succ_scale_le_card
    {A : Finset ℤ} {N s D C0 preprocessingScaleDen fold H finalScaleDen : ℕ}
    (data : Preprocessing.DyadicCenteredPreprocessingData
      (insert 0 A) s D N C0 1 preprocessingScaleDen fold)
    (hzeroA : 0 ∉ A)
    (hinterval : ∀ z ∈ insert 0 A, 0 ≤ z ∧ z < (N : ℤ))
    (hlog : Nat.log 2 N + 1 ≤ H * (Nat.log 2 A.card + 1))
    (hcard : 2 ≤ A.card)
    (hfinal : 4 * (6 * D * H + 2) ≤ finalScaleDen)
    (hscale : (finalScaleDen : ℝ) * (s : ℝ) *
        Real.logb 2 (A.card : ℝ) ≤ (A.card : ℝ)) :
    s + 1 ≤ data.core.card := by
  let ell := Nat.log 2 A.card + 1
  let lossCoefficient := 6 * D * H + 1
  have hell : 1 ≤ ell := by
    dsimp only [ell]
    omega
  have hlogReal := natLog_two_add_one_le_four_mul_logb hcard
  have hscaleNat : (lossCoefficient + 1) * s * ell ≤ A.card := by
    have hnonneg : 0 ≤ Real.logb 2 (A.card : ℝ) := by
      rw [Real.logb]
      positivity
    have hcoeff : 4 * (lossCoefficient + 1) ≤ finalScaleDen := by
      simpa only [lossCoefficient] using hfinal
    have hcoeffReal :
        ((4 * (lossCoefficient + 1) : ℕ) : ℝ) ≤
          (finalScaleDen : ℝ) := by
      exact_mod_cast hcoeff
    have hcast :
        (((lossCoefficient + 1) * s * ell : ℕ) : ℝ) ≤
          (A.card : ℝ) := by
      calc
        (((lossCoefficient + 1) * s * ell : ℕ) : ℝ) =
            (lossCoefficient + 1 : ℝ) * (s : ℝ) * (ell : ℝ) := by
              norm_num
        _ ≤ (lossCoefficient + 1 : ℝ) * (s : ℝ) *
              (4 * Real.logb 2 (A.card : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hlogReal
              (mul_nonneg (by positivity) (by positivity))
        _ = ((4 * (lossCoefficient + 1) : ℕ) : ℝ) * (s : ℝ) *
              Real.logb 2 (A.card : ℝ) := by
            norm_num
            ring
        _ ≤ (finalScaleDen : ℝ) * (s : ℝ) *
              Real.logb 2 (A.card : ℝ) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hcoeffReal (by positivity)) hnonneg
        _ ≤ (A.card : ℝ) := hscale
    exact_mod_cast hcast
  have hpreLoss : preprocessingCardinalityLoss (insert 0 A) s D ≤
      lossCoefficient * s * ell := by
    have h := preprocessingCardinalityLoss_le_scale_mul_log
      (A := insert 0 A) (n := N) (m := A.card) (s := s) (D := D)
      (horizonCoefficient := H) (Finset.mem_insert_self 0 A) hinterval hlog
    simpa only [lossCoefficient, ell] using h
  have hsource := data.source_card_le
  rw [Finset.card_insert_of_notMem hzeroA] at hsource
  dsimp only [preprocessingCardinalityLoss] at hpreLoss
  have hsEll : s ≤ s * ell := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left s hell
  have hbudget : lossCoefficient * s * ell + s ≤ A.card := by
    calc
      lossCoefficient * s * ell + s ≤
          lossCoefficient * s * ell + s * ell :=
        Nat.add_le_add_left hsEll _
      _ = (lossCoefficient + 1) * s * ell := by ring
      _ ≤ A.card := hscaleNat
  omega

end

end Erdos186.CFP

#print axioms Erdos186.CFP.centeredPreprocessingCore_succ_scale_le_card
