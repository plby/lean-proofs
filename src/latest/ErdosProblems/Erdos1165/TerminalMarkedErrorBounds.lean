/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.PoissonKernelMarkedHarnack
import ErdosProblems.Erdos1165.TerminalParameterBounds

/-!
# Numerical loss bounds for the marked terminal Poisson kernel

The zero-visit atom introduces an odds factor `q / (1-q)`.  At the HLOZ
terminal scale the canonical hit probability is at most one half, so this
factor is at most one.  This file records the resulting elementary bound and
combines it with the deterministic estimate that the number of selected
terminal excursions is at most twice the square of the terminal scale.
-/

namespace Erdos1165.TerminalMarkedErrorBounds

open AppendixLocalTime PoissonKernelMarkedHarnack Proposition13Scales
open TerminalParameterBounds ThickPoint

noncomputable section

/-- If `q ≤ 1/2` and the hit and exit relative errors are at most `a ≤ 1`,
then the common marked lower error is at most `3a`.  This includes the
odds-amplified zero-visit atom. -/
theorem markedPoissonLowerError_le_three_mul
    {q hitError exitError a : ℝ}
    (hq0 : 0 ≤ q) (hqHalf : q ≤ 1 / 2)
    (hhit0 : 0 ≤ hitError) (hexit0 : 0 ≤ exitError)
    (hhit : hitError ≤ a) (hexit : exitError ≤ a)
    (ha1 : a ≤ 1) :
    markedPoissonLowerError q hitError exitError ≤ 3 * a := by
  have ha0 : 0 ≤ a := hhit0.trans hhit
  have hhit1 : hitError ≤ 1 := hhit.trans ha1
  have hexit1 : exitError ≤ 1 := hexit.trans ha1
  have hproduct0 : 0 ≤ hitError * exitError := mul_nonneg hhit0 hexit0
  have hproductA : hitError * exitError ≤ a := by
    calc
      hitError * exitError ≤ hitError * 1 :=
        mul_le_mul_of_nonneg_left hexit1 hhit0
      _ = hitError := mul_one _
      _ ≤ a := hhit
  have hqDenom : 0 < 1 - q := by linarith
  have hodds0 : 0 ≤ q / (1 - q) := div_nonneg hq0 hqDenom.le
  have hodds1 : q / (1 - q) ≤ 1 := by
    rw [div_le_one hqDenom]
    linarith
  have hsum0 : 0 ≤ hitError + exitError + hitError * exitError := by
    positivity
  have hsum : hitError + exitError + hitError * exitError ≤ 3 * a := by
    linarith
  unfold markedPoissonLowerError
  rw [max_le_iff]
  constructor
  · linarith
  · calc
      (hitError + exitError + hitError * exitError) * q / (1 - q) =
          (hitError + exitError + hitError * exitError) * (q / (1 - q)) := by
            ring
      _ ≤ (hitError + exitError + hitError * exitError) * 1 :=
        mul_le_mul_of_nonneg_left hodds1 hsum0
      _ ≤ 3 * a := by simpa only [mul_one] using hsum

private theorem terminalLower_chosenProfile_nonneg
    (s : ℕ) (hs : 2 ≤ s) :
    0 ≤ terminalLower s chosenProfileDelta := by
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
  have hpow : (s : ℝ) ^ (1 + chosenProfileDelta) ≤
      (s : ℝ) ^ (2 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hsR
    unfold chosenProfileDelta
    norm_num
  have hlog : 0 < Real.log s := Real.log_pos (by exact_mod_cast hs)
  unfold terminalLower
  exact div_nonneg (by
    rw [Real.rpow_two] at hpow
    linarith [sq_nonneg (s : ℝ)]) (by positivity)

/-- The literal HLOZ terminal excursion count is bounded by twice the square
of the terminal scale.  The ceiling contributes only one extra excursion. -/
theorem requiredTerminalCount_chosenProfile_le_two_sq
    (s : ℕ) (hs : 3 ≤ s) :
    (requiredTerminalCount s chosenProfileDelta : ℝ) ≤
      2 * (s : ℝ) ^ 2 := by
  have hnonneg := terminalLower_chosenProfile_nonneg s (by omega)
  have hceil := requiredTerminalCount_lt_upper s chosenProfileDelta hnonneg
  have hlog : 0 < Real.log s :=
    Real.log_pos (by exact_mod_cast (show 1 < s by omega))
  have hlogOne : (1 : ℝ) ≤ Real.log s := by
    have hmonotone : Real.log (3 : ℝ) ≤ Real.log s :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hs)
    linarith [Real.log_three_gt_d9]
  have hpow0 : 0 ≤ (s : ℝ) ^ (1 + chosenProfileDelta) := by positivity
  have hterminal : terminalLower s chosenProfileDelta ≤ (s : ℝ) ^ 2 := by
    unfold terminalLower
    rw [div_le_iff₀ (by positivity : 0 < 3 * Real.log s)]
    nlinarith [sq_nonneg (s : ℝ)]
  have hsSq : (1 : ℝ) ≤ (s : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
    nlinarith [sq_nonneg (s : ℝ)]
  linarith

/-- Error budget used by the terminal-thickness adapter.  Errors of order
`o(s⁻²)` are more than enough: at the explicit bound `1/(24s²)`, the
product of the all-coordinate marked loss with the number of required
terminal excursions is at most `1/4`. -/
theorem requiredTerminalCount_mul_markedPoissonLowerError_le_quarter
    (s : ℕ) (hs : 3 ≤ s)
    {q hitError exitError : ℝ}
    (hq0 : 0 ≤ q) (hqHalf : q ≤ 1 / 2)
    (hhit0 : 0 ≤ hitError) (hexit0 : 0 ≤ exitError)
    (hhit : hitError ≤ 1 / (24 * (s : ℝ) ^ 2))
    (hexit : exitError ≤ 1 / (24 * (s : ℝ) ^ 2)) :
    (requiredTerminalCount s chosenProfileDelta : ℝ) *
        markedPoissonLowerError q hitError exitError ≤ 1 / 4 := by
  let a : ℝ := 1 / (24 * (s : ℝ) ^ 2)
  have hsReal : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    rw [div_le_one (by positivity : 0 < 24 * (s : ℝ) ^ 2)]
    have hsCast : (3 : ℝ) ≤ s := by exact_mod_cast hs
    nlinarith [sq_nonneg (s : ℝ)]
  have heta := markedPoissonLowerError_le_three_mul hq0 hqHalf
    hhit0 hexit0 (by simpa [a] using hhit) (by simpa [a] using hexit) ha1
  have heta0 : 0 ≤ markedPoissonLowerError q hitError exitError := by
    unfold markedPoissonLowerError
    apply le_max_of_le_left
    have hhit1 : hitError ≤ 1 := hhit.trans ha1
    nlinarith [mul_nonneg hexit0 (sub_nonneg.mpr hhit1)]
  have hm := requiredTerminalCount_chosenProfile_le_two_sq s hs
  calc
    (requiredTerminalCount s chosenProfileDelta : ℝ) *
          markedPoissonLowerError q hitError exitError ≤
        (2 * (s : ℝ) ^ 2) * (3 * a) :=
      mul_le_mul hm heta heta0 (by positivity)
    _ = 1 / 4 := by
      dsimp [a]
      field_simp
      ring

end

end Erdos1165.TerminalMarkedErrorBounds
