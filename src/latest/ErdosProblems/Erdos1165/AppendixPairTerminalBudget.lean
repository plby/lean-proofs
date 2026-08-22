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

import ErdosProblems.Erdos1165.AppendixPairReferenceMass
import ErdosProblems.Erdos1165.TerminalMarkedErrorBounds

/-!
# Terminal marked-kernel budget for the far-pair estimate

This file supplies the upper counterpart of the terminal marked-kernel
numerics.  At the literal radii `s^6 < s^8 < s^9`, the Poisson exit error is
`O(s⁻²)`.  Together with the sharper point-hit error and the fact that the
number of terminal coordinates is at most `2s²`, the full product of marked
upper losses is absorbed by the reserved scale cost.
-/

open Filter Set
open scoped BigOperators ENNReal Topology

namespace Erdos1165.AppendixPairTerminalBudget

open AppendixLocalTime AppendixPairMoment PoissonKernelGreenPole
open PoissonKernelHarnack PoissonKernelMarkedHarnack Proposition13Scales
open TerminalMarkedErrorBounds
open TerminalParameterBounds ThickPoint

noncomputable section

/-- The marked upper error is controlled by twice the sum of the point-hit
and exit-endpoint relative errors.  This is the upper analogue of the
three-error lower estimate in `TerminalMarkedErrorBounds`. -/
theorem markedPoissonUpperError_le_two_mul
    {q hitError exitError : ℝ}
    (hq0 : 0 ≤ q) (hqHalf : q ≤ 1 / 2)
    (hhit0 : 0 ≤ hitError) (hexit0 : 0 ≤ exitError)
    (hexit1 : exitError ≤ 1) :
    markedPoissonUpperError q hitError exitError ≤
      2 * (hitError + exitError) := by
  have hloss := markedPoissonUpperLoss_le_one_add_two_errors
    hq0 hqHalf hhit0 hexit0 hexit1
  have heq : 1 + markedPoissonUpperError q hitError exitError =
      markedPoissonUpperLoss q hitError exitError := by
    unfold markedPoissonUpperError markedPoissonUpperLoss
    rw [add_max]
    congr 1
    all_goals ring
  rw [← heq] at hloss
  linarith

lemma markedPoissonUpperError_nonneg
    {q hitError exitError : ℝ}
    (hhit0 : 0 ≤ hitError) (hexit0 : 0 ≤ exitError) :
    0 ≤ markedPoissonUpperError q hitError exitError := by
  unfold markedPoissonUpperError
  apply le_max_of_le_left
  positivity

/-- A rate-form terminal estimate.  It deliberately takes the two analytic
rate inequalities separately, so the point-hit and Green-pole files remain
independent. -/
theorem requiredTerminalCount_mul_terminalMarkedPoissonUpperError_le_constant
    (s : ℕ) (hs : 3 ≤ s)
    {hitError hitConstant exitConstant : ℝ}
    (hqHalf : terminalHitProbability s ≤ 1 / 2)
    (hhit0 : 0 ≤ hitError)
    (hexit0 : 0 ≤ terminalPoissonExitError s (s ^ 8))
    (hexit1 : terminalPoissonExitError s (s ^ 8) ≤ 1)
    (hhitConstant0 : 0 ≤ hitConstant)
    (hhit : hitError ≤ hitConstant / (s : ℝ) ^ 6)
    (hexit : terminalPoissonExitError s (s ^ 8) ≤
      exitConstant / (s : ℝ) ^ 2) :
    (requiredTerminalCount s chosenProfileDelta : ℝ) *
        terminalMarkedPoissonUpperError s (s ^ 8) hitError ≤
      4 * (hitConstant + exitConstant) := by
  have hsreal : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
  have hspos : (0 : ℝ) < s := zero_lt_one.trans_le hsreal
  have hupper := markedPoissonUpperError_le_two_mul
    (terminalHitProbability_nonneg s) hqHalf hhit0 hexit0 hexit1
  change terminalMarkedPoissonUpperError s (s ^ 8) hitError ≤
      2 * (hitError + terminalPoissonExitError s (s ^ 8)) at hupper
  have hupper0 : 0 ≤ terminalMarkedPoissonUpperError s (s ^ 8) hitError := by
    unfold terminalMarkedPoissonUpperError
    exact markedPoissonUpperError_nonneg
      (q := terminalHitProbability s) hhit0 hexit0
  have hm := requiredTerminalCount_chosenProfile_le_two_sq s hs
  have hsum : hitError + terminalPoissonExitError s (s ^ 8) ≤
      hitConstant / (s : ℝ) ^ 6 + exitConstant / (s : ℝ) ^ 2 := by
    linarith
  calc
    (requiredTerminalCount s chosenProfileDelta : ℝ) *
          terminalMarkedPoissonUpperError s (s ^ 8) hitError ≤
        (2 * (s : ℝ) ^ 2) *
          (2 * (hitError + terminalPoissonExitError s (s ^ 8))) :=
      mul_le_mul hm hupper hupper0 (by positivity)
    _ ≤ (2 * (s : ℝ) ^ 2) *
          (2 * (hitConstant / (s : ℝ) ^ 6 +
            exitConstant / (s : ℝ) ^ 2)) := by
      gcongr
    _ = 4 * (hitConstant / (s : ℝ) ^ 4 + exitConstant) := by
      field_simp
      ring
    _ ≤ 4 * (hitConstant + exitConstant) := by
      have hs4 : (1 : ℝ) ≤ (s : ℝ) ^ 4 := one_le_pow₀ hsreal
      have hdiv : hitConstant / (s : ℝ) ^ 4 ≤ hitConstant := by
        rw [div_le_iff₀ (pow_pos hspos 4)]
        nlinarith
      linarith

/-- The exponent appearing in the finite-product upper estimate has the
same constant bound. -/
theorem two_mul_requiredTerminalCount_mul_errors_le_constant
    (s : ℕ) (hs : 3 ≤ s)
    {hitError exitError hitConstant exitConstant : ℝ}
    (hhit0 : 0 ≤ hitError) (hexit0 : 0 ≤ exitError)
    (hhitConstant0 : 0 ≤ hitConstant)
    (hhit : hitError ≤ hitConstant / (s : ℝ) ^ 6)
    (hexit : exitError ≤ exitConstant / (s : ℝ) ^ 2) :
    2 * (requiredTerminalCount s chosenProfileDelta : ℝ) *
        (hitError + exitError) ≤
      4 * (hitConstant + exitConstant) := by
  have hsreal : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
  have hspos : (0 : ℝ) < s := zero_lt_one.trans_le hsreal
  have hm := requiredTerminalCount_chosenProfile_le_two_sq s hs
  have hsum : hitError + exitError ≤
      hitConstant / (s : ℝ) ^ 6 + exitConstant / (s : ℝ) ^ 2 := by
    linarith
  calc
    2 * (requiredTerminalCount s chosenProfileDelta : ℝ) *
          (hitError + exitError) ≤
        2 * (2 * (s : ℝ) ^ 2) * (hitError + exitError) := by
      gcongr
    _ ≤ 2 * (2 * (s : ℝ) ^ 2) *
          (hitConstant / (s : ℝ) ^ 6 +
            exitConstant / (s : ℝ) ^ 2) := by
      have hsum0 : 0 ≤
          hitConstant / (s : ℝ) ^ 6 + exitConstant / (s : ℝ) ^ 2 :=
        (add_nonneg hhit0 hexit0).trans hsum
      gcongr
    _ = 4 * (hitConstant / (s : ℝ) ^ 4 + exitConstant) := by
      field_simp
      ring
    _ ≤ 4 * (hitConstant + exitConstant) := by
      have hs4 : (1 : ℝ) ≤ (s : ℝ) ^ 4 := one_le_pow₀ hsreal
      have hdiv : hitConstant / (s : ℝ) ^ 4 ≤ hitConstant := by
        rw [div_le_iff₀ (pow_pos hspos 4)]
        nlinarith
      linarith

/-- Any fixed terminal comparison constant is eventually absorbed by one
sixty-fourth of the positive scale cost. -/
theorem eventually_constant_le_sixtyFourth_scaleCost
    {delta C : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop, C ≤ scaleCost delta n / 64 := by
  have htop := ((tendsto_rpow_atTop (costExponent_pos hdelta)).comp
    (tendsto_scaleIndex_atTop delta)).eventually
      (eventually_ge_atTop (64 * C))
  filter_upwards [htop] with n hn
  simp only [Function.comp_apply] at hn
  unfold scaleCost
  linarith

lemma one_add_terminalMarkedPoissonUpperError_eq_loss
    (s S : ℕ) (hitError : ℝ) :
    1 + terminalMarkedPoissonUpperError s S hitError =
      markedPoissonUpperLoss (terminalHitProbability s) hitError
        (terminalPoissonExitError s S) := by
  unfold terminalMarkedPoissonUpperError markedPoissonUpperError
    markedPoissonUpperLoss
  rw [add_max]
  congr 1
  all_goals ring

/-- If the accumulated scalar terminal upper error is at most `H`, then the
actual constant-coordinate ENNReal loss product is at most `exp H`. -/
theorem prod_terminalMarkedPoissonUpperFactor_toReal_le_exp
    (m s S : ℕ) (hitError H : ℝ)
    (herror0 : 0 ≤ terminalMarkedPoissonUpperError s S hitError)
    (hbudget : (m : ℝ) *
      terminalMarkedPoissonUpperError s S hitError ≤ H) :
    (∏ _j : Fin m, ENNReal.ofReal
      (1 + terminalMarkedPoissonUpperError s S hitError)).toReal ≤
        Real.exp H := by
  rw [ENNReal.toReal_prod]
  simp only [ENNReal.toReal_ofReal (by linarith :
    0 ≤ 1 + terminalMarkedPoissonUpperError s S hitError)]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    ((pow_one_add_le_exp_nat_mul herror0 m).trans
      (Real.exp_le_exp.mpr hbudget))

/-- Constant-coordinate specialization of the marked upper product. -/
theorem prod_terminalMarkedPoissonUpperFactor_toReal_le_scaleCost
    {delta : ℝ} {n s : ℕ} (hs : 3 ≤ s)
    {hitError hitConstant exitConstant : ℝ}
    (hqHalf : terminalHitProbability s ≤ 1 / 2)
    (hhit0 : 0 ≤ hitError)
    (hexit0 : 0 ≤ terminalPoissonExitError s (s ^ 8))
    (hexit1 : terminalPoissonExitError s (s ^ 8) ≤ 1)
    (hhitConstant0 : 0 ≤ hitConstant)
    (hhit : hitError ≤ hitConstant / (s : ℝ) ^ 6)
    (hexit : terminalPoissonExitError s (s ^ 8) ≤
      exitConstant / (s : ℝ) ^ 2)
    (hconstant : 4 * (hitConstant + exitConstant) ≤
      scaleCost delta n / 64) :
    (∏ _j : Fin (requiredTerminalCount s chosenProfileDelta),
      ENNReal.ofReal
        (1 + terminalMarkedPoissonUpperError s (s ^ 8) hitError)).toReal ≤
      Real.exp (scaleCost delta n / 64) := by
  let m := requiredTerminalCount s chosenProfileDelta
  let q : Fin m → ℝ := fun _ ↦ terminalHitProbability s
  let hit : Fin m → ℝ := fun _ ↦ hitError
  let exit : Fin m → ℝ := fun _ ↦ terminalPoissonExitError s (s ^ 8)
  have hbudget : 2 * ∑ j, (hit j + exit j) ≤ scaleCost delta n / 64 := by
    have hrate := two_mul_requiredTerminalCount_mul_errors_le_constant
      s hs hhit0 hexit0 hhitConstant0 hhit hexit
    have hsum : ∑ j, (hit j + exit j) =
        (requiredTerminalCount s chosenProfileDelta : ℝ) *
          (hitError + terminalPoissonExitError s (s ^ 8)) := by
      simp [hit, exit, m]
      ring
    rw [hsum]
    nlinarith [hrate, hconstant]
  have hprod := prod_markedPoissonUpperLoss_toReal_le_scaleCost
    (delta := delta) (n := n) q hit exit
    (fun _ ↦ terminalHitProbability_nonneg s)
    (fun _ ↦ hqHalf) (fun _ ↦ hhit0) (fun _ ↦ hexit0)
    (fun _ ↦ hexit1) hbudget
  simpa only [q, hit, exit, m,
    ← one_add_terminalMarkedPoissonUpperError_eq_loss] using hprod

end

end Erdos1165.AppendixPairTerminalBudget
