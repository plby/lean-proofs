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

import ErdosProblems.Erdos1165.AppendixPairTerminalBudget
import ErdosProblems.Erdos1165.TerminalMarkedParameterBounds

/-!
# The terminal analytic certificate supplies the far-pair upper loss

This is the thin numerical adapter between the literal terminal Poisson
certificate and the marked-kernel product used in the far-pair estimate.
The analytic certificate bounds the accumulated scalar upper error by
`1/4`; the finite-product inequality then turns this into an `exp (1/4)`
loss, which is eventually absorbed by the reserved scale cost.
-/

open Filter
open scoped BigOperators ENNReal Topology

namespace Erdos1165.AppendixPairTerminalCertificate

open AppendixLocalTime AppendixPairMoment AppendixPairTerminalBudget
open PoissonKernelMarkedHarnack Proposition13Scales
open TerminalMarkedParameterBounds TerminalParameterBounds

noncomputable section

/-- At a scale carrying the full terminal analytic certificate, the product
of all actual marked upper losses is at most `exp (1/4)`. -/
theorem terminalMarkedUpperLossProduct_le_exp_quarter
    (s : ℕ) (cert : TerminalMarkedAnalyticCertificate s) :
    (∏ _j : Fin (requiredTerminalCount s chosenProfileDelta),
      ENNReal.ofReal
        (markedPoissonUpperLoss (terminalHitProbability s)
          (terminalHitRelativeError s)
          (terminalPoissonExitError s (s ^ 8)))).toReal ≤
      Real.exp (1 / 4) := by
  have herror0 : 0 ≤ terminalMarkedPoissonUpperError s (s ^ 8)
      (terminalHitRelativeError s) :=
    markedPoissonUpperError_nonneg cert.hitError_nonneg cert.exitError_nonneg
  have hprod := prod_terminalMarkedPoissonUpperFactor_toReal_le_exp
    (requiredTerminalCount s chosenProfileDelta) s (s ^ 8)
    (terminalHitRelativeError s) (1 / 4) herror0
    cert.markedUpperLoss_quarter
  simpa only [one_add_terminalMarkedPoissonUpperError_eq_loss] using hprod

/-- The literal terminal upper loss fits the exact far-pair scale budget at
all sufficiently large selected Proposition 1.3 scales. -/
theorem eventually_terminalMarkedUpperLossProduct_le_scaleCost
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      (∏ _j : Fin
          (requiredTerminalCount (scaleIndex delta n) chosenProfileDelta),
        ENNReal.ofReal
          (markedPoissonUpperLoss
            (terminalHitProbability (scaleIndex delta n))
            (terminalHitRelativeError (scaleIndex delta n))
            (terminalPoissonExitError (scaleIndex delta n)
              ((scaleIndex delta n) ^ 8)))).toReal ≤
        Real.exp (scaleCost delta n / 64) := by
  have hcert := eventually_terminalMarkedScaleCertificate_scaleIndex hdelta
  have hquarter := eventually_constant_le_sixtyFourth_scaleCost
    (delta := delta) (C := (1 / 4 : ℝ)) hdelta
  filter_upwards [hcert, hquarter] with n cert hquarter
  exact (terminalMarkedUpperLossProduct_le_exp_quarter
    (scaleIndex delta n) cert.marked).trans (Real.exp_le_exp.mpr hquarter)

end

end Erdos1165.AppendixPairTerminalCertificate
