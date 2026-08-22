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

import ErdosProblems.Erdos1165.AsymmetricActualFarPairConstructor
import ErdosProblems.Erdos1165.AppendixPairTerminalBudget

/-!
# Eventual endpoint for the asymmetric literal pair construction

This file isolates the final quantifier and numerical assembly.  The
walk-facing source construction supplies a sequential one-point upper
family and an actual asymmetric far-pair record.  All scale certificates,
the `exp (1/4)` Harnack choice, and the point-envelope comparison are filled
here, without a scalar pair-bound premise.
-/

open Filter MeasureTheory Set

namespace Erdos1165.AsymmetricLiteralPairEndpoint

open AnnularProfileSequentialUpper AppendixPair AppendixPairMoment
open AppendixPairCrossingTail
open AppendixPairCrossingTailLiteral AppendixPairTerminalBudget
open AppendixPairTerminalCertificate AsymmetricActualFarPairData
open GaussianGeometricSchedule ProfileWeightUpper
open Proposition13Assembly Proposition13LiteralAssembly Proposition13Scales
open TerminalMarkedParameterBounds

noncomputable section

/-- Walk-facing data still needed at one fixed selected scale.  The far-pair
field is an `ActualMarkedFarPairData` object, so it contains the literal
marked/unmarked stopped-word decomposition and the asymmetric compatible
radial rows rather than a final probability comparison. -/
structure AsymmetricPairSourceData (delta : ℝ) (n : ℕ) : Type 1 where
  onePointFamily : ∀ (i : Fin (chosenBlockCount delta n)) (x : Point),
    x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      SequentialProfileUpperFamily
        ((i : ℕ) * chosenBlockLength delta n)
        (scaleIndex delta n) chosenProfileDelta
        (Real.exp prefixProfileCostDeficit) x
  farPairData :
    TerminalMarkedScaleCertificate delta (scaleIndex delta n) →
      ∀ (i : Fin (chosenBlockCount delta n)) (x : Point),
        x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      ∀ (y : Point), y ∈ ThickPoint.candidateBox (scaleIndex delta n) →
        separationLevel (scaleIndex delta n) x y ≤
          decorrelationCutoff (scaleIndex delta n) →
        ProfileRadialTailCertificate delta n x y →
          ActualMarkedFarPairData delta n (Real.exp (1 / 4)) i x y

/-- Fixed-scale assembly from source data and the two canonical analytic
certificates. -/
def literalPairDataOfSource
    {delta : ℝ} {n : ℕ}
    (source : AsymmetricPairSourceData delta n)
    (terminal : TerminalMarkedScaleCertificate delta (scaleIndex delta n))
    (radial : ∀ x y : Point,
      separationLevel (scaleIndex delta n) x y ≤
          decorrelationCutoff (scaleIndex delta n) →
        ProfileRadialTailCertificate delta n x y)
    (htail : profileUpperTailStart ≤ scaleIndex delta n)
    (hbudget : (1 / 4 : ℝ) ≤ scaleCost delta n / 64) :
    LiteralPairData delta n where
  harnackFactor := Real.exp (1 / 4)
  harnackFactor_nonneg := Real.exp_nonneg _
  harnackFactor_le_budget := Real.exp_le_exp.mpr hbudget
  onePointUpper := by
    intro i x hx
    exact successful_le_pairPointEnvelope_of_sequentialUpperFamily
      (stoppedThickPointEvent
        ((i : ℕ) * chosenBlockLength delta n)
        (scaleIndex delta n) chosenProfileDelta
        (chosenThickDelta delta) x)
      (source.onePointFamily i x hx)
      (stoppedThickPointEvent_subset_stoppedSuccessfulPointEvent
        ((i : ℕ) * chosenBlockLength delta n)
        (scaleIndex delta n) chosenProfileDelta
        (chosenThickDelta delta) x)
      htail le_rfl
  farPairData := by
    intro i x hx y hy hlevel
    exact source.farPairData terminal i x hx y hy hlevel
      (radial x y hlevel)

/-- Once the source-indexed stopped-word construction is available
eventually, the exact final target follows with no additional comparison or
limit premise. -/
theorem eventually_nonempty_literalPairData_of_source
    {delta : ℝ} (hdelta : 0 < delta)
    (hsource : ∀ᶠ n : ℕ in atTop,
      Nonempty (AsymmetricPairSourceData delta n)) :
    ∀ᶠ n : ℕ in atTop, Nonempty (LiteralPairData delta n) := by
  have htail : ∀ᶠ n : ℕ in atTop,
      profileUpperTailStart ≤ scaleIndex delta n := by
    have hreal := (tendsto_scaleIndex_atTop delta).eventually
      (eventually_ge_atTop (profileUpperTailStart : ℝ))
    filter_upwards [hreal] with n hn
    exact_mod_cast hn
  filter_upwards
      [hsource,
       eventually_terminalMarkedScaleCertificate_scaleIndex hdelta,
       eventually_profileRadialTailCertificate_expOne,
       htail,
       eventually_constant_le_sixtyFourth_scaleCost
         (delta := delta) (C := (1 / 4 : ℝ)) hdelta]
      with n hsourceN hterminal hradial htailN hbudget
  let source := Classical.choice hsourceN
  refine ⟨literalPairDataOfSource source hterminal ?_ htailN hbudget⟩
  intro x y hlevel
  exact Classical.choice (hradial x y hlevel)

end

end Erdos1165.AsymmetricLiteralPairEndpoint
