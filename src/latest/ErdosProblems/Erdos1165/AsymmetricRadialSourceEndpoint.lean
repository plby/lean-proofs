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

import ErdosProblems.Erdos1165.AsymmetricLiteralPairEndpoint
import ErdosProblems.Erdos1165.AsymmetricTerminalRadialFarPair

/-!
# Source-facing endpoint for the asymmetric radial cover

This is the final interface immediately above the retained-code extractor.
It asks only for the concrete sequential one-point family and, for every far
pair, a scanner-compatible radial cover of the global right-only terminal
partition.  The terminal partition and `ActualMarkedFarPairData` record are
constructed internally.
-/

open Filter MeasureTheory Set

namespace Erdos1165.AsymmetricRadialSourceEndpoint

open AnnularProfileSequentialUpper AppendixPair AppendixPairMoment
open AppendixPairCrossingTail AsymmetricActualFarPairData
open AsymmetricCompatibleRadialFamily AsymmetricLiteralPairEndpoint
open AsymmetricPairPartitionUpper AsymmetricTerminalPartitionAdapter
open AsymmetricTerminalRadialFarPair
open Proposition13Assembly Proposition13LiteralAssembly Proposition13Scales

noncomputable section

/-- The actual retained-code/radial-word source package at one scale. -/
structure AsymmetricRadialSourceData (delta : ℝ) (n : ℕ) : Type 2 where
  onePointFamily : ∀ (i : Fin (chosenBlockCount delta n)) (x : Point),
    x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      SequentialProfileUpperFamily
        ((i : ℕ) * chosenBlockLength delta n)
        (scaleIndex delta n) chosenProfileDelta
        (Real.exp prefixProfileCostDeficit) x
  retained : ∀ (i : Fin (chosenBlockCount delta n)) (x : Point),
    x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
    ∀ (y : Point), y ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      separationLevel (scaleIndex delta n) x y ≤
        decorrelationCutoff (scaleIndex delta n) →
      ProfileRadialTailCertificate delta n x y → Set StepPath
  radialFamily : ∀ (i : Fin (chosenBlockCount delta n)) (x : Point)
      (hx : x ∈ ThickPoint.candidateBox (scaleIndex delta n))
      (y : Point) (hy : y ∈ ThickPoint.candidateBox (scaleIndex delta n))
      (hlevel : separationLevel (scaleIndex delta n) x y ≤
        decorrelationCutoff (scaleIndex delta n))
      (radial : ProfileRadialTailCertificate delta n x y),
    CompatibleRadialFamily
      (asymmetricSuccessful
        (skeletonAtom
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta y))
      (retained i x hx y hy hlevel radial) radial.radialTail
  retained_subset : ∀ (i : Fin (chosenBlockCount delta n)) (x : Point)
      (hx : x ∈ ThickPoint.candidateBox (scaleIndex delta n))
      (y : Point) (hy : y ∈ ThickPoint.candidateBox (scaleIndex delta n))
      (hlevel : separationLevel (scaleIndex delta n) x y ≤
        decorrelationCutoff (scaleIndex delta n))
      (radial : ProfileRadialTailCertificate delta n x y),
    retained i x hx y hy hlevel radial ⊆
      stoppedSuccessfulPointEvent
        ((i : ℕ) * chosenBlockLength delta n)
        (scaleIndex delta n) chosenProfileDelta x

/-- Convert the retained-code source package to the small final endpoint
record. -/
def AsymmetricRadialSourceData.toPairSourceData
    {delta : ℝ} {n : ℕ}
    (source : AsymmetricRadialSourceData delta n)
    (htail : ProfileWeightUpper.profileUpperTailStart ≤ scaleIndex delta n) :
    AsymmetricPairSourceData delta n where
  onePointFamily := source.onePointFamily
  farPairData := by
    intro terminal i x hx y hy hlevel radial
    exact of_terminalPartition_compatibleRadial terminal radial
      (source.retained i x hx y hy hlevel radial)
      (source.radialFamily i x hx y hy hlevel radial)
      (source.onePointFamily i x hx)
      (source.retained_subset i x hx y hy hlevel radial)
      htail le_rfl

/-- Eventual retained-code extractors therefore give the exact requested
literal pair data. -/
theorem eventually_nonempty_literalPairData_of_radialSource
    {delta : ℝ} (hdelta : 0 < delta)
    (hsource : ∀ᶠ n : ℕ in atTop,
      Nonempty (AsymmetricRadialSourceData delta n)) :
    ∀ᶠ n : ℕ in atTop, Nonempty (LiteralPairData delta n) := by
  have htail : ∀ᶠ n : ℕ in atTop,
      ProfileWeightUpper.profileUpperTailStart ≤ scaleIndex delta n := by
    have hreal := (tendsto_scaleIndex_atTop delta).eventually
      (eventually_ge_atTop
        (ProfileWeightUpper.profileUpperTailStart : ℝ))
    filter_upwards [hreal] with n hn
    exact_mod_cast hn
  apply eventually_nonempty_literalPairData_of_source hdelta
  filter_upwards [hsource, htail] with n hsourceN htailN
  exact ⟨(AsymmetricRadialSourceData.toPairSourceData
    (Classical.choice hsourceN) htailN)⟩

end

end Erdos1165.AsymmetricRadialSourceEndpoint
