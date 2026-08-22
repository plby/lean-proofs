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

import ErdosProblems.Erdos1165.AsymmetricCompatibleFullProfileRows
import ErdosProblems.Erdos1165.AsymmetricRadialSourceEndpoint

/-!
# Full-profile retained-row endpoint for the asymmetric pair bound

This is the source-facing form of the final asymmetric endpoint.  A source
extractor supplies a countable prefix-free retained-code cover and the
unrestricted renewal-row estimate for the actual full profile of each code.
Scanner compatibility and the uniform radial-tail comparison are derived
internally by `FullProfileCompatibleRows.toCompatibleRadialFamily`.

No event-probability comparison or final pair-bound scalar is a premise.
-/

open Filter MeasureTheory Set

namespace Erdos1165.AsymmetricFullProfileRadialSourceEndpoint

open AnnularProfileSequentialUpper AppendixPair AppendixPairCrossingTail
open AppendixPairMoment AsymmetricActualFarPairData
open AsymmetricCompatibleFullProfileRows AsymmetricCompatibleRadialFamily
open AsymmetricPairPartitionUpper
open AsymmetricRadialSourceEndpoint AsymmetricTerminalPartitionAdapter
open Proposition13Assembly Proposition13LiteralAssembly Proposition13Scales

noncomputable section

/-- Literal source rows before scanner restriction.  In particular,
`rows.unrestricted_row` is the actual fixed-prefix A.6 renewal estimate and
`rows.retained_prefixFree` is the retained-cylinder partition. -/
structure AsymmetricFullProfileRadialSourceData
    (delta : ℝ) (n : ℕ) : Type 2 where
  onePointFamily : ∀ (i : Fin (chosenBlockCount delta n)) (x : Point),
    x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      SequentialProfileUpperFamily
        ((i : ℕ) * chosenBlockLength delta n)
        (scaleIndex delta n) chosenProfileDelta
        (Real.exp prefixProfileCostDeficit) x
  retained : ∀ (_i : Fin (chosenBlockCount delta n)) (x : Point),
    x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
    ∀ (y : Point), y ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      separationLevel (scaleIndex delta n) x y ≤
        decorrelationCutoff (scaleIndex delta n) →
      ProfileRadialTailCertificate delta n x y → Set StepPath
  rows : ∀ (i : Fin (chosenBlockCount delta n)) (x : Point)
      (hx : x ∈ ThickPoint.candidateBox (scaleIndex delta n))
      (y : Point) (hy : y ∈ ThickPoint.candidateBox (scaleIndex delta n))
      (hlevel : separationLevel (scaleIndex delta n) x y ≤
        decorrelationCutoff (scaleIndex delta n))
      (radial : ProfileRadialTailCertificate delta n x y),
    FullProfileCompatibleRows
      (asymmetricSuccessful
        (skeletonAtom
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta y))
      (retained i x hx y hy hlevel radial) radial
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

/-- Restrict the source's erased return rows by their retained scanner
transition and obtain the compatible family used by the far-pair
constructor. -/
def AsymmetricFullProfileRadialSourceData.toRadialSourceData
    {delta : ℝ} {n : ℕ}
    (source : AsymmetricFullProfileRadialSourceData delta n) :
    AsymmetricRadialSourceData delta n where
  onePointFamily := source.onePointFamily
  retained := source.retained
  radialFamily := by
    intro i x hx y hy hlevel radial
    exact (source.rows i x hx y hy hlevel radial).toCompatibleRadialFamily
  retained_subset := source.retained_subset

/-- Eventual literal full-profile retained-row extractors give the requested
asymmetric literal pair data. -/
theorem eventually_nonempty_literalPairData_of_fullProfileRadialSource
    {delta : ℝ} (hdelta : 0 < delta)
    (hsource : ∀ᶠ n : ℕ in atTop,
      Nonempty (AsymmetricFullProfileRadialSourceData delta n)) :
    ∀ᶠ n : ℕ in atTop, Nonempty (LiteralPairData delta n) := by
  apply eventually_nonempty_literalPairData_of_radialSource hdelta
  filter_upwards [hsource] with n hsourceN
  exact ⟨(AsymmetricFullProfileRadialSourceData.toRadialSourceData
    (Classical.choice hsourceN))⟩

end

end Erdos1165.AsymmetricFullProfileRadialSourceEndpoint
