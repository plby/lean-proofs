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
import ErdosProblems.Erdos1165.AsymmetricTerminalPartitionAdapter

/-!
# The concrete asymmetric terminal/radial far-pair constructor

The terminal partition deletes only the terminal bridges at `y` and keeps
all other increments, including the complete `x` history, in its complement.
This module connects that partition to a compatible post-separation radial
cover.  It is the concrete `ActualMarkedFarPairData` constructor used by the
eventual literal-pair endpoint.
-/

open MeasureTheory Set

namespace Erdos1165.AsymmetricTerminalRadialFarPair

open AnnularProfileSequentialUpper AppendixPairCrossingTail
open AsymmetricActualFarPairConstructor AsymmetricActualFarPairData
open AsymmetricCompatibleRadialFamily AsymmetricPairPartitionUpper
open AsymmetricTerminalPartitionAdapter
open Proposition13Assembly Proposition13LiteralAssembly Proposition13Scales
open TerminalMarkedParameterBounds

noncomputable section

/-- Assemble the concrete right-only terminal partition and any literal
scanner-compatible radial cover of its unmarked union. -/
def of_terminalPartition_compatibleRadial
    {delta : ℝ} {n : ℕ} {historyGain : ℝ}
    {i : Fin (chosenBlockCount delta n)} {x y : Point}
    (terminal : TerminalMarkedScaleCertificate delta (scaleIndex delta n))
    (radial : ProfileRadialTailCertificate delta n x y)
    (retained : Set StepPath)
    (radialFamily : CompatibleRadialFamily
      (asymmetricSuccessful
        (skeletonAtom
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta y))
      retained radial.radialTail)
    (onePointFamily : SequentialProfileUpperFamily
      ((i : ℕ) * chosenBlockLength delta n) (scaleIndex delta n)
      chosenProfileDelta historyGain x)
    (hretainedSubset : retained ⊆ stoppedSuccessfulPointEvent
      ((i : ℕ) * chosenBlockLength delta n)
      (scaleIndex delta n) chosenProfileDelta x)
    (hprofileTail : ProfileWeightUpper.profileUpperTailStart ≤
      scaleIndex delta n)
    (hhistoryGain : historyGain ≤
      Real.exp prefixProfileCostDeficit) :
    ActualMarkedFarPairData delta n (Real.exp (1 / 4)) i x y := by
  let start := (i : ℕ) * chosenBlockLength delta n
  let scale := scaleIndex delta n
  have hscale2 : 2 ≤ scale := by
    dsimp only [scale]
    have hscale4 := terminal.marked.scale_ge_four
    omega
  have hscale1 : 1 ≤ scale := by omega
  exact of_literalAsymmetricCompatibleRows terminal radial
    (skeletonAtom start scale chosenProfileDelta y)
    (markedAtom start scale chosenProfileDelta y)
    (Complement start scale chosenProfileDelta y)
    (UnmarkedBridge chosenProfileDelta scale y)
    (MarkedBridge chosenProfileDelta scale y)
    (fun data entrance exit ↦
      unmarkedFactor (start := start) hscale1 data entrance exit)
    (fun data entrance exit visits ↦
      markedFactor (start := start) hscale1 data entrance exit visits)
    (skeletonAtom_event hscale1)
    (markedAtom_event hscale1)
    (markedFactor_complementWord hscale1)
    (unmarkedFactor_kernel hscale1)
    (markedFactor_kernel hscale2)
    (skeletonAtom_pairwise start scale chosenProfileDelta y)
    (TerminalMarkedSkeletonDecomposition.terminalMarkedAtom_pairwise
      start scale chosenProfileDelta y)
    (thickPair_subset_markedUnion hscale1)
    retained radialFamily onePointFamily hretainedSubset hprofileTail
    hhistoryGain le_rfl

end

end Erdos1165.AsymmetricTerminalRadialFarPair
