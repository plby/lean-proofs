/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricActualFarPairConstructor
import ErdosProblems.Erdos1165.AsymmetricCompatibleRadialCompletionFamily
import ErdosProblems.Erdos1165.AsymmetricTerminalPartitionAdapter

/-!
# Terminal far-pair constructor from genuine completion atoms

This is the concrete terminal-partition specialization for a radial family
whose retained atoms are renewal-completion events rather than synthetic
cylinders.
-/

open MeasureTheory Set

namespace Erdos1165.AsymmetricTerminalCompletionFarPair

open AnnularProfileSequentialUpper AppendixPairCrossingTail
open AsymmetricActualFarPairConstructor AsymmetricActualFarPairData
open AsymmetricCompatibleRadialCompletionFamily
open AsymmetricPairPartitionUpper AsymmetricTerminalPartitionAdapter
open Proposition13Assembly Proposition13LiteralAssembly Proposition13Scales
open TerminalMarkedParameterBounds

noncomputable section

/-- Assemble the concrete right-only terminal partition with a genuine
coarse-completion/deeper-tail radial family. -/
def of_terminalPartition_compatibleRadialCompletion
    {delta : ℝ} {n : ℕ} {historyGain : ℝ}
    {i : Fin (chosenBlockCount delta n)} {x y : Point}
    (terminal : TerminalMarkedScaleCertificate delta (scaleIndex delta n))
    (radial : ProfileRadialTailCertificate delta n x y)
    (retained : Set StepPath)
    (radialFamily : CompatibleRadialCompletionFamily
      (asymmetricSuccessful
        (skeletonAtom
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta y))
      retained
      (stoppedSuccessfulPointEvent
        ((i : ℕ) * chosenBlockLength delta n)
        (scaleIndex delta n) chosenProfileDelta x)
      radial.radialTail)
    (onePointFamily : SequentialProfileUpperFamily
      ((i : ℕ) * chosenBlockLength delta n) (scaleIndex delta n)
      chosenProfileDelta historyGain x)
    (hprofileTail : ProfileWeightUpper.profileUpperTailStart ≤
      scaleIndex delta n)
    (hhistoryGain : historyGain ≤ Real.exp prefixProfileCostDeficit) :
    ActualMarkedFarPairData delta n (Real.exp (1 / 4)) i x y := by
  let start := (i : ℕ) * chosenBlockLength delta n
  let scale := scaleIndex delta n
  have hscale2 : 2 ≤ scale := by
    dsimp only [scale]
    have hscale4 := terminal.marked.scale_ge_four
    omega
  have hscale1 : 1 ≤ scale := by omega
  exact of_literalAsymmetricAtoms terminal radial
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
    retained radialFamily.TailCode radialFamily.retainedAtom
    radialFamily.tailAtom radialFamily.tailWeight
    radialFamily.successful_subset radialFamily.retained_eq
    radialFamily.retained_measurable radialFamily.retained_pairwise
    radialFamily.tail_mass radialFamily.row_le onePointFamily
    radialFamily.retained_subset hprofileTail hhistoryGain le_rfl

end

end Erdos1165.AsymmetricTerminalCompletionFarPair
