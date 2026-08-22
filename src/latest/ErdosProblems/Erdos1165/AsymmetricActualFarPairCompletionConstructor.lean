/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricActualFarPairKernelUpperConstructor
import ErdosProblems.Erdos1165.AsymmetricCompatibleRadialCompletionFamily

/-!
# Far-pair construction from genuine asymmetric completion atoms

This is the completion-atom analogue of the final half of
`of_literalAsymmetricKernelUpperRows`.  The terminal decomposition may use
scanner-restricted marked kernels through the existing kernel-upper
constructor.  The radial comparison is supplied by genuine unrestricted
renewal-completion atoms, so the retained one-point inclusion is pathwise
and never refers to the synthetic complement cylinders.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.AsymmetricActualFarPairCompletionConstructor

open AnnularProfileSequentialUpper AppendixLocalTime AppendixPair
open AppendixPairCrossingTail
open AppendixPairMoment AppendixPairTerminalCertificate
open AsymmetricActualFarPairData
open AsymmetricCompatibleRadialCompletionFamily
open MarkedBoundaryVisitKernel MarkedTerminalDisintegration
open Proposition13Assembly
open Proposition13LiteralAssembly Proposition13Scales
open TerminalExcursionPathwise TerminalMarkedParameterBounds
open TerminalMarkedSkeletonDecomposition TerminalParameterBounds
open TerminalSkeletonWords

noncomputable section

/-- Finish an asymmetric kernel-upper terminal decomposition with genuine
unrestricted renewal-completion atoms.  All local terminal kernel
comparisons have already been checked in `decomposition`; this constructor
only threads the sound completion-row mass identity into the two-stage
coefficient. -/
def of_kernelUpperDecomposition_completionRows
    {delta : ℝ} {n : ℕ} {harnackFactor historyGain : ℝ}
    {i : Fin (chosenBlockCount delta n)} {x y : Point}
    (terminalCertificate :
      TerminalMarkedScaleCertificate delta (scaleIndex delta n))
    (radialCertificate : ProfileRadialTailCertificate delta n x y)
    {Data : Type}
    (successful : Set StepPath)
    (skeletonWeight : Data →
      (Fin (requiredTerminalCount (scaleIndex delta n) chosenProfileDelta) →
        TerminalEntrance (scaleIndex delta n) y) →
      (Fin (requiredTerminalCount (scaleIndex delta n) chosenProfileDelta) →
        TerminalExit (scaleIndex delta n) y) → ℝ≥0∞)
    (decomposition : MarkedStoppedDataUpperDecomposition fairSteps
      (stoppedThickPointEvent
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta
          (chosenThickDelta delta) x ∩
        stoppedThickPointEvent
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta
          (chosenThickDelta delta) y)
      successful skeletonWeight
      (fun _ (u : TerminalEntrance (scaleIndex delta n) y)
          (z : TerminalExit (scaleIndex delta n) y) ↦
        terminalSkeletonKernel
          (terminalOuterBoundary (scaleIndex delta n) y) u.1 z.1)
      (fun _ (u : TerminalEntrance (scaleIndex delta n) y) k
          (z : TerminalExit (scaleIndex delta n) y) ↦
        terminalMarkedKernel
          (terminalOuterBoundary (scaleIndex delta n) y) y u.1 k z.1)
      Set.univ)
    (retained : Set StepPath)
    (radialFamily : CompatibleRadialCompletionFamily
      successful retained
      (stoppedSuccessfulPointEvent
        ((i : ℕ) * chosenBlockLength delta n)
        (scaleIndex delta n) chosenProfileDelta x)
      radialCertificate.radialTail)
    (onePointFamily : SequentialProfileUpperFamily
      ((i : ℕ) * chosenBlockLength delta n) (scaleIndex delta n)
      chosenProfileDelta historyGain x)
    (hprofileTail : ProfileWeightUpper.profileUpperTailStart ≤
      scaleIndex delta n)
    (hhistoryGain : historyGain ≤ Real.exp prefixProfileCostDeficit)
    (hloss : Real.exp (1 / 4) ≤ harnackFactor) :
    ActualMarkedFarPairData delta n harnackFactor i x y := by
  have hretainedUpper : fairSteps.real retained ≤ pairPointEnvelope delta n :=
    AppendixPairCrossingTailLiteral.successful_le_pairPointEnvelope_of_sequentialUpperFamily
      retained onePointFamily radialFamily.retained_subset hprofileTail
      hhistoryGain
  exact of_canonicalTerminal_profileAtomWeights terminalCertificate
    radialCertificate successful retained skeletonWeight decomposition
    radialFamily.TailCode
    radialFamily.retainedAtom radialFamily.tailAtom radialFamily.tailWeight
    radialFamily.successful_subset radialFamily.retained_eq
    radialFamily.retained_measurable radialFamily.retained_pairwise
    radialFamily.tail_mass radialFamily.row_le hloss
    hretainedUpper

end

end Erdos1165.AsymmetricActualFarPairCompletionConstructor
