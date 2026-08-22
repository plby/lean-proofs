/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricActualFarPairConstructor
import ErdosProblems.Erdos1165.AsymmetricPairPartitionKernelUpper

/-!
# Asymmetric far-pair constructor with scanner-dominated marked kernels

This is the sound split-level variant of the literal constructor.  The
unmarked unrestricted comparison partition retains its exact canonical
terminal kernel.  The selected scanner-compatible marked bridges need only
be dominated by the canonical marked kernel.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AsymmetricActualFarPairKernelUpperConstructor

open AnnularProfileSequentialUpper AppendixPair AppendixPairCrossingTail
open AppendixPairMoment AppendixPairTerminalCertificate
open AsymmetricActualFarPairConstructor AsymmetricActualFarPairData
open AsymmetricCompatibleRadialFamily AsymmetricPairPartitionKernelUpper
open AsymmetricPairPartitionUpper MarkedBridgeFactorization
open MarkedSkeletonPartition MarkedTerminalDisintegration
open Proposition13Assembly Proposition13LiteralAssembly Proposition13Scales
open TerminalExcursionPathwise TerminalMarkedParameterBounds
open TerminalMarkedSkeletonDecomposition TerminalParameterBounds
open TerminalSkeletonWords

noncomputable section

/-- Construct the literal far-pair record when the marked insertion family
is a scanner-compatible subtype of the canonical terminal family. -/
def of_literalAsymmetricKernelUpperRows
    {delta : ℝ} {n : ℕ} {harnackFactor historyGain : ℝ}
    {i : Fin (chosenBlockCount delta n)} {x y : Point}
    (terminalCertificate :
      TerminalMarkedScaleCertificate delta (scaleIndex delta n))
    (radialCertificate : ProfileRadialTailCertificate delta n x y)
    {Data : Type} [Countable Data]
    (skeletonAtom : Data →
      (Fin (pairTerminalCount delta n) →
        TerminalEntrance (scaleIndex delta n) y) →
      (Fin (pairTerminalCount delta n) →
        TerminalExit (scaleIndex delta n) y) → Set StepPath)
    (markedAtom : Data →
      (Fin (pairTerminalCount delta n) →
        TerminalEntrance (scaleIndex delta n) y) →
      (Fin (pairTerminalCount delta n) →
        TerminalExit (scaleIndex delta n) y) →
      (Fin (pairTerminalCount delta n) → ℕ) → Set StepPath)
    (Complement : Data →
      (Fin (pairTerminalCount delta n) →
        TerminalEntrance (scaleIndex delta n) y) →
      (Fin (pairTerminalCount delta n) →
        TerminalExit (scaleIndex delta n) y) → Type*)
    (UnmarkedBridge : Fin (pairTerminalCount delta n) →
      TerminalEntrance (scaleIndex delta n) y →
      TerminalExit (scaleIndex delta n) y → Type*)
    (MarkedBridge : Fin (pairTerminalCount delta n) →
      TerminalEntrance (scaleIndex delta n) y → ℕ →
      TerminalExit (scaleIndex delta n) y → Type*)
    [∀ data entrance exit, Countable (Complement data entrance exit)]
    [∀ j entrance exit, Countable (UnmarkedBridge j entrance exit)]
    [∀ j entrance visits exit,
      Countable (MarkedBridge j entrance visits exit)]
    (unmarkedFactor : ∀ data entrance exit,
      ComplementarySkeletonAtom (pairTerminalCount delta n)
        (Complement data entrance exit)
        (fun j ↦ UnmarkedBridge j (entrance j) (exit j)))
    (markedFactor : ∀ data entrance exit visits,
      ComplementarySkeletonAtom (pairTerminalCount delta n)
        (Complement data entrance exit)
        (fun j ↦ MarkedBridge j (entrance j) (visits j) (exit j)))
    (hskeleton_event : ∀ data entrance exit,
      skeletonAtom data entrance exit =
        (unmarkedFactor data entrance exit).event)
    (hmarked_event : ∀ data entrance exit visits,
      markedAtom data entrance exit visits =
        (markedFactor data entrance exit visits).event)
    (hcomplementWord : ∀ data entrance exit visits complement,
      (markedFactor data entrance exit visits).complementWord complement =
        (unmarkedFactor data entrance exit).complementWord complement)
    (hunmarkedKernel : ∀ data entrance exit j,
      (unmarkedFactor data entrance exit).kernel j =
        pairTerminalSkeletonKernel delta n y j (entrance j) (exit j))
    (hmarkedKernel : ∀ data entrance exit visits j,
      (markedFactor data entrance exit visits).kernel j ≤
        pairTerminalMarkedKernel delta n y j
          (entrance j) (visits j) (exit j))
    (hskeleton_disjoint : Pairwise fun index₁ index₂ : SkeletonIndex Data
        (TerminalEntrance (scaleIndex delta n) y)
        (TerminalExit (scaleIndex delta n) y)
        (pairTerminalCount delta n) ↦
      Disjoint (indexedSkeletonAtom skeletonAtom index₁)
        (indexedSkeletonAtom skeletonAtom index₂))
    (hmarked_disjoint : Pairwise fun index₁ index₂ : MarkedIndex Data
        (TerminalEntrance (scaleIndex delta n) y)
        (TerminalExit (scaleIndex delta n) y)
        (pairTerminalCount delta n) ↦
      Disjoint (indexedMarkedAtom markedAtom index₁)
        (indexedMarkedAtom markedAtom index₂))
    (hpair_union :
      stoppedThickPointEvent
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta
          (chosenThickDelta delta) x ∩
        stoppedThickPointEvent
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta
          (chosenThickDelta delta) y ⊆
      ⋃ index : MarkedIndex Data
          (TerminalEntrance (scaleIndex delta n) y)
          (TerminalExit (scaleIndex delta n) y)
          (pairTerminalCount delta n),
        restrictedMarkedAtom Set.univ markedAtom index)
    (retained : Set StepPath)
    (radialFamily : CompatibleRadialFamily
      (asymmetricSuccessful skeletonAtom) retained
      radialCertificate.radialTail)
    (onePointFamily : SequentialProfileUpperFamily
      ((i : ℕ) * chosenBlockLength delta n) (scaleIndex delta n)
      chosenProfileDelta historyGain x)
    (hretainedSubset : retained ⊆ stoppedSuccessfulPointEvent
      ((i : ℕ) * chosenBlockLength delta n)
      (scaleIndex delta n) chosenProfileDelta x)
    (hprofileTail : ProfileWeightUpper.profileUpperTailStart ≤
      scaleIndex delta n)
    (hhistoryGain : historyGain ≤ Real.exp prefixProfileCostDeficit)
    (hloss : Real.exp (1 / 4) ≤ harnackFactor) :
    ActualMarkedFarPairData delta n harnackFactor i x y := by
  let successful := asymmetricSuccessful skeletonAtom
  let skeletonWeight :=
    asymmetricSkeletonWeight Complement UnmarkedBridge unmarkedFactor
  have hdecomposition : MarkedStoppedDataUpperDecomposition fairSteps
      (stoppedThickPointEvent
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta
          (chosenThickDelta delta) x ∩
        stoppedThickPointEvent
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta
          (chosenThickDelta delta) y)
      successful skeletonWeight
      (pairTerminalSkeletonKernel delta n y)
      (pairTerminalMarkedKernel delta n y) Set.univ := by
    exact markedStoppedDataUpperDecomposition_of_asymmetric_kernelUpper
      _ skeletonAtom markedAtom (pairTerminalSkeletonKernel delta n y)
      (pairTerminalMarkedKernel delta n y) Set.univ
      Complement UnmarkedBridge MarkedBridge unmarkedFactor markedFactor
      hskeleton_event hmarked_event hcomplementWord hunmarkedKernel
      hmarkedKernel hskeleton_disjoint hmarked_disjoint hpair_union
  have hretainedUpper : fairSteps.real retained ≤ pairPointEnvelope delta n :=
    AppendixPairCrossingTailLiteral.successful_le_pairPointEnvelope_of_sequentialUpperFamily
      retained onePointFamily hretainedSubset hprofileTail hhistoryGain
  exact of_canonicalTerminal_profileAtomWeights terminalCertificate
    radialCertificate successful retained skeletonWeight
    (by simpa [pairTerminalSkeletonKernel,
        pairTerminalMarkedKernel, pairTerminalCount] using hdecomposition)
    (fun _ : radialFamily.RetainedCode ↦ Unit)
    radialFamily.retainedAtom radialFamily.tailAtom radialFamily.tailWeight
    radialFamily.successful_subset_doubleUnion radialFamily.retained_eq
    radialFamily.retainedAtom_measurable radialFamily.retainedAtom_pairwise
    radialFamily.tailAtom_mass radialFamily.tailWeight_tsum_le hloss
    hretainedUpper

end

end Erdos1165.AsymmetricActualFarPairKernelUpperConstructor
