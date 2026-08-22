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

import ErdosProblems.Erdos1165.AsymmetricActualFarPairData
import ErdosProblems.Erdos1165.AsymmetricPairPartitionUpper
import ErdosProblems.Erdos1165.AsymmetricCompatibleRadialFamily

/-!
# Literal asymmetric far-pair constructor

This is the assembly point for HLOZ (A.16)--(A.17).  It retains the complete
first-point stopped history, inserts only the second-point continuation, and
sums a literal family of post-separation radial words before applying the
profile-tail envelope.  The marked stopped-data decomposition is constructed
from prefix-free complementary words; it is not accepted as a premise.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AsymmetricActualFarPairConstructor

open AppendixPair AppendixPairMoment AppendixPairTerminalCertificate
open AsymmetricActualFarPairData AsymmetricPairPartitionUpper
open AsymmetricCompatibleRadialFamily
open AnnularProfileSequentialUpper
open MarkedBoundaryVisitKernel MarkedBridgeFactorization
open MarkedSkeletonPartition MarkedTerminalDisintegration
open Proposition13Assembly Proposition13LiteralAssembly Proposition13Scales
open TerminalExcursionPathwise TerminalMarkedParameterBounds
open TerminalMarkedSkeletonDecomposition TerminalParameterBounds
open TerminalSkeletonWords

noncomputable section

/-- Number of terminal coordinates erased at the second point. -/
abbrev pairTerminalCount (delta : ℝ) (n : ℕ) : ℕ :=
  AppendixLocalTime.requiredTerminalCount
    (scaleIndex delta n) chosenProfileDelta

/-- Canonical terminal unmarked kernel for the second point. -/
abbrev pairTerminalSkeletonKernel
    (delta : ℝ) (n : ℕ) (y : Point) :
    Fin (pairTerminalCount delta n) →
      TerminalEntrance (scaleIndex delta n) y →
      TerminalExit (scaleIndex delta n) y → ℝ≥0∞ :=
  fun _ u z ↦ terminalSkeletonKernel
    (terminalOuterBoundary (scaleIndex delta n) y) u.1 z.1

/-- Canonical terminal marked visit/exit kernel for the second point. -/
abbrev pairTerminalMarkedKernel
    (delta : ℝ) (n : ℕ) (y : Point) :
    Fin (pairTerminalCount delta n) →
      TerminalEntrance (scaleIndex delta n) y → ℕ →
      TerminalExit (scaleIndex delta n) y → ℝ≥0∞ :=
  fun _ u k z ↦ terminalMarkedKernel
    (terminalOuterBoundary (scaleIndex delta n) y) y u.1 k z.1

/-- Construct the exact `ActualMarkedFarPairData` record from literal
asymmetric insertion atoms and a two-stage radial-word mixture.

The only estimates in the signature are one-dimensional ingredients:
individual radial-word atom factorization, a row-wise conditional-weight
sum, the A.11 one-point family, and the explicit finite profile-mixture
certificate. -/
def of_literalAsymmetricAtoms
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
      (markedFactor data entrance exit visits).kernel j =
        pairTerminalMarkedKernel delta n y j
          (entrance j) (visits j) (exit j))
    (hskeleton_disjoint : Pairwise fun i j : SkeletonIndex Data
        (TerminalEntrance (scaleIndex delta n) y)
        (TerminalExit (scaleIndex delta n) y)
        (pairTerminalCount delta n) ↦
      Disjoint (indexedSkeletonAtom skeletonAtom i)
        (indexedSkeletonAtom skeletonAtom j))
    (hmarked_disjoint : Pairwise fun i j : MarkedIndex Data
        (TerminalEntrance (scaleIndex delta n) y)
        (TerminalExit (scaleIndex delta n) y)
        (pairTerminalCount delta n) ↦
      Disjoint (indexedMarkedAtom markedAtom i)
        (indexedMarkedAtom markedAtom j))
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
        restrictedMarkedAtom
          Set.univ markedAtom index)
    (retained : Set StepPath)
    {RetainedCode : Type*} [Countable RetainedCode]
    (TailCode : RetainedCode → Type*)
    [∀ r, Countable (TailCode r)]
    (retainedAtom : RetainedCode → Set StepPath)
    (tailAtom : ∀ r, TailCode r → Set StepPath)
    (tailWeight : ∀ r, TailCode r → ℝ≥0∞)
    (hsuccessful : asymmetricSuccessful skeletonAtom ⊆
      ⋃ r, ⋃ t, tailAtom r t)
    (hretained : retained = ⋃ r, retainedAtom r)
    (hretainedMeasurable : ∀ r, MeasurableSet (retainedAtom r))
    (hretainedDisjoint : Pairwise fun r s ↦
      Disjoint (retainedAtom r) (retainedAtom s))
    (hatomMass : ∀ r t,
      fairSteps (tailAtom r t) =
        tailWeight r t * fairSteps (retainedAtom r))
    (htailWeight : ∀ r, ∑' t, tailWeight r t ≤
      ENNReal.ofReal radialCertificate.radialTail)
    (onePointFamily : SequentialProfileUpperFamily
      ((i : ℕ) * chosenBlockLength delta n) (scaleIndex delta n)
      chosenProfileDelta historyGain x)
    (hretainedSubset : retained ⊆ stoppedSuccessfulPointEvent
      ((i : ℕ) * chosenBlockLength delta n)
      (scaleIndex delta n) chosenProfileDelta x)
    (hprofileTail : ProfileWeightUpper.profileUpperTailStart ≤
      scaleIndex delta n)
    (hhistoryGain : historyGain ≤
      Real.exp AppendixPairCrossingTail.prefixProfileCostDeficit)
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
      (pairTerminalMarkedKernel delta n y)
      Set.univ := by
    exact markedStoppedDataUpperDecomposition_of_asymmetric_factorization
      _ skeletonAtom markedAtom (pairTerminalSkeletonKernel delta n y)
      (pairTerminalMarkedKernel delta n y)
      Set.univ
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
    TailCode retainedAtom tailAtom tailWeight hsuccessful hretained
    hretainedMeasurable hretainedDisjoint hatomMass htailWeight hloss
    hretainedUpper

/-- Split-level specialization of `of_literalAsymmetricAtoms`.  The
dependent compatible radial family constructs the retained cylinders,
post-separation tail atoms, exact atom masses, and the two-stage successful
comparison internally. -/
def of_literalAsymmetricCompatibleRows
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
      (markedFactor data entrance exit visits).kernel j =
        pairTerminalMarkedKernel delta n y j
          (entrance j) (visits j) (exit j))
    (hskeleton_disjoint : Pairwise fun i j : SkeletonIndex Data
        (TerminalEntrance (scaleIndex delta n) y)
        (TerminalExit (scaleIndex delta n) y)
        (pairTerminalCount delta n) ↦
      Disjoint (indexedSkeletonAtom skeletonAtom i)
        (indexedSkeletonAtom skeletonAtom j))
    (hmarked_disjoint : Pairwise fun i j : MarkedIndex Data
        (TerminalEntrance (scaleIndex delta n) y)
        (TerminalExit (scaleIndex delta n) y)
        (pairTerminalCount delta n) ↦
      Disjoint (indexedMarkedAtom markedAtom i)
        (indexedMarkedAtom markedAtom j))
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
    (hhistoryGain : historyGain ≤
      Real.exp AppendixPairCrossingTail.prefixProfileCostDeficit)
    (hloss : Real.exp (1 / 4) ≤ harnackFactor) :
    ActualMarkedFarPairData delta n harnackFactor i x y :=
  of_literalAsymmetricAtoms terminalCertificate radialCertificate
    skeletonAtom markedAtom Complement UnmarkedBridge MarkedBridge
    unmarkedFactor markedFactor hskeleton_event hmarked_event hcomplementWord
    hunmarkedKernel hmarkedKernel hskeleton_disjoint hmarked_disjoint
    hpair_union retained (fun _ : radialFamily.RetainedCode ↦ Unit)
    radialFamily.retainedAtom radialFamily.tailAtom radialFamily.tailWeight
    radialFamily.successful_subset_doubleUnion radialFamily.retained_eq
    radialFamily.retainedAtom_measurable radialFamily.retainedAtom_pairwise
    radialFamily.tailAtom_mass radialFamily.tailWeight_tsum_le
    onePointFamily hretainedSubset hprofileTail hhistoryGain hloss

end

end Erdos1165.AsymmetricActualFarPairConstructor
