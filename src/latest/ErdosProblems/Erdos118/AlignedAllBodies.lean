import ErdosProblems.Erdos118.AlignedBridgeDiagram
import ErdosProblems.Erdos118.AlignedSecondMarker
import ErdosProblems.Erdos118.PairedFirstSecond
import ErdosProblems.Erdos118.RightLastRefinement

/-! The second aligned marker bridge and all three last-body certificates.
The common terminal singleton test relates their actual parameters.
All six first leaves are submitted using their own conservative steps. -/

namespace Erdos118.AlignedAllBodies

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays AlignedLastOpening AlignedFirstBodies AlignedBridgeDiagram

abbrev TPair {H : Set ℕ} {B : SimpleGraph G} {O : Opening H B} {F : Pair O}
    (D : Diagram O F) :=
  PairedFirstSecond.Pair H B true false D.lowerBody D.upperBody
    (.leaf F.oldLeft) (.leaf D.right) D.lowerCertificate.size D.upperCertificate.size

theorem exists_t_pair {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    {O : Opening H B} {F : Pair O} (D : Diagram O F) (d : ℕ) :
    ∃ T : TPair D,
      (∀ x ∈ BodyResponses.newWord T.lowerSetup.position, x ∈ H ∧ d < x) ∧
      (∀ x ∈ BodyResponses.newWord T.upperSetup.position, x ∈ H ∧ d < x) :=
  PairedFirstSecond.exists_pair hH B true false D.lowerBody D.upperBody
    (.leaf F.oldLeft) (.leaf D.right) D.sameOrdinary
    D.lowerCertificate.size D.upperCertificate.size
    D.lowerCertificate.bound D.upperCertificate.bound (fun _ ↦ D.upperCertificate.positive)
    D.lowerCommand D.upperCommand D.lowerCertificate.certificate D.upperCertificate.certificate d

structure UCertificates {H : Set ℕ} {B : SimpleGraph G} {O : Opening H B} {F : Pair O}
    (D : Diagram O F) (T : TPair D) where
  lowerBody : BodyDecision
  upperBody : BodyDecision
  lowerLast : lowerBody.roots = []
  upperLast : upperBody.roots = []
  lowerExact : ExactSlots.Exact (.body lowerBody)
  upperExact : ExactSlots.Exact (.body upperBody)
  sameOrdinary : lowerBody.stem.ordinary = upperBody.stem.ordinary
  lowerStep : ConservativeRuns.Step H (GraphPayoff.payoff B .inside)
    (.leaf F.insertedLeft, .leaf O.insertedRight) (.leaf F.insertedLeft, .body lowerBody)
  upperRun : ConservativeRuns.Run H (GraphPayoff.payoff B .inside)
    (.leaf O.first.target, .leaf O.second.target) (.leaf T.upper, .body upperBody)
  lowerBlue : RamseyGame.Outcome H
    (GraphPayoff.game B .inside (.leaf F.insertedLeft, .body lowerBody)) true
  upperBlue : RamseyGame.Outcome H
    (GraphPayoff.game B .inside (.leaf T.upper, .body upperBody)) true
  lowerCommand : RightBlue H (GraphPayoff.payoff B .inside) (.leaf F.insertedLeft, .body lowerBody)
  upperCommand : RightBlue H (GraphPayoff.payoff B .inside) (.leaf T.upper, .body upperBody)
  lowerCertificate : RightBody H B F.insertedLeft lowerBody
  upperCertificate : RightBody H B T.upper upperBody
  lowerSize : O.insertedPositive.size = lowerCertificate.size + 1
  upperSize : D.upperCertificate.size = upperCertificate.size + 1
  lowerZero : D.lowerCertificate.size = 0 ↔ lowerCertificate.size = 0
  upperZero : D.lowerCertificate.size = 0 ↔ upperCertificate.size = 0

theorem exists_u_certificates {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      InsideCounts.beforeLast S = InsideCounts.beforeLast T)
    (singleton : Bool)
    (htest : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      ((LastBodyRefinement.lastLabel T).length = 1 ↔ singleton = true))
    {O : Opening H B} {F : Pair O} (D : Diagram O F) (T : TPair D) :
    Nonempty (UCertificates D T) := by
  obtain ⟨v, hv, hvf⟩ := D.rightSuffix
  have hroot : D.right.position.stem.root = O.insertedRight.position.stem.root := by
    have h := congrArg (fun xs : List ℕ ↦ xs.headD 0) hv
    simpa only [Position.ordinary, Stem.ordinary, List.cons_append, List.headD_cons] using h
  obtain ⟨A, E, hAL, hEL, hA, hE, hord, hsA, hsE, hbA, hbE, hcA, hcE⟩ :=
    AlignedSecondMarker.align hH B F.insertedLeft O.insertedRight T.upper D.right
      O.insertedNext O.insertedRightRoots O.insertedRightLeaves D.rightRoots D.rightLeaves
      O.insertedRightExact D.rightExact hroot D.insertedRequest v hv hvf T.upperHandoff
  obtain ⟨d, bD, hbD⟩ := body_setups B .inside true A (.leaf F.insertedLeft) hcA
  obtain ⟨g, bG, hbG⟩ := body_setups B .inside true E (.leaf T.upper) hcE
  let CD : RightBody H B F.insertedLeft A := ⟨d, bD, hbD⟩
  let CG : RightBody H B T.upper E := ⟨g, bG, hbG⟩
  have hsizeD := AlignedBodyCounts.right_certificate hH B hall F.insertedLeft A
    F.exactSlots.2 hA F.roots_nil.2 hAL d bD hbD
  change F.insertedSetup.position.label.length = d + 2 at hsizeD
  rw [F.insertedSetup.label_length] at hsizeD
  have hsizeG := AlignedBodyCounts.right_certificate hH B hall T.upper E
    (T.exactSlots D.lowerExact D.upperExact).2 hE D.upperLast hEL g bG hbG
  change T.upperSetup.position.label.length = g + 2 at hsizeG
  rw [T.upperSetup.label_length] at hsizeG
  have ht := RightLastRefinement.right_certificate hH B singleton htest F.oldLeft
    D.lowerBody D.lowerExact D.lowerLast D.lowerCertificate.size
    D.lowerCertificate.bound D.lowerCertificate.certificate
  have hd := RightLastRefinement.right_certificate hH B singleton htest F.insertedLeft
    A hA hAL d bD hbD
  have hg := RightLastRefinement.right_certificate hH B singleton htest T.upper E hE hEL g bG hbG
  exact ⟨{
    lowerBody := A, upperBody := E, lowerLast := hAL, upperLast := hEL
    lowerExact := hA, upperExact := hE, sameOrdinary := hord, lowerStep := hsA
    upperRun := Relation.ReflTransGen.tail (Relation.ReflTransGen.tail D.upperRun T.upperStep) hsE
    lowerBlue := hbA, upperBlue := hbE, lowerCommand := hcA, upperCommand := hcE
    lowerCertificate := CD, upperCertificate := CG
    lowerSize := by dsimp [CD]; omega
    upperSize := by dsimp [CG]; omega
    lowerZero := ht.trans hd.symm, upperZero := ht.trans hg.symm }⟩

abbrev UPair {H : Set ℕ} {B : SimpleGraph G} {O : Opening H B} {F : Pair O}
    {D : Diagram O F} {T : TPair D} (C : UCertificates D T) :=
  PairedFirstSecond.Pair H B true true C.lowerBody C.upperBody
    (.leaf F.insertedLeft) (.leaf T.upper) C.lowerCertificate.size C.upperCertificate.size

theorem exists_u_pair {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    {O : Opening H B} {F : Pair O} {D : Diagram O F} {T : TPair D}
    (C : UCertificates D T) (d : ℕ) :
    ∃ U : UPair C,
      (∀ x ∈ BodyResponses.newWord U.lowerSetup.position, x ∈ H ∧ d < x) ∧
      (∀ x ∈ BodyResponses.newWord U.upperSetup.position, x ∈ H ∧ d < x) := by
  have hcompat : 0 < C.lowerCertificate.size → 0 < C.upperCertificate.size := by
    intro hd
    have hzero := C.lowerZero.symm.trans C.upperZero
    have hne : C.upperCertificate.size ≠ 0 := fun he ↦ (Nat.ne_of_gt hd) (hzero.mpr he)
    exact Nat.pos_of_ne_zero hne
  exact PairedFirstSecond.exists_pair hH B true true C.lowerBody C.upperBody
    (.leaf F.insertedLeft) (.leaf T.upper) C.sameOrdinary
    C.lowerCertificate.size C.upperCertificate.size
    C.lowerCertificate.bound C.upperCertificate.bound hcompat
    C.lowerCommand C.upperCommand C.lowerCertificate.certificate C.upperCertificate.certificate d

end Erdos118.AlignedAllBodies
