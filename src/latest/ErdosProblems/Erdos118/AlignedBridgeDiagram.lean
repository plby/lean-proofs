import ErdosProblems.Erdos118.AlignedThirdRun
import ErdosProblems.Erdos118.AlignedMarkerBridge
import ErdosProblems.Erdos118.AlignedBodyCounts

/-! First shared last-body stem of the aligned bridge. Both waiting
source bounds were saved before the third-game run. The unused right
suffix remains above its saved bound for the next bridge stage. -/

namespace Erdos118.AlignedBridgeDiagram

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays AlignedLastOpening AlignedFirstBodies

structure RightBody (H : Set ℕ) (B : SimpleGraph G) (P : Pending) (D : BodyDecision) where
  size : ℕ
  bound : ℕ
  certificate : ∀ A : BodyResponses.Setup D.stem size,
    (∀ x ∈ BodyResponses.newWord A.position, x ∈ H) →
    (∀ x ∈ BodyResponses.newWord A.position, bound < x) →
    RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf (applyBody D A))) true

structure Diagram {H : Set ℕ} {B : SimpleGraph G} (O : Opening H B) (F : Pair O) where
  insertedRequest : RightRequest H B F.insertedLeft O.insertedRight
    O.insertedNext O.insertedRightRoots
  right : Pending
  rightRoots : right.roots = [O.insertedNext]
  rightLeaves : right.leaves = []
  rightExact : ExactSlots.Exact (.leaf right)
  rightSuffix : ∃ w : List ℕ,
    right.position.ordinary = O.insertedRight.position.ordinary ++ w ∧
      ∀ x ∈ w, x ∈ H ∧ insertedRequest.bound < x
  lowerBody : BodyDecision
  upperBody : BodyDecision
  lowerLast : lowerBody.roots = []
  upperLast : upperBody.roots = []
  lowerExact : ExactSlots.Exact (.body lowerBody)
  upperExact : ExactSlots.Exact (.body upperBody)
  sameOrdinary : lowerBody.stem.ordinary = upperBody.stem.ordinary
  lowerStep : ConservativeRuns.Step H (GraphPayoff.payoff B .inside)
    (.leaf F.oldLeft, .leaf O.oldRight) (.leaf F.oldLeft, .body lowerBody)
  upperRun : ConservativeRuns.Run H (GraphPayoff.payoff B .inside)
    (.leaf O.first.target, .leaf O.second.target) (.body upperBody, .leaf right)
  lowerBlue : RamseyGame.Outcome H
    (GraphPayoff.game B .inside (.leaf F.oldLeft, .body lowerBody)) true
  upperBlue : RamseyGame.Outcome H
    (GraphPayoff.game B .inside (.body upperBody, .leaf right)) true
  lowerCommand : RightBlue H (GraphPayoff.payoff B .inside) (.leaf F.oldLeft, .body lowerBody)
  upperCommand : LeftBlue H (GraphPayoff.payoff B .inside) (.body upperBody, .leaf right)
  lowerCertificate : RightBody H B F.oldLeft lowerBody
  upperCertificate : InsertedAlignment.PositiveBody H B upperBody right
  lowerSize : O.oldPositive.size = lowerCertificate.size + 1

theorem exists_diagram {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      InsideCounts.beforeLast S = InsideCounts.beforeLast T)
    (hlast : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (LastBodyRefinement.lastLabel S).length ≠ 1)
    (O : Opening H B) (F : Pair O) : Nonempty (Diagram O F) := by
  obtain ⟨⟨RT⟩, ⟨RU⟩⟩ := F.requests
  let M := max RT.bound RU.bound
  obtain ⟨T, U, hTR, hTL, hUR, hUL, hT, hU, hrun, _, hh, v, w, hv, hw, hvf, hwf⟩ :=
    AlignedThirdRun.checkpoint hH B hall O M
  have hTroot : T.position.stem.root = O.oldRight.position.stem.root := by
    have h := congrArg (fun xs : List ℕ ↦ xs.headD 0) hv
    simpa only [Position.ordinary, Stem.ordinary, List.cons_append, List.headD_cons] using h
  obtain ⟨D, E, hDlast, hElast, hD, hE, hord, hsD, hsE, hbD, hbE, hcD, hcE⟩ :=
    AlignedMarkerBridge.align hH B F.oldLeft O.oldRight T U O.oldNext O.oldRightRoots
      O.oldRightLeaves hTR hTL O.oldRightExact hT hTroot RT v hv
      (fun x hx ↦ ⟨(hvf x hx).1, (le_max_left _ _).trans_lt (hvf x hx).2⟩) hh
  obtain ⟨t, bT, hbT⟩ := body_setups B .inside true D (.leaf F.oldLeft) hcD
  let CT : RightBody H B F.oldLeft D := ⟨t, bT, hbT⟩
  obtain ⟨CE⟩ := InsertedAlignment.positive_body hH B hlast E U hE hElast hcE
  have hsize := AlignedBodyCounts.right_certificate hH B hall F.oldLeft D
    F.exactSlots.1 hD F.roots_nil.1 hDlast t bT hbT
  change F.oldSetup.position.label.length = t + 2 at hsize
  rw [F.oldSetup.label_length] at hsize
  exact ⟨{
    insertedRequest := RU, right := U, rightRoots := hUR, rightLeaves := hUL, rightExact := hU
    rightSuffix := ⟨w, hw,
      fun x hx ↦ ⟨(hwf x hx).1, (le_max_right _ _).trans_lt (hwf x hx).2⟩⟩
    lowerBody := D, upperBody := E, lowerLast := hDlast, upperLast := hElast
    lowerExact := hD, upperExact := hE, sameOrdinary := hord
    lowerStep := hsD, upperRun := Relation.ReflTransGen.tail hrun hsE
    lowerBlue := hbD, upperBlue := hbE, lowerCommand := hcD, upperCommand := hcE
    lowerCertificate := CT, upperCertificate := CE, lowerSize := by dsimp [CT]; omega }⟩

end Erdos118.AlignedBridgeDiagram
