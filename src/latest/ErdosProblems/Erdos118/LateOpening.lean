import ErdosProblems.Erdos118.InsertedAlignment

/-!
Three actual blue games at the common last-body opening, constructed from
the initial inside hypothesis. Both opposite words retain their managed
data; subsequent simultaneous body and leaf responses are still required.
-/

namespace Erdos118.LateOpening

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays ReplaySources InsertedAlignment

structure Opening (H : Set ℕ) (B : SimpleGraph G) where
  initial : ManagedRelays.Initial H B .inside
  initialPositive : 0 < initial.size
  oldBody : BodyDecision
  insertedBody : BodyDecision
  oldRight : Pending
  insertedRight : Pending
  oldLast : oldBody.roots = []
  insertedLast : insertedBody.roots = []
  oldExact : ExactSlots.Exact (.body oldBody)
  insertedExact : ExactSlots.Exact (.body insertedBody)
  sameOrdinary : oldBody.stem.ordinary = insertedBody.stem.ordinary
  oldRightLast : oldRight.roots = []
  oldRightNonlast : oldRight.leaves ≠ []
  insertedRightLast : insertedRight.roots = []
  insertedRightNonlast : insertedRight.leaves ≠ []
  oldManaged : DeferredManaged.Managed initial (.leaf oldRight)
  first : ManagedCritical.InitialReplay initial oldRight
  source : Source H B .inside true first.target
  sourceExact : source.Exact
  insertedManaged : DeferredSource.Managed source (.leaf insertedRight)
  second : DeferredSource.Replay source insertedRight
  oldBlue : RamseyGame.Outcome H
    (GraphPayoff.game B .inside (.body oldBody, .leaf oldRight)) true
  insertedBlue : RamseyGame.Outcome H
    (GraphPayoff.game B .inside (.body insertedBody, .leaf insertedRight)) true
  oldCommand : LeftBlue H (GraphPayoff.payoff B .inside) (.body oldBody, .leaf oldRight)
  insertedCommand : LeftBlue H (GraphPayoff.payoff B .inside)
    (.body insertedBody, .leaf insertedRight)
  oldPositive : PositiveBody H B oldBody oldRight
  insertedPositive : PositiveBody H B insertedBody insertedRight

theorem exists_opening {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true)
    (hfirst : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (FirstBodyRefinement.firstLabel S).length ≠ 1)
    (hlate : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      LastMarkerRefinement.lastMarker T < LastMarkerRefinement.lastMarker S)
    (hlast : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (LastBodyRefinement.lastLabel S).length ≠ 1) : Nonempty (Opening H B) := by
  obtain ⟨I, hk, P, T, c, ⟨Z⟩, hPR, hPL, hTR, hTL, hP, _, _, hcP, hfP, ⟨MT⟩, ⟨T₁⟩⟩ :=
    ManagedOpening.initial_critical_replay hH B hB hinit hfirst hlate hlast
  obtain ⟨b, hb⟩ := certificate B P T c hPR hPL hcP
  obtain ⟨J, hJ, R, U, hRR, hRL, hUR, hUL, hR, _, hr, _, ⟨v, hv, hvf⟩, _, hcR, ⟨MU⟩, ⟨U₁⟩⟩ :=
    RootInsertion.inserted_checkpoint hH B hB hinit I hk P T₁.target c hPR hP Z hfP
      T₁.handoff hlate hlast b
  obtain ⟨D, E, hDlast, hElast, hD, hE, hord, _, _, hbD, hbE, hcD, hcE⟩ :=
    align hH B P R T U c hPR hPL hRR hRL hP hR hr b hb v hv hvf hcR
  obtain ⟨positiveD⟩ := positive_body hH B hlast D T hD hDlast hcD
  obtain ⟨positiveE⟩ := positive_body hH B hlast E U hE hElast hcE
  exact ⟨{
    initial := I, initialPositive := hk
    oldBody := D, insertedBody := E, oldRight := T, insertedRight := U
    oldLast := hDlast, insertedLast := hElast, oldExact := hD, insertedExact := hE
    sameOrdinary := hord, oldRightLast := hTR, oldRightNonlast := hTL
    insertedRightLast := hUR, insertedRightNonlast := hUL
    oldManaged := MT, first := T₁, source := J, sourceExact := hJ
    insertedManaged := MU, second := U₁
    oldBlue := hbD, insertedBlue := hbE, oldCommand := hcD, insertedCommand := hcE
    oldPositive := positiveD, insertedPositive := positiveE }⟩

end Erdos118.LateOpening
