import ErdosProblems.Erdos118.AlignedInsertion
import ErdosProblems.Erdos118.InsertedAlignment

/-! Three actual blue games at the aligned last-body opening. The source
left stems have equal ordinary words; both right words remain critical,
and their root/body replays retain their own exact decorations. -/

namespace Erdos118.AlignedLastOpening

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays InsertedAlignment

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
  oldNext : ℕ
  insertedNext : ℕ
  oldRightRoots : oldRight.roots = [oldNext]
  oldRightLeaves : oldRight.leaves = []
  insertedRightRoots : insertedRight.roots = [insertedNext]
  insertedRightLeaves : insertedRight.leaves = []
  oldRightExact : ExactSlots.Exact (.leaf oldRight)
  insertedRightExact : ExactSlots.Exact (.leaf insertedRight)
  first : AlignedRootPreparation.Replay initial oldRight
  source : AlignedRightPreparation.RootCertificate H B first.target
  sourcePositive : 0 < source.size
  second : AlignedRightPreparation.Replay source insertedRight
  firstExact : ExactSlots.Exact (.leaf first.target)
  secondExact : ExactSlots.Exact (.leaf second.target)
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
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      InsideCounts.beforeLast S = InsideCounts.beforeLast T)
    (hlast : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (LastBodyRefinement.lastLabel S).length ≠ 1) : Nonempty (Opening H B) := by
  obtain ⟨I, hk, P, T, c, e, ⟨Z⟩, hPR, hPL, hTR, hTL, hP, hT, _, hcP, hfP, ⟨T₁⟩⟩ :=
    AlignedOpening.initial_critical_replay hH B hB hinit hfirst hall
  obtain ⟨b, hb⟩ := certificate B P T c hPR hPL hcP
  have hTlen : 1 < T₁.target.position.stem.rootLabel.length := by
    change 1 < T₁.body.position.stem.rootLabel.length
    rw [T₁.body.stem_eq, T₁.rootSetup.label_length]
    omega
  obtain ⟨J, hJ, R, U, f, hRR, hRL, hUR, hUL, hR, hU, hr, _, ⟨v, hv, hvf⟩, _, hcR, ⟨U₁⟩⟩ :=
    AlignedInsertion.inserted_checkpoint hH B hB hinit hall I hk P T₁.target c hPR hP Z hfP
      hTlen T₁.handoff b
  obtain ⟨D, E, hDlast, hElast, hD, hE, hord, _, _, hbD, hbE, hcD, hcE⟩ :=
    align hH B P R T U c hPR hPL hRR hRL hP hR hr b hb v hv hvf hcR
  obtain ⟨positiveD⟩ := positive_body hH B hlast D T hD hDlast hcD
  obtain ⟨positiveE⟩ := positive_body hH B hlast E U hE hElast hcE
  have hT₁ : ExactSlots.Exact (.leaf T₁.target) :=
    ExactSlots.step_exact (DecisionStates.Step.body (ofRoot T₁.rootSetup) T₁.body)
      (ExactSlots.step_exact (DecisionStates.Step.root T₁.rootSetup) trivial)
  have hU₁ : ExactSlots.Exact (.leaf U₁.target) :=
    ExactSlots.step_exact (DecisionStates.Step.body (ofRoot U₁.rootSetup) U₁.body)
      (ExactSlots.step_exact (DecisionStates.Step.root U₁.rootSetup) trivial)
  exact ⟨{
    initial := I, initialPositive := hk
    oldBody := D, insertedBody := E, oldRight := T, insertedRight := U
    oldLast := hDlast, insertedLast := hElast, oldExact := hD, insertedExact := hE
    sameOrdinary := hord, oldNext := e, insertedNext := f
    oldRightRoots := hTR, oldRightLeaves := hTL
    insertedRightRoots := hUR, insertedRightLeaves := hUL
    oldRightExact := hT, insertedRightExact := hU
    first := T₁, source := J, sourcePositive := hJ, second := U₁
    firstExact := hT₁, secondExact := hU₁
    oldBlue := hbD, insertedBlue := hbE, oldCommand := hcD, insertedCommand := hcE
    oldPositive := positiveD, insertedPositive := positiveE }⟩

end Erdos118.AlignedLastOpening
