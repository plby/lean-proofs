import ErdosProblems.Erdos118.AlignedLastOpening
import ErdosProblems.Erdos118.SharedFirstLast

/-! Submit both source-left first leaves with common first and last
indices; retain actual blue handoffs and both right next-body requests. -/

namespace Erdos118.AlignedFirstBodies

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays AlignedLastOpening

structure Pair {H : Set ℕ} {B : SimpleGraph G} (O : Opening H B) where
  oldSetup : BodyResponses.Setup O.oldBody.stem O.oldPositive.size
  insertedSetup : BodyResponses.Setup O.insertedBody.stem O.insertedPositive.size
  sameOrdinary : oldSetup.position.ordinary = insertedSetup.position.ordinary
  sameMarker : oldSetup.position.size = insertedSetup.position.size
  sameEntries : oldSetup.position.entries = insertedSetup.position.entries
  sameFirst : oldSetup.position.label.headD 0 = insertedSetup.position.label.headD 0
  sameLast : oldSetup.position.label.getLastD 0 = insertedSetup.position.label.getLastD 0
  separated : ∀ x ∈ oldSetup.position.label, x < oldSetup.position.label.getLastD 0 →
    x < insertedSetup.position.label.tail.headD 0
  oldStep : ConservativeRuns.Step H (GraphPayoff.payoff B .inside)
    (.body O.oldBody, .leaf O.oldRight) (.leaf (applyBody O.oldBody oldSetup), .leaf O.oldRight)
  insertedStep : ConservativeRuns.Step H (GraphPayoff.payoff B .inside)
    (.body O.insertedBody, .leaf O.insertedRight)
      (.leaf (applyBody O.insertedBody insertedSetup), .leaf O.insertedRight)
  oldBlue : RamseyGame.Outcome H (GraphPayoff.game B .inside
    (.leaf (applyBody O.oldBody oldSetup), .leaf O.oldRight)) true
  insertedBlue : RamseyGame.Outcome H (GraphPayoff.game B .inside
    (.leaf (applyBody O.insertedBody insertedSetup), .leaf O.insertedRight)) true
  oldHandoff : RightBlue H (GraphPayoff.payoff B .inside)
    (.leaf (applyBody O.oldBody oldSetup), .leaf O.oldRight)
  insertedHandoff : RightBlue H (GraphPayoff.payoff B .inside)
    (.leaf (applyBody O.insertedBody insertedSetup), .leaf O.insertedRight)

def Pair.oldLeft {H : Set ℕ} {B : SimpleGraph G} {O : Opening H B} (F : Pair O) : Pending :=
  applyBody O.oldBody F.oldSetup

def Pair.insertedLeft {H : Set ℕ} {B : SimpleGraph G} {O : Opening H B} (F : Pair O) : Pending :=
  applyBody O.insertedBody F.insertedSetup

theorem Pair.exactSlots {H : Set ℕ} {B : SimpleGraph G} {O : Opening H B} (F : Pair O) :
    ExactSlots.Exact (.leaf F.oldLeft) ∧ ExactSlots.Exact (.leaf F.insertedLeft) :=
  ⟨ExactSlots.step_exact (DecisionStates.Step.body O.oldBody F.oldSetup) O.oldExact,
    ExactSlots.step_exact (DecisionStates.Step.body O.insertedBody F.insertedSetup) O.insertedExact⟩

theorem Pair.roots_nil {H : Set ℕ} {B : SimpleGraph G} {O : Opening H B} (F : Pair O) :
    F.oldLeft.roots = [] ∧ F.insertedLeft.roots = [] := ⟨O.oldLast, O.insertedLast⟩

theorem Pair.leaves_nonempty {H : Set ℕ} {B : SimpleGraph G} {O : Opening H B} (F : Pair O) :
    F.oldLeft.leaves ≠ [] ∧ F.insertedLeft.leaves ≠ [] := by
  have hn : ∀ (D : BodyDecision) (k : ℕ) (A : BodyResponses.Setup D.stem k),
      0 < k → (applyBody D A).leaves ≠ [] := by
    intro D k A hk he
    have h := congrArg List.length he
    change A.position.label.tail.length = 0 at h
    rw [List.length_tail, A.label_length] at h
    omega
  exact ⟨hn O.oldBody _ F.oldSetup O.oldPositive.positive,
    hn O.insertedBody _ F.insertedSetup O.insertedPositive.positive⟩

theorem exists_pair {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G) (O : Opening H B) (d : ℕ) :
    ∃ F : Pair O,
      (∀ x ∈ BodyResponses.newWord F.oldSetup.position, x ∈ H ∧ d < x) ∧
      (∀ x ∈ BodyResponses.newWord F.insertedSetup.position, x ∈ H ∧ d < x) := by
  let c₁ := pairBound (.body O.oldBody, .leaf O.oldRight)
  let c₂ := pairBound (.body O.insertedBody, .leaf O.insertedRight)
  let g₁ := guard H B .inside false O.oldBody (.leaf O.oldRight) O.oldPositive.size
  let g₂ := guard H B .inside false O.insertedBody (.leaf O.insertedRight) O.insertedPositive.size
  let M := max O.oldPositive.bound (max O.insertedPositive.bound
    (max c₁ (max c₂ (max g₁ (max g₂ d)))))
  have hb₁M : O.oldPositive.bound ≤ M := by dsimp [M]; omega
  have hb₂M : O.insertedPositive.bound ≤ M := by dsimp [M]; omega
  have hc₁M : c₁ ≤ M := by dsimp [M]; omega
  have hc₂M : c₂ ≤ M := by dsimp [M]; omega
  have hg₁M : g₁ ≤ M := by dsimp [M]; omega
  have hg₂M : g₂ ≤ M := by dsimp [M]; omega
  have hdM : d ≤ M := by dsimp [M]; omega
  obtain ⟨A, E, hord, hmarker, hentries, hfirst, hlast, hsep, hA, hE⟩ :=
    SharedFirstLast.body_pair_separated hH O.oldBody.stem O.insertedBody.stem
      O.oldBody.room O.insertedBody.room O.sameOrdinary M O.oldPositive.size
      O.insertedPositive.size O.oldPositive.positive O.insertedPositive.positive
  have hAc : ∀ x ∈ BodyResponses.newWord A.position, c₁ < x :=
    fun x hx ↦ hc₁M.trans_lt (hA x hx).2
  have hEc : ∀ x ∈ BodyResponses.newWord E.position, c₂ < x :=
    fun x hx ↦ hc₂M.trans_lt (hE x hx).2
  have hbA := O.oldPositive.certificate A (fun x hx ↦ (hA x hx).1)
    (fun x hx ↦ hb₁M.trans_lt (hA x hx).2)
  have hbE := O.insertedPositive.certificate E (fun x hx ↦ (hE x hx).1)
    (fun x hx ↦ hb₂M.trans_lt (hE x hx).2)
  let F : Pair O :=
    { oldSetup := A, insertedSetup := E, sameOrdinary := hord, sameMarker := hmarker
      sameEntries := hentries, sameFirst := hfirst, sameLast := hlast, separated := hsep
      oldStep := body_step B .inside false O.oldBody (.leaf O.oldRight) A
        (command_allowed B .inside false O.oldBody (.leaf O.oldRight) O.oldCommand)
        (fun x hx ↦ (hA x hx).1) hAc (fun x hx ↦ hg₁M.trans_lt (hA x hx).2)
      insertedStep := body_step B .inside false O.insertedBody (.leaf O.insertedRight) E
        (command_allowed B .inside false O.insertedBody (.leaf O.insertedRight) O.insertedCommand)
        (fun x hx ↦ (hE x hx).1) hEc (fun x hx ↦ hg₂M.trans_lt (hE x hx).2)
      oldBlue := hbA, insertedBlue := hbE
      oldHandoff := body_handoff hH B .inside false O.oldBody (.leaf O.oldRight) A hAc hbA
      insertedHandoff := body_handoff hH B .inside false O.insertedBody
        (.leaf O.insertedRight) E hEc hbE }
  exact ⟨F, fun x hx ↦ ⟨(hA x hx).1, hdM.trans_lt (hA x hx).2⟩,
    fun x hx ↦ ⟨(hE x hx).1, hdM.trans_lt (hE x hx).2⟩⟩

structure RightRequest (H : Set ℕ) (B : SimpleGraph G) (S P : Pending)
    (c : ℕ) (hR : P.roots = [c]) where
  bound : ℕ
  certificate : ∀ Q : Stem, ∀ v : List ℕ,
    Q.root = P.position.stem.root → Q.done.length = c - 1 →
    Q.ordinary = P.position.ordinary ++ v →
    (∀ x ∈ v, x ∈ H) → (∀ x ∈ v, bound < x) →
    ∃ A : StemResponses.Setup P.position (c - 1), A.newWord = v ∧
      A.stem.ordinary = Q.ordinary ∧
      ConservativeRuns.Step H (GraphPayoff.payoff B .inside)
        (.leaf S, .leaf P) (.leaf S, .body (ofStem P c [] hR A)) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside
        (.leaf S, .body (ofStem P c [] hR A))) true

theorem Pair.requests {H : Set ℕ} {B : SimpleGraph G} {O : Opening H B} (F : Pair O) :
    Nonempty (RightRequest H B F.oldLeft O.oldRight O.oldNext O.oldRightRoots) ∧
      Nonempty (RightRequest H B F.insertedLeft O.insertedRight
        O.insertedNext O.insertedRightRoots) := by
  obtain ⟨bT, hbT⟩ := StemReplay.right_body_words_step (GraphPayoff.payoff B .inside)
    (.leaf F.oldLeft) O.oldRight O.oldNext [] O.oldRightRoots O.oldRightLeaves F.oldHandoff
  obtain ⟨bU, hbU⟩ := StemReplay.right_body_words_step (GraphPayoff.payoff B .inside)
    (.leaf F.insertedLeft) O.insertedRight O.insertedNext [] O.insertedRightRoots
      O.insertedRightLeaves F.insertedHandoff
  exact ⟨⟨⟨bT, hbT⟩⟩, ⟨⟨bU, hbU⟩⟩⟩

end Erdos118.AlignedFirstBodies
