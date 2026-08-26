import ErdosProblems.Erdos118.StrictSharedBodyRequests
import ErdosProblems.Erdos118.SharedFirstLast

/-! First leaves of both source last bodies: one ordinary word,
independent positive label sizes, and separate actual graph certificates. -/

namespace Erdos118.StrictSharedFirstLeaves

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays

structure Pair {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {value : Bool} {J : StrictTwoRootRequests.Requests O value}
    {W : StrictSecondOpening.Opening J} (Q : StrictSharedBodyRequests.Requests W) where
  oldSetup : BodyResponses.Setup Q.aligned.old.stem Q.old.size
  insertedSetup : BodyResponses.Setup Q.aligned.inserted.stem Q.inserted.size
  ordinary : oldSetup.position.ordinary = insertedSetup.position.ordinary
  marker : oldSetup.position.size = insertedSetup.position.size
  entries : oldSetup.position.entries = insertedSetup.position.entries
  first : oldSetup.position.label.headD 0 = insertedSetup.position.label.headD 0
  last : oldSetup.position.label.getLastD 0 = insertedSetup.position.label.getLastD 0
  separated : ∀ x ∈ oldSetup.position.label, x < oldSetup.position.label.getLastD 0 →
    x < insertedSetup.position.label.tail.headD 0
  oldStep : ConservativeRuns.Step O.prepared.alphabet (GraphPayoff.payoff O.prepared.graph .inside)
    (.body Q.aligned.old, .leaf O.opening.checkpoint.right)
    (.leaf (applyBody Q.aligned.old oldSetup), .leaf O.opening.checkpoint.right)
  insertedStep : ConservativeRuns.Step W.prepared.alphabet
    (GraphPayoff.payoff W.prepared.graph .inside)
    (.body Q.aligned.inserted, .leaf W.opening.checkpoint.right)
    (.leaf (applyBody Q.aligned.inserted insertedSetup), .leaf W.opening.checkpoint.right)
  oldBlue : RamseyGame.Outcome O.prepared.alphabet (GraphPayoff.game O.prepared.graph .inside
    (.leaf (applyBody Q.aligned.old oldSetup), .leaf O.opening.checkpoint.right)) true
  insertedBlue : RamseyGame.Outcome W.prepared.alphabet (GraphPayoff.game W.prepared.graph .inside
    (.leaf (applyBody Q.aligned.inserted insertedSetup), .leaf W.opening.checkpoint.right)) true
  oldHandoff : RightBlue O.prepared.alphabet (GraphPayoff.payoff O.prepared.graph .inside)
    (.leaf (applyBody Q.aligned.old oldSetup), .leaf O.opening.checkpoint.right)
  insertedHandoff : RightBlue W.prepared.alphabet (GraphPayoff.payoff W.prepared.graph .inside)
    (.leaf (applyBody Q.aligned.inserted insertedSetup), .leaf W.opening.checkpoint.right)

def Pair.oldLeft {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {value : Bool} {J : StrictTwoRootRequests.Requests O value}
    {W : StrictSecondOpening.Opening J} {Q : StrictSharedBodyRequests.Requests W}
    (F : Pair Q) : Pending := applyBody Q.aligned.old F.oldSetup

def Pair.insertedLeft {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {value : Bool} {J : StrictTwoRootRequests.Requests O value}
    {W : StrictSecondOpening.Opening J} {Q : StrictSharedBodyRequests.Requests W}
    (F : Pair Q) : Pending := applyBody Q.aligned.inserted F.insertedSetup

theorem Pair.exactSlots {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {value : Bool} {J : StrictTwoRootRequests.Requests O value}
    {W : StrictSecondOpening.Opening J} {Q : StrictSharedBodyRequests.Requests W} (F : Pair Q) :
    ExactSlots.Exact (.leaf F.oldLeft) ∧ ExactSlots.Exact (.leaf F.insertedLeft) :=
  ⟨ExactSlots.step_exact (DecisionStates.Step.body Q.aligned.old F.oldSetup) Q.aligned.oldExact,
    ExactSlots.step_exact (DecisionStates.Step.body Q.aligned.inserted F.insertedSetup)
      Q.aligned.insertedExact⟩

theorem Pair.roots_nil {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {value : Bool} {J : StrictTwoRootRequests.Requests O value}
    {W : StrictSecondOpening.Opening J} {Q : StrictSharedBodyRequests.Requests W} (F : Pair Q) :
    F.oldLeft.roots = [] ∧ F.insertedLeft.roots = [] :=
  ⟨Q.aligned.oldRoots, Q.aligned.insertedRoots⟩

theorem Pair.leaves_nonempty {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {value : Bool} {J : StrictTwoRootRequests.Requests O value}
    {W : StrictSecondOpening.Opening J} {Q : StrictSharedBodyRequests.Requests W} (F : Pair Q) :
    F.oldLeft.leaves ≠ [] ∧ F.insertedLeft.leaves ≠ [] := by
  have hn : ∀ (D : BodyDecision) (k : ℕ) (A : BodyResponses.Setup D.stem k),
      0 < k → (applyBody D A).leaves ≠ [] := by
    intro D k A hk he
    have h := congrArg List.length he
    change A.position.label.tail.length = 0 at h
    rw [List.length_tail, A.label_length] at h
    omega
  exact ⟨hn Q.aligned.old _ F.oldSetup Q.old.positive,
    hn Q.aligned.inserted _ F.insertedSetup Q.inserted.positive⟩

theorem exists_pair {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {value : Bool} {J : StrictTwoRootRequests.Requests O value}
    {W : StrictSecondOpening.Opening J} (Q : StrictSharedBodyRequests.Requests W) (d : ℕ) :
    ∃ F : Pair Q,
      (∀ x ∈ BodyResponses.newWord F.oldSetup.position, x ∈ W.prepared.alphabet ∧ d < x) ∧
      (∀ x ∈ BodyResponses.newWord F.insertedSetup.position, x ∈ W.prepared.alphabet ∧ d < x) := by
  have hKH : W.prepared.alphabet ⊆ O.prepared.alphabet :=
    W.prepared.subset.trans (J.inserted.subset.trans J.subset)
  let c₁ := pairBound (.body Q.aligned.old, .leaf O.opening.checkpoint.right)
  let c₂ := pairBound (.body Q.aligned.inserted, .leaf W.opening.checkpoint.right)
  let g₁ := guard O.prepared.alphabet O.prepared.graph .inside false
    Q.aligned.old (.leaf O.opening.checkpoint.right) Q.old.size
  let g₂ := guard W.prepared.alphabet W.prepared.graph .inside false
    Q.aligned.inserted (.leaf W.opening.checkpoint.right) Q.inserted.size
  let M := max Q.old.bound (max Q.inserted.bound (max c₁ (max c₂ (max g₁ (max g₂ d)))))
  have hb₁M : Q.old.bound ≤ M := by dsimp [M]; omega
  have hb₂M : Q.inserted.bound ≤ M := by dsimp [M]; omega
  have hc₁M : c₁ ≤ M := by dsimp [M]; omega
  have hc₂M : c₂ ≤ M := by dsimp [M]; omega
  have hg₁M : g₁ ≤ M := by dsimp [M]; omega
  have hg₂M : g₂ ≤ M := by dsimp [M]; omega
  have hdM : d ≤ M := by dsimp [M]; omega
  obtain ⟨A, E, hord, hmarker, hentries, hfirst, hlast, hsep, hA, hE⟩ :=
    SharedFirstLast.body_pair_separated W.prepared.infinite Q.aligned.old.stem
      Q.aligned.inserted.stem Q.aligned.old.room Q.aligned.inserted.room Q.aligned.ordinary M
      Q.old.size Q.inserted.size Q.old.positive Q.inserted.positive
  have hAc : ∀ x ∈ BodyResponses.newWord A.position, c₁ < x :=
    fun x hx ↦ hc₁M.trans_lt (hA x hx).2
  have hEc : ∀ x ∈ BodyResponses.newWord E.position, c₂ < x :=
    fun x hx ↦ hc₂M.trans_lt (hE x hx).2
  have hbA := Q.old.certificate A (fun x hx ↦ hKH (hA x hx).1)
    (fun x hx ↦ hb₁M.trans_lt (hA x hx).2)
  have hbE := Q.inserted.certificate E (fun x hx ↦ (hE x hx).1)
    (fun x hx ↦ hb₂M.trans_lt (hE x hx).2)
  let F : Pair Q :=
    { oldSetup := A, insertedSetup := E, ordinary := hord, marker := hmarker
      entries := hentries, first := hfirst, last := hlast, separated := hsep
      oldStep := body_step O.prepared.graph .inside false Q.aligned.old
        (.leaf O.opening.checkpoint.right) A
        (command_allowed O.prepared.graph .inside false Q.aligned.old
          (.leaf O.opening.checkpoint.right) Q.aligned.oldCommand)
        (fun x hx ↦ hKH (hA x hx).1) hAc (fun x hx ↦ hg₁M.trans_lt (hA x hx).2)
      insertedStep := body_step W.prepared.graph .inside false Q.aligned.inserted
        (.leaf W.opening.checkpoint.right) E
        (command_allowed W.prepared.graph .inside false Q.aligned.inserted
          (.leaf W.opening.checkpoint.right) Q.aligned.insertedCommand)
        (fun x hx ↦ (hE x hx).1) hEc (fun x hx ↦ hg₂M.trans_lt (hE x hx).2)
      oldBlue := hbA, insertedBlue := hbE
      oldHandoff := body_handoff O.prepared.infinite O.prepared.graph .inside false
        Q.aligned.old (.leaf O.opening.checkpoint.right) A hAc hbA
      insertedHandoff := body_handoff W.prepared.infinite W.prepared.graph .inside false
        Q.aligned.inserted (.leaf W.opening.checkpoint.right) E hEc hbE }
  exact ⟨F, fun x hx ↦ ⟨(hA x hx).1, hdM.trans_lt (hA x hx).2⟩,
    fun x hx ↦ ⟨(hE x hx).1, hdM.trans_lt (hE x hx).2⟩⟩

end Erdos118.StrictSharedFirstLeaves
