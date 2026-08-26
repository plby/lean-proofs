import ErdosProblems.Erdos118.LateOpening
import ErdosProblems.Erdos118.MiddleRun
import ErdosProblems.Erdos118.SelectedLeafReplay

/-!
The first actual middle run, with the fine body label retained for the
second game. The old right continuation fires an earlier extracted actual
selected-leaf certificate in the third game.
-/

namespace Erdos118.FirstMiddle

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays BoundaryRelays FreshCheckpoints

structure Diagram {H : Set ℕ} {B : SimpleGraph G} (O : LateOpening.Opening H B) where
  bound : ℕ
  fineBound : O.insertedPositive.bound ≤ bound
  finePair : pairBound (.body O.insertedBody, .leaf O.insertedRight) ≤ bound
  fineGuard : guard H B .inside false O.insertedBody (.leaf O.insertedRight)
    O.insertedPositive.size ≤ bound
  fineStem : O.insertedBody.stem.decorated.sum ≤ bound
  left : Pending
  right : Pending
  lastIndex : ℕ
  leftRoot : left.roots = []
  leftLeaf : left.leaves = [lastIndex]
  rightRoot : right.roots = []
  rightLeaf : right.leaves = []
  leftStem : left.position.stem = O.oldBody.stem
  rightBody : SameBody O.oldRight right
  leftExact : ExactSlots.Exact (.leaf left)
  rightExact : ExactSlots.Exact (.leaf right)
  reserve : SharedLast.Reserve H bound O.insertedPositive.size left.position
  entriesSupported : ∀ x ∈ left.position.entries, x ∈ H
  run : ConservativeRuns.Run H (GraphPayoff.payoff B .inside)
    (.body O.oldBody, .leaf O.oldRight) (.leaf left, .leaf right)
  blue : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf left, .leaf right)) true
  handoff : LeftBlue H (GraphPayoff.payoff B .inside) (.leaf left, .leaf right)
  targetRest : List ℕ
  targetSlot : O.first.target.leaves = O.oldRight.position.label.getLastD 0 :: targetRest
  certificate : SelectedLeafReplay.Certificate H B .inside false
    O.first.target (.leaf O.second.target) (O.oldRight.position.label.getLastD 0)
    targetRest targetSlot
  replay : SelectedLeafReplay.Replay certificate right.position

theorem exists_diagram {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (O : LateOpening.Opening H B) : Nonempty (Diagram O) := by
  have hi : O.first.target.position.entries.length < O.oldRight.position.label.getLastD 0 := by
    rw [O.first.entries]
    exact DeferredBodyReplay.current_lt_last O.oldRight O.oldRightNonlast
  obtain ⟨rest, hslot⟩ := NextSelectedLeaf.next_leaf O.first.target O.first.exactSlots
    (O.oldRight.position.label.getLastD 0) O.first.last_mem hi
    (by intro j hj hij; exact O.first.next_le j hj (O.first.entries ▸ hij))
  obtain ⟨C⟩ := SelectedLeafReplay.exists_certificate hH B .inside false
    O.first.target (.leaf O.second.target) (O.oldRight.position.label.getLastD 0)
    rest hslot O.second.handoff
  let p := pairBound (.body O.oldBody, .leaf O.oldRight)
  let q := pairBound (.body O.insertedBody, .leaf O.insertedRight)
  let g := guard H B .inside false O.oldBody (.leaf O.oldRight) O.oldPositive.size
  let f := guard H B .inside false O.insertedBody (.leaf O.insertedRight) O.insertedPositive.size
  let M := O.oldPositive.bound + O.insertedPositive.bound + p + q + g + f +
    O.insertedBody.stem.decorated.sum + C.bound
  have hMold : O.oldPositive.bound ≤ M := by omega
  have hMfine : O.insertedPositive.bound ≤ M := by omega
  have hMp : p ≤ M := by omega
  have hMq : q ≤ M := by omega
  have hMg : g ≤ M := by omega
  have hMf : f ≤ M := by omega
  have hMs : O.insertedBody.stem.decorated.sum ≤ M := by omega
  have hMC : C.bound ≤ M := by omega
  obtain ⟨A, Z, hf⟩ := SharedLast.body_reserved_sizes O.oldBody.stem O.oldBody.room hH M
    O.oldPositive.size O.insertedPositive.size
  have hb := O.oldPositive.certificate A (fun x hx ↦ (hf x hx).1)
    (fun x hx ↦ hMold.trans_lt (hf x hx).2)
  have hs := body_step B .inside false O.oldBody (.leaf O.oldRight) A
    (command_allowed B .inside false O.oldBody (.leaf O.oldRight) O.oldCommand)
    (fun x hx ↦ (hf x hx).1) (fun x hx ↦ hMp.trans_lt (hf x hx).2)
    (fun x hx ↦ hMg.trans_lt (hf x hx).2)
  have hh := body_handoff hH B .inside false O.oldBody (.leaf O.oldRight) A
    (fun x hx ↦ hMp.trans_lt (hf x hx).2) hb
  let P := applyBody O.oldBody A
  have hP : ExactSlots.Exact (.leaf P) :=
    ExactSlots.step_exact (DecisionStates.Step.body O.oldBody A) O.oldExact
  have hPL : P.leaves ≠ [] := by
    intro he
    have he' : A.position.label.tail = [] := he
    have hlen := congrArg List.length he'
    rw [List.length_tail, A.label_length] at hlen
    simp only [List.length_nil] at hlen
    have hk := O.oldPositive.positive
    omega
  obtain ⟨P', Q', j, hPP, hQQ, hPL', hQL', hP', hQ', hrun, hb', hh', hf'⟩ :=
    MiddleRun.endpoint hH Set.Subset.rfl B M P O.oldRight O.oldLast O.oldRightLast hPL
      hP O.oldManaged.exact hb (fun _ ↦ hh)
  obtain ⟨u, v, hu, hv, huf, hvf⟩ := hf'
  obtain ⟨R⟩ := C.fire_last O.oldRight Q' O.first.exactSlots O.first.ordinary O.first.entries
    hQQ hQ' hQL' v hv (fun x hx ↦ (hvf x hx).1)
    (fun x hx ↦ hMC.trans_lt (hvf x hx).2)
  have hentries : P'.position.entries = P.position.entries ++ u := by
    change P'.position.ordinary = P.position.ordinary ++ u at hu
    simp only [Position.ordinary, hPP.2.1, hPP.2.2.1, List.append_assoc] at hu
    have he := List.append_cancel_left hu
    have he' : P.position.size :: P'.position.entries =
        P.position.size :: (P.position.entries ++ u) := by
      simpa only [List.cons_append] using he
    exact (List.cons.inj he').2
  have hsupport : ∀ x ∈ P'.position.entries, x ∈ H := by
    intro x hx
    rw [hentries] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact (hf x (List.mem_append_right _ (List.mem_cons_of_mem _ hx))).1
    · exact (huf x hx).1
  exact ⟨{
    bound := M, fineBound := hMfine, finePair := hMq, fineGuard := hMf, fineStem := hMs
    left := P', right := Q', lastIndex := j, leftRoot := hPP.1, leftLeaf := hPL'
    rightRoot := hQQ.1, rightLeaf := hQL', leftStem := hPP.2.1.trans A.stem_eq
    rightBody := hQQ, leftExact := hP', rightExact := hQ'
    reserve := Z.move P'.position hPP.2.1 hPP.2.2.1 hPP.2.2.2.1
    entriesSupported := hsupport, run := Relation.ReflTransGen.head hs hrun
    blue := hb', handoff := hh', targetRest := rest, targetSlot := hslot
    certificate := C, replay := R }⟩

end Erdos118.FirstMiddle
