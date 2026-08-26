import ErdosProblems.Erdos118.SecondMiddle
import ErdosProblems.Erdos118.InsideCompletion

/-! The two middle phases produce a literal completion triangle when the
third game's retained right body has the positive next-label shape. -/

namespace Erdos118.TwoMiddlePositive

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays BoundaryRelays FreshCheckpoints

theorem triangle {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    {O : LateOpening.Opening H B} (D : FirstMiddle.Diagram O)
    (hmem : O.insertedRight.position.label.getLastD 0 ∈ O.second.target.position.label)
    (hmin : ∀ j ∈ O.second.target.position.label, O.insertedRight.position.entries.length < j →
      O.insertedRight.position.label.getLastD 0 ≤ j) :
    ∃ s t u : G, B.Adj s t ∧ B.Adj s u ∧ B.Adj t u := by
  have heU := congrArg List.length O.second.entries
  have hi : O.second.target.position.entries.length <
      O.insertedRight.position.label.getLastD 0 := by
    rw [heU]
    exact DeferredBodyReplay.current_lt_last O.insertedRight O.insertedRightNonlast
  obtain ⟨rest, hslot⟩ := NextSelectedLeaf.next_leaf O.second.target O.second.exactSlots
    (O.insertedRight.position.label.getLastD 0) hmem hi
    (by intro j hj hij; exact hmin j hj (heU ▸ hij))
  obtain ⟨CU⟩ := SelectedLeafReplay.exists_certificate hH B .inside true
    O.second.target (.leaf D.replay.target) (O.insertedRight.position.label.getLastD 0)
    rest hslot D.replay.handoff
  obtain ⟨L⟩ := SecondMiddle.exists_last_pair hH B D CU.bound
  obtain ⟨RU⟩ := CU.fire_last O.insertedRight L.right O.second.exactSlots
    O.second.ordinary heU L.rightBody L.rightExact L.rightLast.2 L.suffix L.ordinary
    (fun x hx ↦ (L.fresh x hx).1) (fun x hx ↦ (L.fresh x hx).2)
  exact InsideCompletion.triangle hH B L.oldLeft L.fineLeft D.right L.right
    D.replay.target RU.target L.oldLast L.fineLast ⟨D.rightRoot, D.rightLeaf⟩ L.rightLast
    L.sameOrdinary D.replay.ordinary RU.ordinary L.oldBlue L.fineBlue RU.blue

end Erdos118.TwoMiddlePositive
