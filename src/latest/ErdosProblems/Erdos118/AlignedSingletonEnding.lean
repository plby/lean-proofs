import ErdosProblems.Erdos118.AlignedAllBodies
import ErdosProblems.Erdos118.SharedFinalLeaf

/-! The zero-parameter alternative of the actual aligned three-game
diagram produces a triangle. The positive-parameter ending is separate. -/

namespace Erdos118.AlignedSingletonEnding

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays AlignedLastOpening AlignedFirstBodies AlignedBridgeDiagram
open AlignedAllBodies

private theorem one_leaf (P : Pending) (hP : ExactSlots.Exact (.leaf P))
    (hlen : P.leaves.length = 1) : P.leaves = [P.position.label.getLastD 0] := by
  obtain ⟨j, hj⟩ := List.length_eq_one_iff.mp hlen
  exact hj.trans (congrArg (fun x ↦ [x]) (ExactSlots.pending_next_last P hP hj).symm)

theorem triangle {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    {O : Opening H B} {F : Pair O} {D : Diagram O F} {T : TPair D}
    (C : UCertificates D T) (U : UPair C) (ht : D.lowerCertificate.size = 0) :
    ∃ s t u : G, B.Adj s t ∧ B.Adj s u ∧ B.Adj t u := by
  have hd := C.lowerZero.mp ht
  have hp : O.oldPositive.size = 1 := by rw [D.lowerSize, ht]
  have hq : O.insertedPositive.size = 1 := by rw [C.lowerSize, hd]
  have hS₀len : F.oldLeft.leaves.length = 1 := by
    change F.oldSetup.position.label.tail.length = 1
    rw [List.length_tail, F.oldSetup.label_length, hp]
  have hS₁len : F.insertedLeft.leaves.length = 1 := by
    change F.insertedSetup.position.label.tail.length = 1
    rw [List.length_tail, F.insertedSetup.label_length, hq]
  have hS₀L := one_leaf F.oldLeft F.exactSlots.1 hS₀len
  have hS₁L : F.insertedLeft.leaves = [F.oldLeft.position.label.getLastD 0] := by
    rw [one_leaf F.insertedLeft F.exactSlots.2 hS₁len]
    exact congrArg (fun x ↦ [x]) F.sameLast.symm
  have hTL : T.lower.leaves = [] := by
    apply List.eq_nil_of_length_eq_zero
    change T.lowerSetup.position.label.tail.length = 0
    rw [List.length_tail, T.lowerSetup.label_length, ht]
  have hUL : U.lower.leaves = [] := by
    apply List.eq_nil_of_length_eq_zero
    change U.lowerSetup.position.label.tail.length = 0
    rw [List.length_tail, U.lowerSetup.label_length, hd]
  exact SharedFinalLeaf.triangle hH B F.oldLeft F.insertedLeft T.lower U.lower T.upper U.upper
    (F.oldLeft.position.label.getLastD 0) F.exactSlots.1 F.roots_nil.1 F.roots_nil.2 hS₀L hS₁L
    ⟨D.lowerLast, hTL⟩ ⟨C.lowerLast, hUL⟩ F.sameOrdinary (congrArg List.length F.sameEntries)
    T.sameOrdinary.symm U.sameOrdinary.symm T.lowerHandoff U.lowerHandoff U.upperBlue

end Erdos118.AlignedSingletonEnding
