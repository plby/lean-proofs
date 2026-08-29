/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFinitePriorityRelation
import ErdosProblems.Erdos599.GroundingFiniteSourceRoot

/-!
# Root defects created by a genuine finite-priority insertion

Unlike the purely backward diagnostic, this file keeps the forward edges of
the private finite trace.  A base root can be destroyed in exactly three
ways: by stopping at the prescribed boundary, by deleting a private backward
edge, or by deleting a base edge which competes at a head or tail with an
inserted private forward edge.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingFinitePriorityGeneralRootObstruction

open Alternating GroundingRootedReachabilityWarp
open DWeb.KappaLadder

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Exact last-deleted data for an arbitrary finite priority trace. -/
structure PriorityDeletedRootData
    (E : Set (V × V)) (Q : FiniteTrace Gamma.graph)
    (T A : Set V) (boundary : V) where
  baseRoot : RootedPath (Gamma := Gamma) E A boundary
  boundary_not_rooted : ¬ ∃ a ∈ A,
    Relation.ReflTransGen (fun x y ↦ (x, y) ∈
      GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T)
      a boundary
  lastDeleted : LastDeletedHead baseRoot.path
    (GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T)
  lastDeleted_head_not_rooted : ¬ ∃ a ∈ A,
    Relation.ReflTransGen (fun x y ↦ (x, y) ∈
      GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T)
      a lastDeleted.head
  incomingTail : V
  incoming_mem_path :
    (incomingTail, lastDeleted.head) ∈ baseRoot.path.edgeSet
  incoming_not_priority :
    (incomingTail, lastDeleted.head) ∉
      GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T
  incoming_cause : incomingTail ∈ T ∨
    (incomingTail, lastDeleted.head) ∈
      (AltPath.finite Q).directionEdges .backward ∨
    ∃ f ∈ (AltPath.finite Q).directionEdges .forward,
      incomingTail = f.1 ∨ lastDeleted.head = f.2

namespace PriorityDeletedRootData

/-- The suffix after the last deleted head still reaches the old boundary
in the genuine priority relation. -/
theorem suffix_reaches_boundary
    {E : Set (V × V)} {Q : FiniteTrace Gamma.graph}
    {T A : Set V} {boundary : V}
    (D : PriorityDeletedRootData E Q T A boundary) :
    Relation.ReflTransGen (fun x y ↦ (x, y) ∈
      GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T)
      D.lastDeleted.head boundary := by
  have hsuffix : Relation.ReflTransGen (fun x y ↦ (x, y) ∈
      GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T)
      D.lastDeleted.suffix.start D.lastDeleted.suffix.finish := by
    apply Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ D.lastDeleted.suffix.edgeSet)
      (p := fun x y ↦ (x, y) ∈
        GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T)
    · intro x y hxy
      exact D.lastDeleted.suffix_edgeSet_subset hxy
    · exact Walk.reflTransGen_edgeSet D.lastDeleted.suffix.walk
  rw [D.lastDeleted.suffix_start, D.lastDeleted.suffix_finish,
    D.baseRoot.finish_eq] at hsuffix
  exact hsuffix

end PriorityDeletedRootData

/-- Complete root-loss classification for a genuine finite priority trace.
The proof unfolds the actual retained-base construction; no forward-edge
failure is discarded. -/
theorem exists_priorityDeletedRootData
    (E : Set (V × V)) (Q : FiniteTrace Gamma.graph)
    (T A : Set V) (boundary : V)
    (hEadj : E ⊆ {e | Gamma.graph.Adj e.1 e.2})
    (hbaseRoot : ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a boundary)
    (hpriorityUnrooted : ¬ ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈
        GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T)
        a boundary) :
    Nonempty (PriorityDeletedRootData E Q T A boundary) := by
  let P : RootedPath (Gamma := Gamma) E A boundary :=
    (exists_rootedPath_of_reflTransGen hEadj hbaseRoot).some
  have hdeleted : ∃ e ∈ P.path.edgeSet,
      e ∉ GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T := by
    by_contra hnone
    apply hpriorityUnrooted
    refine ⟨P.path.start, P.start_mem, ?_⟩
    have hreach : Relation.ReflTransGen (fun x y ↦ (x, y) ∈
        GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T)
        P.path.start P.path.finish := by
      apply Relation.ReflTransGen.mono
        (r := fun x y ↦ (x, y) ∈ P.path.edgeSet)
        (p := fun x y ↦ (x, y) ∈
          GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T)
      · intro x y hxy
        by_contra hnot
        exact hnone ⟨(x, y), hxy, hnot⟩
      · exact Walk.reflTransGen_edgeSet P.path.walk
    simpa only [P.finish_eq] using hreach
  let D : LastDeletedHead P.path
      (GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T) :=
    (exists_lastDeletedHead P.path hdeleted).some
  have hheadUnrooted : ¬ ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈
        GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T)
        a D.head := by
    rintro ⟨a, ha, haD⟩
    apply hpriorityUnrooted
    refine ⟨a, ha, haD.trans ?_⟩
    have hsuffix : Relation.ReflTransGen (fun x y ↦ (x, y) ∈
        GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T)
        D.suffix.start D.suffix.finish := by
      apply Relation.ReflTransGen.mono
        (r := fun x y ↦ (x, y) ∈ D.suffix.edgeSet)
        (p := fun x y ↦ (x, y) ∈
          GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T)
      · intro x y hxy
        exact D.suffix_edgeSet_subset hxy
      · exact Walk.reflTransGen_edgeSet D.suffix.walk
    rw [D.suffix_start, D.suffix_finish, P.finish_eq] at hsuffix
    exact hsuffix
  obtain ⟨tail, hinPath, hnotPriority⟩ := D.deleted_incoming
  have hinE : (tail, D.head) ∈ E := P.edgeSet_subset hinPath
  have hcause : tail ∈ T ∨
      (tail, D.head) ∈ (AltPath.finite Q).directionEdges .backward ∨
      ∃ f ∈ (AltPath.finite Q).directionEdges .forward,
        tail = f.1 ∨ D.head = f.2 := by
    by_cases htail : tail ∈ T
    · exact Or.inl htail
    · right
      change (tail, D.head) ∉
        GroundingFinitePriorityRelation.stopAt
          (GroundingFinitePriorityRelation.priorityEdges E
            ((AltPath.finite Q).directionEdges .backward)
            ((AltPath.finite Q).directionEdges .forward)) T at hnotPriority
      have hnotRetained : (tail, D.head) ∉
          GroundingFinitePriorityRelation.retainedBaseEdges E
            ((AltPath.finite Q).directionEdges .backward)
            ((AltPath.finite Q).directionEdges .forward) := by
        intro hretained
        exact hnotPriority ⟨Or.inl hretained, htail⟩
      change (tail, D.head) ∉ E \ (
        (AltPath.finite Q).directionEdges .backward ∪
          GroundingFinitePriorityRelation.forwardConflictEdges E
            ((AltPath.finite Q).directionEdges .forward)) at hnotRetained
      by_cases hback : (tail, D.head) ∈
          (AltPath.finite Q).directionEdges .backward
      · exact Or.inl hback
      · right
        have hconflict : (tail, D.head) ∈
            GroundingFinitePriorityRelation.forwardConflictEdges E
              ((AltPath.finite Q).directionEdges .forward) := by
          by_contra hnotConflict
          exact hnotRetained ⟨hinE, by
            intro hbad
            exact hbad.elim hback hnotConflict⟩
        exact hconflict.2
  exact ⟨{
    baseRoot := P
    boundary_not_rooted := hpriorityUnrooted
    lastDeleted := D
    lastDeleted_head_not_rooted := hheadUnrooted
    incomingTail := tail
    incoming_mem_path := hinPath
    incoming_not_priority := hnotPriority
    incoming_cause := hcause }⟩

end GroundingFinitePriorityGeneralRootObstruction
end Erdos599

#print axioms
  Erdos599.GroundingFinitePriorityGeneralRootObstruction.exists_priorityDeletedRootData
#print axioms
  Erdos599.GroundingFinitePriorityGeneralRootObstruction.PriorityDeletedRootData.suffix_reaches_boundary
