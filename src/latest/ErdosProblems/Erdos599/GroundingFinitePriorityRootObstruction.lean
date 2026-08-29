/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFinitePriorityRelation
import ErdosProblems.Erdos599.GroundingFiniteSourceRoot

/-!
# Root defects created by a finite priority deletion

A purely backward priority trace only removes its backward edges and then
stops at the prescribed boundary.  When this destroys an existing root, a
last deleted head gives a lossless normal form: the surviving suffix still
reaches the original boundary point, and the deleted incoming edge is either
a boundary departure or one of the private backward edges.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingFinitePriorityRootObstruction

open Alternating GroundingRootedReachabilityWarp
open DWeb.KappaLadder

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Exact last-deleted data when a purely backward priority insertion
destroys a root which existed in the base relation.  The `LastDeletedHead`
field retains the whole surviving continuation to `boundary`. -/
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
      (AltPath.finite Q).directionEdges .backward

namespace PriorityDeletedRootData

/-- The retained suffix is an explicit priority-relation continuation from
the last deleted head to the original boundary point. -/
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

/-- Complete root-loss classification for a purely backward priority
trace. -/
theorem exists_priorityDeletedRootData
    (E : Set (V × V)) (Q : FiniteTrace Gamma.graph)
    (T A : Set V) (boundary : V)
    (hEadj : E ⊆ {e | Gamma.graph.Adj e.1 e.2})
    (hforward : (AltPath.finite Q).directionEdges .forward = ∅)
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
      (tail, D.head) ∈ (AltPath.finite Q).directionEdges .backward := by
    by_cases htail : tail ∈ T
    · exact Or.inl htail
    · right
      by_contra hnotBack
      apply hnotPriority
      change (tail, D.head) ∈
        GroundingFinitePriorityRelation.stopAt
          (GroundingFinitePriorityRelation.priorityEdges E
            ((AltPath.finite Q).directionEdges .backward)
            ((AltPath.finite Q).directionEdges .forward)) T
      refine ⟨?_, htail⟩
      left
      refine ⟨hinE, ?_⟩
      intro hdeleted
      rcases hdeleted with hback | hconflict
      · exact hnotBack hback
      · rw [hforward] at hconflict
        rcases hconflict with ⟨_hinE, f, hf, _hincidence⟩
        exact hf
  exact ⟨{
    baseRoot := P
    boundary_not_rooted := hpriorityUnrooted
    lastDeleted := D
    lastDeleted_head_not_rooted := hheadUnrooted
    incomingTail := tail
    incoming_mem_path := hinPath
    incoming_not_priority := hnotPriority
    incoming_cause := hcause }⟩

end GroundingFinitePriorityRootObstruction
end Erdos599

#print axioms
  Erdos599.GroundingFinitePriorityRootObstruction.exists_priorityDeletedRootData
#print axioms
  Erdos599.GroundingFinitePriorityRootObstruction.PriorityDeletedRootData.suffix_reaches_boundary
