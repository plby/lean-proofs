/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFinitePriorityRootObstruction
import ErdosProblems.Erdos599.GroundingSeparatorPointRemoval
import ErdosProblems.Erdos599.GroundingPathPrefix

/-!
# Private-boundary normalization for a finite priority root defect

If deleting one unrooted boundary point does not preserve separation, there
is an ambient source--target path meeting the old boundary only there.  Its
last deleted edge cannot be a boundary stop.  Thus the priority root defect
is reduced to an old base-relation deletion or to one of the newly inserted
private backward deletions.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingFinitePriorityPrivateBoundary

open DirectedPath Alternating
open DWeb.KappaLadder

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Last-deleted data on an ambient path which meets the boundary only at
its final point. -/
structure PrivatePathDeletedData
    (E : Set (V × V)) (Q : FiniteTrace Gamma.graph)
    (B : Set V) (unused boundary : V) where
  root : V
  root_mem_source : root ∈ Gamma.source
  root_ne_unused : root ≠ unused
  targetWitness : FinitePath Gamma.graph
  targetWitness_spec : Gamma.IsTargetPathFrom root targetWitness
  targetWitness_inter_boundary : targetWitness.support ∩ B = {boundary}
  path : FinitePath Gamma.graph
  path_start_root : path.start = root
  path_finish_boundary : path.finish = boundary
  path_support_subset : path.support ⊆ targetWitness.support
  lastDeleted : LastDeletedHead path
    (GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q B)
  lastDeleted_head_not_rooted : ¬ ∃ a ∈ Gamma.source \ {unused},
    Relation.ReflTransGen (fun x y ↦ (x, y) ∈
      GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q B)
      a lastDeleted.head
  incomingTail : V
  incoming_mem_path : (incomingTail, lastDeleted.head) ∈ path.edgeSet
  incoming_not_priority : (incomingTail, lastDeleted.head) ∉
    GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q B
  incomingTail_not_boundary : incomingTail ∉ B
  incoming_cause :
    (incomingTail, lastDeleted.head) ∉ E ∨
    (incomingTail, lastDeleted.head) ∈
      (AltPath.finite Q).directionEdges .backward

namespace PrivatePathDeletedData

theorem suffix_reaches_boundary
    {E : Set (V × V)} {Q : FiniteTrace Gamma.graph}
    {B : Set V} {unused boundary : V}
    (D : PrivatePathDeletedData E Q B unused boundary) :
    Relation.ReflTransGen (fun x y ↦ (x, y) ∈
      GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q B)
      D.lastDeleted.head boundary := by
  have hsuffix : Relation.ReflTransGen (fun x y ↦ (x, y) ∈
      GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q B)
      D.lastDeleted.suffix.start D.lastDeleted.suffix.finish := by
    apply Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ D.lastDeleted.suffix.edgeSet)
      (p := fun x y ↦ (x, y) ∈
        GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q B)
    · intro x y hxy
      exact D.lastDeleted.suffix_edgeSet_subset hxy
    · exact Walk.reflTransGen_edgeSet D.lastDeleted.suffix.walk
  rw [D.lastDeleted.suffix_start, D.lastDeleted.suffix_finish,
    D.path_finish_boundary] at hsuffix
  exact hsuffix

end PrivatePathDeletedData

/-- A private ambient witness whose root is not the deliberately deleted
source has an exact non-boundary last-deleted normal form. -/
theorem exists_privatePathDeletedData
    (E : Set (V × V)) (Q : FiniteTrace Gamma.graph)
    (B : Set V) (unused boundary root : V)
    (hforward : (AltPath.finite Q).directionEdges .forward = ∅)
    (hrootSource : root ∈ Gamma.source) (hrootNe : root ≠ unused)
    (p : FinitePath Gamma.graph) (hp : Gamma.IsTargetPathFrom root p)
    (hpBoundary : p.support ∩ B = {boundary})
    (hunrooted : ¬ ∃ a ∈ Gamma.source \ {unused},
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈
        GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q B)
        a boundary) :
    Nonempty (PrivatePathDeletedData E Q B unused boundary) := by
  have hbSupport : boundary ∈ p.support := by
    have : boundary ∈ ({boundary} : Set V) := Set.mem_singleton boundary
    rw [← hpBoundary] at this
    exact this.1
  obtain ⟨r, hrStart, hrFinish, hrSupport, _hrEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix
      (Sum.inl p : Gamma.DPath) hbSupport
  have hpStart : p.start = root := hp.1
  have hstartAllowed : r.start ∈ Gamma.source \ {unused} := by
    rw [hrStart]
    change p.start ∈ Gamma.source \ {unused}
    rw [hpStart]
    exact ⟨hrootSource, by simpa using hrootNe⟩
  have hdeleted : ∃ e ∈ r.edgeSet,
      e ∉ GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q B := by
    by_contra hnone
    apply hunrooted
    refine ⟨r.start, hstartAllowed, ?_⟩
    have hreach : Relation.ReflTransGen (fun x y ↦ (x, y) ∈
        GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q B)
        r.start r.finish := by
      apply Relation.ReflTransGen.mono
        (r := fun x y ↦ (x, y) ∈ r.edgeSet)
        (p := fun x y ↦ (x, y) ∈
          GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q B)
      · intro x y hxy
        by_contra hnot
        exact hnone ⟨(x, y), hxy, hnot⟩
      · exact Walk.reflTransGen_edgeSet r.walk
    simpa only [hrFinish] using hreach
  let D : LastDeletedHead r
      (GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q B) :=
    (exists_lastDeletedHead r hdeleted).some
  have hheadUnrooted : ¬ ∃ a ∈ Gamma.source \ {unused},
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈
        GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q B)
        a D.head := by
    rintro ⟨a, ha, haD⟩
    apply hunrooted
    refine ⟨a, ha, haD.trans ?_⟩
    have hsuffix : Relation.ReflTransGen (fun x y ↦ (x, y) ∈
        GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q B)
        D.suffix.start D.suffix.finish := by
      apply Relation.ReflTransGen.mono
        (r := fun x y ↦ (x, y) ∈ D.suffix.edgeSet)
        (p := fun x y ↦ (x, y) ∈
          GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q B)
      · intro x y hxy
        exact D.suffix_edgeSet_subset hxy
      · exact Walk.reflTransGen_edgeSet D.suffix.walk
    rw [D.suffix_start, D.suffix_finish, hrFinish] at hsuffix
    exact hsuffix
  obtain ⟨tail, hinPath, hnotPriority⟩ := D.deleted_incoming
  have htailSupportR : tail ∈ r.support :=
    (r.edgeSet_subset_support_prod hinPath).1
  have htailSupport : tail ∈ p.support := hrSupport htailSupportR
  have htailNeBoundary : tail ≠ boundary := by
    rw [← hrFinish]
    exact FinitePath.source_ne_finish_of_mem_edgeSet r hinPath
  have htailNotB : tail ∉ B := by
    intro htailB
    have htailEq : tail = boundary := by
      have : tail ∈ ({boundary} : Set V) := by
        rw [← hpBoundary]
        exact ⟨htailSupport, htailB⟩
      simpa only [Set.mem_singleton_iff] using this
    exact htailNeBoundary htailEq
  have hcause : (tail, D.head) ∉ E ∨
      (tail, D.head) ∈ (AltPath.finite Q).directionEdges .backward := by
    by_cases hnotE : (tail, D.head) ∉ E
    · exact Or.inl hnotE
    · right
      by_contra hnotBack
      apply hnotPriority
      change (tail, D.head) ∈
        GroundingFinitePriorityRelation.stopAt
          (GroundingFinitePriorityRelation.priorityEdges E
            ((AltPath.finite Q).directionEdges .backward)
            ((AltPath.finite Q).directionEdges .forward)) B
      refine ⟨?_, htailNotB⟩
      left
      refine ⟨not_not.mp hnotE, ?_⟩
      intro hdeleted
      rcases hdeleted with hback | hconflict
      · exact hnotBack hback
      · rw [hforward] at hconflict
        rcases hconflict with ⟨_hinE, f, hf, _hincidence⟩
        exact hf
  exact ⟨{
    root := root
    root_mem_source := hrootSource
    root_ne_unused := hrootNe
    targetWitness := p
    targetWitness_spec := hp
    targetWitness_inter_boundary := hpBoundary
    path := r
    path_start_root := hrStart.trans hpStart
    path_finish_boundary := hrFinish
    path_support_subset := hrSupport
    lastDeleted := D
    lastDeleted_head_not_rooted := hheadUnrooted
    incomingTail := tail
    incoming_mem_path := hinPath
    incoming_not_priority := hnotPriority
    incomingTail_not_boundary := htailNotB
    incoming_cause := hcause }⟩

end GroundingFinitePriorityPrivateBoundary
end Erdos599

#print axioms
  Erdos599.GroundingFinitePriorityPrivateBoundary.exists_privatePathDeletedData
#print axioms
  Erdos599.GroundingFinitePriorityPrivateBoundary.PrivatePathDeletedData.suffix_reaches_boundary
