/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFinitePriorityGeneralRootObstruction
import ErdosProblems.Erdos599.GroundingPathPrefix

/-!
# Private-boundary normalization for a genuine finite-priority insertion

A private ambient source--target path meeting a frontier only at its retained
endpoint cannot lose its root merely because the priority relation is stopped
at that frontier: the tail of the last deleted edge occurs strictly before
the endpoint.  The remaining causes are therefore literal base-relation
absence, a private backward edge, or incidence conflict with an inserted
private forward edge.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingFinitePriorityGeneralPrivateBoundary

open DirectedPath Alternating
open DWeb.KappaLadder

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Exact last-deleted data on a private ambient path for a genuine private
finite trace. -/
structure PrivatePathDeletedData
    (E : Set (V × V)) (Q : FiniteTrace Gamma.graph)
    (T : Set V) (unused boundary : V) where
  root : V
  root_mem_source : root ∈ Gamma.source
  root_ne_unused : root ≠ unused
  targetWitness : FinitePath Gamma.graph
  targetWitness_spec : Gamma.IsTargetPathFrom root targetWitness
  targetWitness_inter_boundary : targetWitness.support ∩ T = {boundary}
  path : FinitePath Gamma.graph
  path_start_root : path.start = root
  path_finish_boundary : path.finish = boundary
  path_support_subset : path.support ⊆ targetWitness.support
  lastDeleted : LastDeletedHead path
    (GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T)
  lastDeleted_head_not_rooted : ¬ ∃ a ∈ Gamma.source \ {unused},
    Relation.ReflTransGen (fun x y ↦ (x, y) ∈
      GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T)
      a lastDeleted.head
  incomingTail : V
  incoming_mem_path : (incomingTail, lastDeleted.head) ∈ path.edgeSet
  incoming_not_priority : (incomingTail, lastDeleted.head) ∉
    GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T
  incomingTail_not_boundary : incomingTail ∉ T
  incoming_cause :
    (incomingTail, lastDeleted.head) ∉ E ∨
    (incomingTail, lastDeleted.head) ∈
      (AltPath.finite Q).directionEdges .backward ∨
    ∃ f ∈ (AltPath.finite Q).directionEdges .forward,
      incomingTail = f.1 ∨ lastDeleted.head = f.2

namespace PrivatePathDeletedData

/-- The retained suffix still reaches the private boundary endpoint. -/
theorem suffix_reaches_boundary
    {E : Set (V × V)} {Q : FiniteTrace Gamma.graph}
    {T : Set V} {unused boundary : V}
    (D : PrivatePathDeletedData E Q T unused boundary) :
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
    D.path_finish_boundary] at hsuffix
  exact hsuffix

end PrivatePathDeletedData

/-- A private ambient witness whose root is allowed has an exact
non-boundary last-deleted normal form for the genuine priority insertion. -/
theorem exists_privatePathDeletedData
    (E : Set (V × V)) (Q : FiniteTrace Gamma.graph)
    (T : Set V) (unused boundary root : V)
    (hrootSource : root ∈ Gamma.source) (hrootNe : root ≠ unused)
    (p : FinitePath Gamma.graph) (hp : Gamma.IsTargetPathFrom root p)
    (hpBoundary : p.support ∩ T = {boundary})
    (hunrooted : ¬ ∃ a ∈ Gamma.source \ {unused},
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈
        GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T)
        a boundary) :
    Nonempty (PrivatePathDeletedData E Q T unused boundary) := by
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
      e ∉ GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T := by
    by_contra hnone
    apply hunrooted
    refine ⟨r.start, hstartAllowed, ?_⟩
    have hreach : Relation.ReflTransGen (fun x y ↦ (x, y) ∈
        GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T)
        r.start r.finish := by
      apply Relation.ReflTransGen.mono
        (r := fun x y ↦ (x, y) ∈ r.edgeSet)
        (p := fun x y ↦ (x, y) ∈
          GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T)
      · intro x y hxy
        by_contra hnot
        exact hnone ⟨(x, y), hxy, hnot⟩
      · exact Walk.reflTransGen_edgeSet r.walk
    simpa only [hrFinish] using hreach
  let D : LastDeletedHead r
      (GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T) :=
    (exists_lastDeletedHead r hdeleted).some
  have hheadUnrooted : ¬ ∃ a ∈ Gamma.source \ {unused},
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈
        GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T)
        a D.head := by
    rintro ⟨a, ha, haD⟩
    apply hunrooted
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
    rw [D.suffix_start, D.suffix_finish, hrFinish] at hsuffix
    exact hsuffix
  obtain ⟨tail, hinPath, hnotPriority⟩ := D.deleted_incoming
  have htailSupportR : tail ∈ r.support :=
    (r.edgeSet_subset_support_prod hinPath).1
  have htailSupport : tail ∈ p.support := hrSupport htailSupportR
  have htailNeBoundary : tail ≠ boundary := by
    rw [← hrFinish]
    exact FinitePath.source_ne_finish_of_mem_edgeSet r hinPath
  have htailNotT : tail ∉ T := by
    intro htailT
    have htailEq : tail = boundary := by
      have : tail ∈ ({boundary} : Set V) := by
        rw [← hpBoundary]
        exact ⟨htailSupport, htailT⟩
      simpa only [Set.mem_singleton_iff] using this
    exact htailNeBoundary htailEq
  have hcause : (tail, D.head) ∉ E ∨
      (tail, D.head) ∈ (AltPath.finite Q).directionEdges .backward ∨
      ∃ f ∈ (AltPath.finite Q).directionEdges .forward,
        tail = f.1 ∨ D.head = f.2 := by
    by_cases hnotE : (tail, D.head) ∉ E
    · exact Or.inl hnotE
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
        exact hnotPriority ⟨Or.inl hretained, htailNotT⟩
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
          exact hnotRetained ⟨not_not.mp hnotE, by
            intro hbad
            exact hbad.elim hback hnotConflict⟩
        exact hconflict.2
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
    incomingTail_not_boundary := htailNotT
    incoming_cause := hcause }⟩

end GroundingFinitePriorityGeneralPrivateBoundary
end Erdos599

#print axioms
  Erdos599.GroundingFinitePriorityGeneralPrivateBoundary.exists_privatePathDeletedData
#print axioms
  Erdos599.GroundingFinitePriorityGeneralPrivateBoundary.PrivatePathDeletedData.suffix_reaches_boundary
