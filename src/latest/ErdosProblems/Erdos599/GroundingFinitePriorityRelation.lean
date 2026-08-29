/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.TerminalContactSwitch
import ErdosProblems.Erdos599.SafeSwitching
import ErdosProblems.Erdos599.GroundingRootedReachabilityWarp
import ErdosProblems.Erdos599.GroundingBlockingReachability

/-!
# Inserting one finite alternating route with priority

Given an already locally bi-unique base relation, insert the forward edges
of one finite alternating trace after removing its backward edges and every
base edge which competes with an inserted forward edge at either endpoint.
Finally stop the result at an arbitrary boundary.  The resulting relation
is locally bi-unique by construction and uses only edges of the ambient
graph whenever both inputs do.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingFinitePriorityRelation

open Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Base edges which compete at a head or tail with a private forward
edge. -/
def forwardConflictEdges (E F : Set (V × V)) : Set (V × V) :=
  {e | e ∈ E ∧ ∃ f ∈ F, e.1 = f.1 ∨ e.2 = f.2}

/-- The base relation after deleting the private backward edges and all
incidence conflicts with the private forward relation. -/
def retainedBaseEdges (E B F : Set (V × V)) : Set (V × V) :=
  E \ (B ∪ forwardConflictEdges E F)

/-- Insert the private forward relation into the retained base. -/
def priorityEdges (E B F : Set (V × V)) : Set (V × V) :=
  retainedBaseEdges E B F ∪ F

/-- Stop every outgoing edge at `T`. -/
def stopAt (E : Set (V × V)) (T : Set V) : Set (V × V) :=
  {e ∈ E | e.1 ∉ T}

/-- The private finite trace inserted ahead of the base relation and
stopped at `T`. -/
def finitePriorityEdgesAt (E : Set (V × V))
    (Q : FiniteTrace Gamma.graph) (T : Set V) : Set (V × V) :=
  stopAt
    (priorityEdges E
      ((AltPath.finite Q).directionEdges .backward)
      ((AltPath.finite Q).directionEdges .forward)) T

/-- A purely backward private trace performs an exact edge deletion before
the boundary stop. -/
theorem finitePriorityEdgesAt_eq_stopAt_diff_of_forward_empty
    (E : Set (V × V)) (Q : FiniteTrace Gamma.graph) (T : Set V)
    (hforward : (AltPath.finite Q).directionEdges .forward = ∅) :
    finitePriorityEdgesAt E Q T =
      stopAt (E \ (AltPath.finite Q).directionEdges .backward) T := by
  simp [finitePriorityEdgesAt, priorityEdges, retainedBaseEdges,
    forwardConflictEdges, hforward]

/-- No backward edge of a purely backward private trace survives its
priority insertion. -/
theorem backward_not_mem_finitePriorityEdgesAt_of_forward_empty
    (E : Set (V × V)) (Q : FiniteTrace Gamma.graph) (T : Set V)
    (hforward : (AltPath.finite Q).directionEdges .forward = ∅)
    {e : V × V} (he : e ∈ (AltPath.finite Q).directionEdges .backward) :
    e ∉ finitePriorityEdgesAt E Q T := by
  rw [finitePriorityEdgesAt_eq_stopAt_diff_of_forward_empty E Q T hforward]
  intro hmem
  exact hmem.1.2 he

theorem retainedBaseEdges_subset
    (E B F : Set (V × V)) : retainedBaseEdges E B F ⊆ E :=
  Set.sdiff_subset

theorem priorityEdges_subset_union
    (E B F : Set (V × V)) : priorityEdges E B F ⊆ E ∪ F := by
  intro e he
  rcases he with he | he
  · exact Or.inl he.1
  · exact Or.inr he

theorem finitePriorityEdgesAt_subset_union
    (E : Set (V × V)) (Q : FiniteTrace Gamma.graph) (T : Set V) :
    finitePriorityEdgesAt E Q T ⊆
      E ∪ (AltPath.finite Q).directionEdges .forward := by
  intro e he
  exact priorityEdges_subset_union _ _ _ he.1

private theorem directionEdges_subset_edgeSet
    (Q : AltPath Gamma.graph) (d : Direction) :
    Q.directionEdges d ⊆ Q.edgeSet := by
  intro e he
  simp only [AltPath.directionEdges, Set.mem_iUnion] at he
  obtain ⟨l, hl, _hd, hel⟩ := he
  rw [Q.edgeSet_eq_iUnion_links]
  simp only [Set.mem_iUnion]
  exact ⟨l, hl, hel⟩

/-- Conflict deletion makes every surviving base edge incidence-disjoint
from every inserted forward edge. -/
theorem retainedBase_forward_incidence_disjoint
    {E B F : Set (V × V)} {e f : V × V}
    (he : e ∈ retainedBaseEdges E B F) (hf : f ∈ F) :
    e.1 ≠ f.1 ∧ e.2 ≠ f.2 := by
  constructor
  · intro htail
    exact he.2 (Or.inr ⟨he.1, f, hf, Or.inl htail⟩)
  · intro hhead
    exact he.2 (Or.inr ⟨he.1, f, hf, Or.inr hhead⟩)

/-- Inserting one locally bi-unique forward relation into a locally
bi-unique base remains locally bi-unique after the explicit conflict cut. -/
theorem priorityEdges_biUnique
    {E B F : Set (V × V)}
    (hE : Relator.BiUnique (fun x y ↦ (x, y) ∈ E))
    (hF : Relator.BiUnique (fun x y ↦ (x, y) ∈ F)) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ priorityEdges E B F) := by
  constructor
  · intro x y z hxz hyz
    rcases hxz with hxz | hxz <;> rcases hyz with hyz | hyz
    · exact hE.1 hxz.1 hyz.1
    · exact False.elim <|
        (retainedBase_forward_incidence_disjoint hxz hyz).2 rfl
    · exact False.elim <|
        (retainedBase_forward_incidence_disjoint hyz hxz).2 rfl
    · exact hF.1 hxz hyz
  · intro x y z hxy hxz
    rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz
    · exact hE.2 hxy.1 hxz.1
    · exact False.elim <|
        (retainedBase_forward_incidence_disjoint hxy hxz).1 rfl
    · exact False.elim <|
        (retainedBase_forward_incidence_disjoint hxz hxy).1 rfl
    · exact hF.2 hxy hxz

/-- Stopping at a boundary preserves local bi-uniqueness. -/
theorem stopAt_biUnique {E : Set (V × V)} (T : Set V)
    (hE : Relator.BiUnique (fun x y ↦ (x, y) ∈ E)) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ stopAt E T) := by
  exact ⟨fun _ _ _ hx hy ↦ hE.1 hx.1 hy.1,
    fun _ _ _ hx hy ↦ hE.2 hx.1 hy.1⟩

/-- The concrete finite-priority relation is locally bi-unique. -/
theorem finitePriorityEdgesAt_biUnique
    (E : Set (V × V)) (Q : FiniteTrace Gamma.graph) (T : Set V)
    (hE : Relator.BiUnique (fun x y ↦ (x, y) ∈ E)) :
    Relator.BiUnique
      (fun x y ↦ (x, y) ∈ finitePriorityEdgesAt E Q T) := by
  apply stopAt_biUnique T
  apply priorityEdges_biUnique hE
  exact Alternating.AltPath.forwardEdges_biUnique (AltPath.finite Q)

/-- The priority relation uses only ambient graph edges. -/
theorem finitePriorityEdgesAt_subset_adj
    (E : Set (V × V)) (Q : FiniteTrace Gamma.graph) (T : Set V)
    (hE : E ⊆ {e | Gamma.graph.Adj e.1 e.2}) :
    finitePriorityEdgesAt E Q T ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  rcases finitePriorityEdgesAt_subset_union E Q T he with he | he
  · exact hE he
  · exact (AltPath.finite Q).edgeSet_subset_adj
      (directionEdges_subset_edgeSet (AltPath.finite Q) .forward he)

/-- The stopping boundary has no outgoing priority edge. -/
theorem boundary_noOutgoing_finitePriorityEdgesAt
    (E : Set (V × V)) (Q : FiniteTrace Gamma.graph) (T : Set V)
    {t : V} (ht : t ∈ T) :
    ¬ HasOutgoing (finitePriorityEdgesAt E Q T) t := by
  rintro ⟨y, hty⟩
  exact hty.2 ht

/-- Hence the stopping boundary is a reachability antichain. -/
theorem finitePriorityEdgesAt_reachabilityAntichain
    (E : Set (V × V)) (Q : FiniteTrace Gamma.graph) (T : Set V) :
    GroundingRootedReachabilityWarp.IsReachabilityAntichain
      (finitePriorityEdgesAt E Q T) T := by
  intro b hb c _hc hbc
  exact GroundingBlockingReachability.eq_of_reflTransGen_of_noOutgoing
    (boundary_noOutgoing_finitePriorityEdgesAt E Q T hb) hbc

end GroundingFinitePriorityRelation
end Erdos599

#print axioms Erdos599.GroundingFinitePriorityRelation.finitePriorityEdgesAt_biUnique
#print axioms Erdos599.GroundingFinitePriorityRelation.finitePriorityEdgesAt_subset_adj
#print axioms
  Erdos599.GroundingFinitePriorityRelation.finitePriorityEdgesAt_reachabilityAntichain
