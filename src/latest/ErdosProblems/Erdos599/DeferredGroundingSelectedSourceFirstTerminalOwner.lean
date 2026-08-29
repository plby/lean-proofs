/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingSelectedSourceFirstOwner

/-!
# Terminal source-first owner restorations are literal no-ops

The finite-record and essential-terminal branches of the deferred
source-first owner classification end at the actual terminal of the
sacrificed limiting component.  In those two branches the maximal restoring
prefix is therefore the whole finite component.  Replacing the owner by that
prefix changes neither the truncated warp nor its edge relation.

This removes a genuine case from the simultaneous exchange: terminal-owner
restoration needs no compatibility or matching choice.  The remaining
competition is confined to an interior source-first point (old request or
virtual escape).
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DirectedPath
open Alternating PopularAuxiliary.Input
open PopularGroundingBridge GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal

namespace ReservedStrongSelectedStartingLastContact.SourceSaturation

/-- Two initial finite subpaths of one limiting component with the same
endpoint are equal.  This local form is used to identify a maximal restoring
prefix with its whole finite owner. -/
private theorem initialSubpath_eq_of_finish_eq
    (P : Gamma.DPath) (p q : FinitePath Gamma.graph)
    (hpStart : p.start = P.initial) (hqStart : q.start = P.initial)
    (hpEdges : p.edgeSet ⊆ P.edgeSet)
    (hqEdges : q.edgeSet ⊆ P.edgeSet)
    (hfinish : p.finish = q.finish) :
    p = q := by
  have hpOccurs :=
    initialSubpath_finish_occursAt_length P p hpStart hpEdges
  have hqOccurs :=
    initialSubpath_finish_occursAt_length P q hqStart hqEdges
  have hpOccurs' : GroundingCut.OccursAt P p.walk.length q.finish := by
    simpa only [hfinish] using hpOccurs
  have hlength : p.walk.length = q.walk.length :=
    GroundingCutDecoder.occursAt_index_injective hpOccurs' hqOccurs
  have hpq : p.IsPrefixOf q :=
    initialSubpath_isPrefixOf_of_length_le P p q
      hpStart hqStart hpEdges hqEdges hlength.le
  have hqp : q.IsPrefixOf p :=
    initialSubpath_isPrefixOf_of_length_le P q p
      hqStart hpStart hqEdges hpEdges hlength.ge
  apply FinitePath.eq_of_start_finish_edgeSet_eq p q
  · exact hpStart.trans hqStart.symm
  · exact hfinish
  · apply Set.Subset.antisymm
    · exact p.walk.edgeSet_subset_of_support_prefix q.walk hpq
    · exact q.walk.edgeSet_subset_of_support_prefix p.walk hqp

/-- If the maximal required source-first point is the terminal of the
sacrificed owner, the displayed restoring prefix is literally that whole
owner. -/
theorem LastSourceFirstPrefix.sourcePrefix_eq_owner_of_terminal
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D)
    (hterminal : Gamma.terminal? D.owner = some F.boundary) :
    (Sum.inl F.sourcePrefix : Gamma.DPath) = D.owner := by
  cases howner : D.owner with
  | inl p =>
      apply congrArg Sum.inl
      apply initialSubpath_eq_of_finish_eq D.owner F.sourcePrefix p
      · exact F.sourcePrefix_start
      · rw [howner]
        rfl
      · exact F.sourcePrefix_edges
      · rw [howner]
        exact Set.Subset.rfl
      · have hterminal' := hterminal
        rw [howner] at hterminal'
        change some p.finish = some F.boundary at hterminal'
        exact F.sourcePrefix_finish.trans (Option.some.inj hterminal').symm
  | inr ray =>
      rw [howner] at hterminal
      change (none : Option V) = some F.boundary at hterminal
      cases hterminal

/-- Consequently terminal-owner restoration is exactly the original
truncated reference warp. -/
theorem LastSourceFirstPrefix.restoredWarp_eq_truncatedWarp_of_terminal
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D)
    (hterminal : Gamma.terminal? D.owner = some F.boundary) :
    F.restoredWarp = X.truncatedWarp := by
  rw [LastSourceFirstPrefix.restoredWarp,
    F.sourcePrefix_eq_owner_of_terminal hterminal]
  ext p
  simp only [Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · rintro (rfl | ⟨hp, _hne⟩)
    · exact D.owner_mem
    · exact hp
  · intro hp
    by_cases hEq : p = D.owner
    · exact Or.inl hEq
    · exact Or.inr ⟨hp, hEq⟩

/-- In the terminal-owner cases the unchanged truncated warp already roots
every required source-first point on that owner. -/
theorem LastSourceFirstPrefix.truncatedWarp_roots_owner_boundaries_of_terminal
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D)
    (hterminal : Gamma.terminal? D.owner = some F.boundary)
    {z : V}
    (hz : z ∈ reservedStrongSelectedSourceFirstBB
      (L := L) (hL := hL) (S := S))
    (hzOwner : z ∈ D.owner.support) :
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ Alternating.familyEdges X.truncatedWarp) a z := by
  obtain ⟨a, ha, hreach⟩ := F.restoredWarp_roots_owner_boundaries hz hzOwner
  refine ⟨a, ha, ?_⟩
  rw [F.restoredWarp_eq_truncatedWarp_of_terminal hterminal] at hreach
  exact hreach

end ReservedStrongSelectedStartingLastContact.SourceSaturation

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.LastSourceFirstPrefix.sourcePrefix_eq_owner_of_terminal
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.LastSourceFirstPrefix.restoredWarp_eq_truncatedWarp_of_terminal
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.LastSourceFirstPrefix.truncatedWarp_roots_owner_boundaries_of_terminal
