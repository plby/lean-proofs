/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingRawRequestWords

/-!
# Genuine roots and the first rootedness crossing in the raw relation

Every restored source prefix and its first attachment edge survive stopping
at the actual source-first separator. A request which is not rooted must
therefore have a forward stopping contact or a backward reference crossing.
This records an exact remaining obstruction, not an assumed rooting theorem.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath Alternating PopularAuxiliary.Input

universe u

namespace PopularAuxiliary.Input.RunsFromTo

/-- A finite signed traversal leaving a predicate has a step leaving it. -/
theorem exists_predicate_exit {V : Type u} {a b : V} {q : List (SignedEdge V)}
    (h : RunsFromTo a b q) {P : V → Prop} (ha : P a) (hb : ¬ P b) :
    ∃ s ∈ q, P s.entry ∧ ¬ P s.exit := by
  classical
  induction h with
  | nil => exact (hb ha).elim
  | cons s h ih =>
      by_cases hs : P s.exit
      · obtain ⟨t, ht, htP, htNot⟩ := ih hs hb
        exact ⟨t, List.mem_cons_of_mem s ht, htP, htNot⟩
      · exact ⟨s, List.mem_cons_self, ha, hs⟩

end PopularAuxiliary.Input.RunsFromTo

namespace DWeb.KappaLadder.Deferred

open PopularGroundingBridge GroundingSimultaneousDecode

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal
local notation "T" => reservedStrongSelectedSourceFirstBB (L := L) (hL := hL) (S := S)
local notation "ES" => reservedRawStoppedEdges (L := L) (hL := hL) (S := S) T

/-- Rootedness uses the stopped raw relation, not the full relation. -/
def reservedRawSourceRooted (x : V) : Prop :=
  ∃ a ∈ Gamma.source, Relation.ReflTransGen (fun u v ↦ (u, v) ∈ ES) a x

theorem reservedRawSourceRooted_of_source {x : V} (hx : x ∈ Gamma.source) :
    reservedRawSourceRooted (L := L) (hL := hL) (S := S) x :=
  ⟨x, hx, .refl⟩

theorem reservedRawSourceRooted_step {x y : V}
    (hx : reservedRawSourceRooted (L := L) (hL := hL) (S := S) x)
    (hxy : (x, y) ∈ ES) :
    reservedRawSourceRooted (L := L) (hL := hL) (S := S) y := by
  obtain ⟨a, ha, hax⟩ := hx
  exact ⟨a, ha, hax.tail hxy⟩

theorem reservedRawPrefix_disjoint_sourceFirst (r : Request J S.cut) :
    Disjoint T (reservedRawOwnerAttachment r).sourcePrefix.support :=
  (reservedRawOwnerAttachment_prefix_grounded_and_avoids r).2.mono_left
    reservedStrongSelectedSourceFirstBB_subset_relevantBB

theorem reservedRawPrefix_edges_subset_stopped (r : Request J S.cut) :
    (reservedRawOwnerAttachment r).sourcePrefix.edgeSet ⊆ ES := by
  intro e he
  exact ⟨reservedRawSimultaneousEdges_contains_prefix r he,
    fun hxT ↦ Set.disjoint_left.1 (reservedRawPrefix_disjoint_sourceFirst r) hxT
      ((reservedRawOwnerAttachment r).sourcePrefix.edgeSet_subset_support_prod he).1⟩

/-- All vertices of the actual restored finite prefix are stopped roots. -/
theorem reservedRawPrefix_sourceRooted (r : Request J S.cut) {x : V}
    (hx : x ∈ (reservedRawOwnerAttachment r).sourcePrefix.support) :
    reservedRawSourceRooted (L := L) (hL := hL) (S := S) x :=
  ⟨(reservedRawOwnerAttachment r).sourcePrefix.start,
    (reservedRawOwnerAttachment_prefix_grounded_and_avoids r).1,
    GroundingRootedReachabilityWarp.finitePath_start_reaches_of_mem_support
      (reservedRawOwnerAttachment r).sourcePrefix
      (reservedRawPrefix_edges_subset_stopped r) hx⟩

theorem reservedRawAnchor_sourceRooted (r : Request J S.cut) :
    reservedRawSourceRooted (L := L) (hL := hL) (S := S)
      (reservedRawOwnerAttachment r).anchor := by
  apply reservedRawPrefix_sourceRooted r
  rw [← (reservedRawOwnerAttachment r).sourcePrefix_finish]
  exact (reservedRawOwnerAttachment r).sourcePrefix.finish_mem_support

theorem reservedRawAnchor_not_sourceFirst (r : Request J S.cut) :
    (reservedRawOwnerAttachment r).anchor ∉ T := by
  intro hxT
  apply Set.disjoint_left.1 (reservedRawPrefix_disjoint_sourceFirst r) hxT
  rw [← (reservedRawOwnerAttachment r).sourcePrefix_finish]
  exact (reservedRawOwnerAttachment r).sourcePrefix.finish_mem_support

theorem reservedRawAttachment_mem_stopped (r : Request J S.cut) :
    ((reservedRawOwnerAttachment r).anchor,
      (reservedRawOwnerAttachment r).nextVertex) ∈ ES :=
  ⟨reservedRawSimultaneousEdges_contains_forward r (Or.inl rfl),
    reservedRawAnchor_not_sourceFirst r⟩

theorem reservedRawNext_sourceRooted (r : Request J S.cut) :
    reservedRawSourceRooted (L := L) (hL := hL) (S := S)
      (reservedRawOwnerAttachment r).nextVertex :=
  reservedRawSourceRooted_step (reservedRawAnchor_sourceRooted r)
    (reservedRawAttachment_mem_stopped r)

/-- Failure of request rooting has a literal crossing in its actual word:
either a forward edge leaves the stopping set, or a backward reference
step leaves the source-rooted region. No alternative is discarded here. -/
theorem reservedRawRequest_not_rooted_obstruction (r : Request J S.cut)
    (hr : ¬ reservedRawSourceRooted (L := L) (hL := hL) (S := S) (requestVertex r)) :
    (∃ e ∈ (reservedRawOwnerAttachment r).forwardEdges,
      e.1 ∈ T ∧ reservedRawSourceRooted (L := L) (hL := hL) (S := S) e.1 ∧
        ¬ reservedRawSourceRooted (L := L) (hL := hL) (S := S) e.2) ∨
    (∃ e ∈ reservedRawRequestBackwardEdges r,
      reservedRawSourceRooted (L := L) (hL := hL) (S := S) e.2 ∧
        ¬ reservedRawSourceRooted (L := L) (hL := hL) (S := S) e.1) := by
  classical
  obtain ⟨s, hs, hentry, hexit⟩ := (reservedRawRequestSteps_runs r).exists_predicate_exit
    (reservedRawAnchor_sourceRooted r) hr
  cases hd : s.direction with
  | forward =>
      have he : s.edge ∈ (reservedRawOwnerAttachment r).forwardEdges := by
        rw [← reservedRawRequestSteps_forwardEdges]
        exact ⟨s, hs, hd, rfl⟩
      have hroot : reservedRawSourceRooted (L := L) (hL := hL) (S := S) s.edge.1 := by
        simpa only [SignedEdge.entry, hd] using hentry
      have hnot : ¬ reservedRawSourceRooted (L := L) (hL := hL) (S := S) s.edge.2 := by
        simpa only [SignedEdge.exit, hd] using hexit
      have hT : s.edge.1 ∈ T := by
        by_contra hT
        exact hnot (reservedRawSourceRooted_step hroot
          ⟨reservedRawSimultaneousEdges_contains_forward r he, hT⟩)
      exact Or.inl ⟨s.edge, he, hT, hroot, hnot⟩
  | backward =>
      refine Or.inr ⟨s.edge, ⟨s, hs, hd, rfl⟩, ?_, ?_⟩
      · simpa only [SignedEdge.entry, hd] using hentry
      · simpa only [SignedEdge.exit, hd] using hexit

#print axioms reservedRawPrefix_sourceRooted
#print axioms reservedRawNext_sourceRooted
#print axioms reservedRawRequest_not_rooted_obstruction

end DWeb.KappaLadder.Deferred
end Erdos599
