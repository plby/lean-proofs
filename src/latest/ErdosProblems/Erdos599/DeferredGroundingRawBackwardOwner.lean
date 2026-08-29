/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingRawRootSeeds

/-!
# Unique request ownership of non-cut backward changes

An earlier backward gadget exposes its whole reference owner. A later
non-cut backward gadget on that owner would violate the actual strong
selection rule. This does not assume that the whole owner avoids the cut.
-/

noncomputable section

namespace Erdos599.DWeb.KappaLadder.Deferred

open Set _root_.Erdos599.DirectedPath Alternating
open PopularAuxiliary.Input PopularGroundingBridge GroundingSimultaneousDecode
open GroundingRawSelectedEdgeSwitch

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal
local notation "U" => popularAuxiliaryIndexed L hL
local notation "K" => reservedGroundedCarrierControls L hL S

/-- The only extra backward gadget in the full suffix is already cut. -/
theorem reservedRawRequestBackward_eq_tail_diff_cut (r : Request J S.cut) :
    reservedRawRequestBackwardEdges r =
      (J).representedEdges (reservedRawOwnerAttachment r).tail \ GroundingCut.CE J S.cut := by
  apply Set.Subset.antisymm
  · intro e he
    exact ⟨reservedRawRequestBackward_subset_tail r he,
      (reservedRawRequestBackward_subset_cut_reference r he).2⟩
  · intro e he
    cases r with
    | inl z =>
        change e ∈ directedSignedEdgeSet .backward (reservedRawOwnerAttachment (.inl z)).steps
        rw [(reservedRawOwnerAttachment (.inl z)).steps_backwardEdges
          ((strongSelectedWarp U S K).starts_in_source ⟨.inl z, rfl⟩)]
        exact he.1
    | inr f =>
        have hpart := (reservedRawOwnerAttachment (.inr f)).entrySteps_backward_partition
          ((strongSelectedWarp U S K).starts_in_source ⟨.inr f, rfl⟩) f.1.1 f.1.2
          (strongSelectedPath_finish U S K (.inr f))
        have hmem := he.1
        rw [hpart] at hmem
        rcases hmem with hword | hfinal
        · exact hword
        · exact (he.2 ((Set.mem_singleton_iff.1 hfinal).symm ▸
            selectedEdge_mem_CE U S K f)).elim

/-- After cut deletion the global backward relation consists exactly of
the backward steps in the request words. -/
theorem reservedRawBackward_diff_cut :
    reservedRawBackwardEdges (L := L) (hL := hL) (S := S) \ GroundingCut.CE J S.cut =
      ⋃ r : Request J S.cut, reservedRawRequestBackwardEdges r := by
  ext e
  constructor
  · rintro ⟨hback, hcut⟩
    obtain ⟨r, hr⟩ := Set.mem_iUnion.1 hback
    apply Set.mem_iUnion.2
    refine ⟨r, ?_⟩
    rw [reservedRawRequestBackward_eq_tail_diff_cut]
    exact ⟨hr, hcut⟩
  · intro he
    obtain ⟨r, hr⟩ := Set.mem_iUnion.1 he
    rw [reservedRawRequestBackward_eq_tail_diff_cut] at hr
    exact ⟨Set.mem_iUnion.2 ⟨r, hr.1⟩, hr.2⟩

theorem reservedRawRequestBackward_owner_exposed
    (r : Request J S.cut) {Y : Gamma.DPath} (hY : Y ∈ (J).ladder.paths)
    {e : V × V} (he : e ∈ reservedRawRequestBackwardEdges r) (heY : e ∈ Y.edgeSet) :
    Y ∈ exposedLadderPaths J (strongSelectedPath U S K r) :=
  Or.inl ⟨hY, LambdaVertex.edge e.1 e.2, (reservedRawRequestBackward_gadget r he).1,
    (PopularSwitching.edge_mem_ladderTrace_iff J Y e.1 e.2).2 heY⟩

/-- A reference component exposed earlier has no later non-cut backward change. -/
theorem reservedRawRequestBackward_not_on_earlier_exposed
    (r s : Request J S.cut)
    (hrs : GroundingAssembly.requestRank U S r < GroundingAssembly.requestRank U S s)
    {Y : Gamma.DPath} (hY : Y ∈ exposedLadderPaths J (strongSelectedPath U S K r))
    {e : V × V} (he : e ∈ reservedRawRequestBackwardEdges s) (heY : e ∈ Y.edgeSet) :
    False := by
  have hgate := reservedRawRequestBackward_gadget s he
  have hmet : LambdaVertex.edge e.1 e.2 ∈
      GroundingSimultaneousDecode.metLadderTrace J (strongSelectedPath U S K r) :=
    (mem_metLadderTrace_iff J _ _).2
      ⟨Y, hY, (PopularSwitching.edge_mem_ladderTrace_iff J Y e.1 e.2).2 heY⟩
  have hne : LambdaVertex.edge e.1 e.2 ≠ requestAuxVertex s :=
    fun h ↦ hgate.2 (h.symm ▸ requestAuxVertex_mem_cut s)
  exact Set.disjoint_left.1 (strongSelectedPath_avoids_earlier_components U S K r s hrs)
    hgate.1 ⟨hmet, by simpa using hne⟩

/-- All actual backward changes on one reference owner belong to one request. -/
theorem reservedRawRequestBackward_owner_unique
    (r s : Request J S.cut) {Y : Gamma.DPath} (hY : Y ∈ (J).ladder.paths)
    {e f : V × V} (he : e ∈ reservedRawRequestBackwardEdges r) (heY : e ∈ Y.edgeSet)
    (hf : f ∈ reservedRawRequestBackwardEdges s) (hfY : f ∈ Y.edgeSet) : r = s := by
  rcases lt_trichotomy (GroundingAssembly.requestRank U S r)
      (GroundingAssembly.requestRank U S s) with hlt | heq | hgt
  · exact (reservedRawRequestBackward_not_on_earlier_exposed r s hlt
      (reservedRawRequestBackward_owner_exposed r hY he heY) hf hfY).elim
  · exact (GroundingAssembly.requestRank U S).injective heq
  · exact (reservedRawRequestBackward_not_on_earlier_exposed s r hgt
      (reservedRawRequestBackward_owner_exposed s hY hf hfY) he heY).elim

/-- An owner with an actual backward change is not any selected starting
record, including the record belonging to its own request. -/
theorem reservedRawRequestBackward_owner_ne_startingRecord
    (r s : Request J S.cut) {Y : Gamma.DPath} (hY : Y ∈ (J).ladder.paths)
    {e : V × V} (he : e ∈ reservedRawRequestBackwardEdges r) (heY : e ∈ Y.edgeSet) :
    Y ≠ (reservedStrongSelectedStartingRecord s).record := by
  classical
  intro hsame
  by_cases hrs : r = s
  · subst s
    exact (reservedRawRequestBackward_subset_cut_reference r he).1.2 (hsame ▸ heY)
  · exact reservedRawOwner_record_not_exposed_other s r (fun h ↦ hrs h.symm)
      (hsame ▸ reservedRawRequestBackward_owner_exposed r hY he heY)

/-- On a backward-changed owner, the retained reference relation removes
exactly the cut edges and the backward steps of that single request. -/
theorem reservedRawRetained_on_backwardOwner_iff
    (r : Request J S.cut) {Y : Gamma.DPath} (hY : Y ∈ (J).ladder.paths)
    {e : V × V} (he : e ∈ reservedRawRequestBackwardEdges r) (heY : e ∈ Y.edgeSet)
    {f : V × V} (hfY : f ∈ Y.edgeSet) :
    f ∈ reservedRawRetainedEdges (L := L) (hL := hL) (S := S) ↔
      f ∉ GroundingCut.CE J S.cut ∧ f ∉ reservedRawRequestBackwardEdges r := by
  constructor
  · intro hf
    exact ⟨hf.1.1.2, fun hback ↦ hf.2 (Set.mem_iUnion.2
      ⟨r, reservedRawRequestBackward_subset_tail r hback⟩)⟩
  · rintro ⟨hcut, hback⟩
    refine ⟨⟨⟨⟨Y, hY, hfY⟩, hcut⟩, ?_⟩, ?_⟩
    · intro howner
      obtain ⟨s, hs⟩ := Set.mem_iUnion.1 howner
      have hsame : Y = (reservedStrongSelectedStartingRecord s).record :=
        DWeb.IsWarp.eq_of_mem_support (J).ladder.disjoint hY
          (reservedStrongSelectedStartingRecord s).record_mem_ladder
          (Y.edgeSet_subset_support_prod hfY).1
          ((reservedStrongSelectedStartingRecord s).record.edgeSet_subset_support_prod hs).1
      exact reservedRawRequestBackward_owner_ne_startingRecord r s hY he heY hsame
    · intro hglobal
      obtain ⟨s, hs⟩ := Set.mem_iUnion.1 hglobal
      have hsBack : f ∈ reservedRawRequestBackwardEdges s := by
        rw [reservedRawRequestBackward_eq_tail_diff_cut]
        exact ⟨hs, hcut⟩
      have hrs := reservedRawRequestBackward_owner_unique r s hY he heY hsBack hfY
      exact hback (by simpa only [hrs] using hsBack)

#print axioms reservedRawRequestBackward_eq_tail_diff_cut
#print axioms reservedRawRequestBackward_owner_unique
#print axioms reservedRawRetained_on_backwardOwner_iff

end Erdos599.DWeb.KappaLadder.Deferred
