/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingCarrierRouteAvoidance
import ErdosProblems.Erdos599.GroundingAvoidingControls

/-!
# Avoiding the cut-reachable part of off-apex reference owners

The carrier of an owner consists of vertices with an internal auxiliary
route to the cut. Suffixes keep every witnessing route inside this carrier.
Countability and disjointness come from the actual reference traces.
This treats cut-preceded fragments of grounded parents as well as hanging
parents and includes contacts at edge gadgets, not just old vertices.
-/

noncomputable section

namespace Erdos599.GroundingCutReachableOwnerAvoidance

open Set DirectedPath PopularGroundingBridge PopularAuxiliary.Input

universe u

variable {V I : Type u} {Gamma : DWeb V}
variable {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
variable {U : Popular.KappaIndexed L.lambda kappa}
variable (S : Popular.PopularSeparator U) (r : Request L S.cut)

/-- The cut-reachable part of one actual owner whose whole trace omits
the request apex. No inherited or intrinsic grounding assumption is used. -/
def ownerCarrier (Y : Gamma.DPath) : Set L.LV :=
  {z | Y ∈ L.ladder.paths ∧ requestAuxVertex r ∉ PopularSwitching.ladderTrace L Y ∧
    ∃ q : FinitePath L.lambda.graph,
      q.start = z ∧ q.finish ∈ S.cut ∧ q.support ⊆ PopularSwitching.ladderTrace L Y}

theorem ownerCarrier_subset_trace (Y : Gamma.DPath) :
    ownerCarrier S r Y ⊆ PopularSwitching.ladderTrace L Y := by
  rintro z ⟨_hY, _hapex, q, hs, _hf, hq⟩
  exact hs ▸ hq q.start_mem_support

theorem ownerCarrier_countable (Y : Gamma.DPath) :
    (ownerCarrier S r Y).Countable :=
  (PopularSwitching.ladderTrace_countable L Y).mono (ownerCarrier_subset_trace S r Y)

theorem ownerCarrier_disjoint_apex (Y : Gamma.DPath) :
    Disjoint (ownerCarrier S r Y) {requestAuxVertex r} := by
  apply Set.disjoint_left.2
  intro z hz hzApex
  have heq := Set.mem_singleton_iff.mp hzApex
  exact hz.2.1 (heq ▸ ownerCarrier_subset_trace S r Y hz)

theorem ownerCarrier_pairwise_disjoint :
    Pairwise (fun Y Z ↦ Disjoint (ownerCarrier S r Y) (ownerCarrier S r Z)) := by
  intro Y Z hne
  apply Set.disjoint_left.2
  intro z hzY hzZ
  exact Set.disjoint_left.1
    (GroundingFragmentCarrier.ladderTrace_disjoint_of_ne L hzY.1 hzZ.1 hne)
    (ownerCarrier_subset_trace S r Y hzY) (ownerCarrier_subset_trace S r Z hzZ)

/-- Taking suffixes keeps each witness inside the cut-reachable carrier. -/
theorem exists_internal_route (Y : Gamma.DPath) (z : L.LV)
    (hz : z ∈ ownerCarrier S r Y) :
    ∃ q : FinitePath L.lambda.graph,
      q.start = z ∧ q.finish ∈ S.cut ∧ q.support ⊆ ownerCarrier S r Y := by
  obtain ⟨hY, hapex, q, hs, hf, hq⟩ := hz
  refine ⟨q, hs, hf, ?_⟩
  intro x hx
  refine ⟨hY, hapex, q.suffixFrom x hx, q.suffixFrom_start x hx, ?_, ?_⟩
  · rw [q.suffixFrom_finish x hx]
    exact hf
  · exact (q.suffixFrom_support_subset x hx).trans hq

def carrier : Set L.LV := ⋃ Y, ownerCarrier S r Y

def collidingPaths : Set (FinitePath L.lambda.graph) :=
  GroundingAvoidingControls.meetsCarrier (carrier S r)

/-- The actual exception class has nonstationary indices, by an explicit
disjoint source--cut splice construction. -/
theorem collidingPaths_indices_nonstationary :
    ¬ Stationary.IsStationaryBelow kappa
      (GroundingSelection.restrictedIndices U (requestFan S r) (collidingPaths S r)) :=
  Popular.initialIndices_nonstationary_of_carrier_routes U S (requestFan S r)
    (ownerCarrier S r) (ownerCarrier_countable S r) (ownerCarrier_disjoint_apex S r)
    (ownerCarrier_pairwise_disjoint S r) (exists_internal_route S r)

/-- Every edge gadget in a cut-preceded surviving fragment belongs to the
carrier whenever its parent trace avoids the request apex. -/
theorem edge_mem_carrier_of_cutPredecessor
    (P : L.Fragment) (hP : P ∈ GroundingCut.fragments L S.cut)
    (hapex : requestAuxVertex r ∉ PopularSwitching.ladderTrace L P.parent)
    {s e : V × V} (hsC : s ∈ GroundingCut.CE L S.cut)
    (hsParent : s ∈ P.parent.edgeSet) (hsHead : s.2 = P.path.initial)
    (heP : e ∈ P.path.edgeSet) :
    LambdaVertex.edge e.1 e.2 ∈ carrier S r := by
  obtain ⟨q, hstart, hfinish, hsupport⟩ :=
    GroundingFragmentWarp.exists_edge_path_to_cutPredecessor L S.cut
      hP hsC hsParent hsHead heP
  apply Set.mem_iUnion.2
  refine ⟨P.parent, P.parent_mem, hapex, q, hstart, ?_, ?_⟩
  · rw [hfinish]
    exact hsC.1
  · intro z hz
    obtain ⟨f, hf, rfl⟩ := hsupport hz
    apply (PopularSwitching.edge_mem_ladderTrace_iff L P.parent f.1 f.2).2
    rcases Set.mem_insert_iff.mp hf with rfl | hf
    · exact hsParent
    · exact P.edges_subset hf

/-- The same carrier also contains every old vertex of that fragment. -/
theorem old_mem_carrier_of_cutPredecessor
    (P : L.Fragment) (hP : P ∈ GroundingCut.fragments L S.cut)
    (hapex : requestAuxVertex r ∉ PopularSwitching.ladderTrace L P.parent)
    {s : V × V} (hsC : s ∈ GroundingCut.CE L S.cut)
    (hsParent : s ∈ P.parent.edgeSet) (hsHead : s.2 = P.path.initial)
    {x : V} (hx : x ∈ P.path.support) : LambdaVertex.old x ∈ carrier S r := by
  obtain ⟨q, hstart, hfinish, hsupport⟩ :=
    GroundingFragmentWarp.exists_path_to_cutPredecessor L S.cut
      hP hsC hsParent hsHead hx
  apply Set.mem_iUnion.2
  refine ⟨P.parent, P.parent_mem, hapex, q, hstart, ?_, ?_⟩
  · rw [hfinish]
    exact hsC.1
  · intro z hz
    rcases hsupport hz with hz | hz
    · rcases Set.mem_singleton_iff.mp hz with rfl
      exact (PopularSwitching.old_mem_ladderTrace_iff L P.parent x).2 (P.support_subset hx)
    · obtain ⟨f, hf, rfl⟩ := hz
      apply (PopularSwitching.edge_mem_ladderTrace_iff L P.parent f.1 f.2).2
      rcases Set.mem_insert_iff.mp hf with rfl | hf
      · exact hsParent
      · exact P.edges_subset hf

#print axioms collidingPaths_indices_nonstationary
#print axioms edge_mem_carrier_of_cutPredecessor
#print axioms old_mem_carrier_of_cutPredecessor

end Erdos599.GroundingCutReachableOwnerAvoidance
