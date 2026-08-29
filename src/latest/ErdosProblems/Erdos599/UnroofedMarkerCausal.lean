/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerPrefix
import ErdosProblems.Erdos599.UnroofedMarkerSmallness
import ErdosProblems.Erdos599.RegularRows

/-!
# Causal row interfaces for the unroofed-marker ladder

Every actual causal row rule supplies a fair preferred stream. Strict-prior
truncation gives exactly the final unroofed ladder through the current
accumulated stage, and every registered vertex enters its limit roof.
These statements do not identify old-ladder row registrations with new
ones; the row generators must still be instantiated with this protocol.
-/

noncomputable section

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Order Ladder KappaLadder
open CardinalInduction.RegularRows

universe u

variable {V : Type u} (G : DWeb V) {kappa : Cardinal.{u}}

def causalLadder (Q : CausalRowRule kappa V) (hkappa : aleph0 ≤ kappa) :
    G.KappaLadder kappa := ladder G kappa (Q.preferred hkappa)

def priorCausalLadder (Q : CausalRowRule kappa V) (hkappa : aleph0 ≤ kappa)
    (a : Stage kappa) : G.KappaLadder kappa :=
  ladder G kappa (Q.priorPreferred a (fun b _hba ↦ Q.state hkappa b))

theorem priorCausalLadder_warpAt (Q : CausalRowRule kappa V) (hkappa : aleph0 ≤ kappa)
    (a b : Stage kappa) (hba : b ≤ a) :
    (priorCausalLadder G Q hkappa a).warpAt b = (causalLadder G Q hkappa).warpAt b := by
  apply warpAt_eq_of_forall_lt
  intro c hc
  exact Q.priorPreferred_eq_preferred_of_lt hkappa (hc.trans_le hba)

theorem priorCausalLadder_frontier (Q : CausalRowRule kappa V) (hkappa : aleph0 ≤ kappa)
    (a b : Stage kappa) (hba : b ≤ a) :
    (priorCausalLadder G Q hkappa a).frontier b = (causalLadder G Q hkappa).frontier b := by
  apply frontier_eq_of_forall_lt
  intro c hc
  exact Q.priorPreferred_eq_preferred_of_lt hkappa (hc.trans_le hba)

theorem priorCausalLadder_stageWeb (Q : CausalRowRule kappa V) (hkappa : aleph0 ≤ kappa)
    (a b : Stage kappa) (hba : b ≤ a) :
    (priorCausalLadder G Q hkappa a).stageWeb b = (causalLadder G Q hkappa).stageWeb b := by
  apply stageWeb_eq_of_forall_lt
  intro c hc
  exact Q.priorPreferred_eq_preferred_of_lt hkappa (hc.trans_le hba)

theorem priorCausalLadder_successorWarp (Q : CausalRowRule kappa V) (hkappa : aleph0 ≤ kappa)
    (a b : Stage kappa) (hba : b < a) :
    (priorCausalLadder G Q hkappa a).successorWarp b =
      (causalLadder G Q hkappa).successorWarp b := by
  apply successorWarp_eq_of_forall_le
  intro c hc
  exact Q.priorPreferred_eq_preferred_of_lt hkappa (hc.trans_lt hba)

theorem priorCausalLadder_recordedBefore (Q : CausalRowRule kappa V) (hkappa : aleph0 ≤ kappa)
    (a : Stage kappa) :
    (priorCausalLadder G Q hkappa a).bookkeeping.recordedBefore a =
      (causalLadder G Q hkappa).bookkeeping.recordedBefore a := by
  apply recordedBefore_eq_of_forall_lt
  intro b hb
  exact Q.priorPreferred_eq_preferred_of_lt hkappa hb

theorem preferred_mem_limitRoof (preferred : Stage kappa → Option V)
    (hNoEnter : G.NoEdgeEnters G.source) (hkappa : aleph0 ≤ kappa)
    {a : Stage kappa} {y : V} (hy : preferred a = some y) :
    y ∈ (ladder G kappa preferred).limitRoof := by
  let b : Stage kappa := ⟨a.1 + 1, (Cardinal.isSuccLimit_ord hkappa).succ_lt a.2⟩
  have hrequest : extendLadderPreference kappa preferred a.1 = some y := by
    simpa only [extendLadderPreference_stage] using hy
  have hroof := preferred_mem_successorRoof G (extendLadderPreference kappa preferred) hrequest
  apply Set.mem_iUnion.mpr
  refine ⟨b, ?_⟩
  rw [(ladder G kappa preferred).frontier_eq_essential_terminalFrontier
    (ladder_geometry G kappa preferred hNoEnter).roofsSourceAtStages, G.roof_essential]
  exact hroof

theorem causalCarrier_subset_limitRoof (Q : CausalRowRule kappa V)
    (hNoEnter : G.NoEdgeEnters G.source) (hkappa : kappa.IsRegular)
    (huncountable : aleph0 < kappa) :
    (Q.rowSystem hkappa.aleph0_le).carrier ⊆ (causalLadder G Q hkappa.aleph0_le).limitRoof := by
  intro x hx
  obtain ⟨a, ha⟩ := Q.exists_preferred_eq_some_of_mem_carrier hkappa huncountable hx
  exact preferred_mem_limitRoof G (Q.preferred hkappa.aleph0_le) hNoEnter hkappa.aleph0_le ha

theorem causalLadder_exists_goodClub (Q : CausalRowRule kappa V)
    (hNoEnter : G.NoEdgeEnters G.source) (hkappa : kappa.IsRegular)
    (huncountable : aleph0 < kappa) (hNorm : G.IsNormalized) (hG : G.IsUnhindered) :
    ∃ C : Set (Stage kappa), Stationary.IsClubBelow kappa C ∧
      Disjoint C (causalLadder G Q hkappa.aleph0_le).phi ∧
      ∀ a ∈ C, ((causalLadder G Q hkappa.aleph0_le).stageWeb a).IsUnhindered :=
  exists_club_unhindered_stages G kappa (Q.preferred hkappa.aleph0_le)
    hNoEnter hkappa huncountable hNorm hG

#print axioms priorCausalLadder_warpAt
#print axioms priorCausalLadder_recordedBefore
#print axioms preferred_mem_limitRoof
#print axioms causalCarrier_subset_limitRoof
#print axioms causalLadder_exists_goodClub

end Erdos599.DWeb.UnroofedMarker
