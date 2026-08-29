/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaRawEdgeEntrySwitch

/-!
# The actual strongly selected edge-request transaction

The selected fan proves all cut normalization hypotheses. For an ordinary
finite source, its raw head-stopping switch is biunique and has the exact
boundary relative to the actual cut-deleted ladder. It has a genuine
path/ray realization; no simultaneous grounding claim is made here.
-/

noncomputable section

namespace Erdos599
namespace GroundingRawSelectedEdgeSwitch

open Set DirectedPath Alternating Alternating.TerminalContactSwitch
open PopularAuxiliary.Input PopularGroundingBridge GroundingSimultaneousDecode

universe u

variable {V I : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : PopularAuxiliary.Input Gamma I}
variable (U : Popular.KappaIndexed L.lambda kappa)
variable (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)

/-- The actual raw, head-stopping relation for a selected edge request. -/
def selectedRawEdges (e : edgeRequests L S.cut) : Set (V × V) :=
  rawEdgeEntrySwitchedEdges (strongSelectedPath U S K (.inr e)) e.1.1 e.1.2
    (strongSelectedPath_finish U S K (.inr e)) (GroundingCut.CE L S.cut)

include K in
/-- The selected route makes its cut edge a genuine limiting reference
edge, even though requests were initially defined using only cut tags. -/
theorem selectedEdge_mem_CE (e : edgeRequests L S.cut) : e.1 ∈ GroundingCut.CE L S.cut := by
  refine ⟨e.2, ?_⟩
  let p := strongSelectedPath U S K (.inr e)
  have hs : p.start ∈ L.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source ⟨.inr e, rfl⟩
  have hfinish : p.finish = .edge e.1.1 e.1.2 :=
    strongSelectedPath_finish U S K (.inr e)
  apply L.edgeNode_mem_familyEdges_of_start_in_source p hs
  exact hfinish ▸ p.finish_mem_support

/-- The actual strong selection meets no other cut-edge gadget. -/
theorem selected_edgeCut_gadget_unique (e : edgeRequests L S.cut)
    (f : V × V) (hf : f ∈ GroundingCut.CE L S.cut)
    (hfp : LambdaVertex.edge f.1 f.2 ∈ (strongSelectedPath U S K (.inr e)).support) :
    f = e.1 := by
  have h := strongSelectedPath_cut_contact_eq_requestAuxVertex U S K (.inr e) hfp hf.1
  have hparts : f.1 = e.1.1 ∧ f.2 = e.1.2 := LambdaVertex.edge.inj h
  exact Prod.ext hparts.1 hparts.2

/-- All cut and incidence premises are discharged for the selected
ordinary-source branch, retaining its exact endpoint at the edge head. -/
theorem selectedRawEdges_biUnique_and_balance
    (hL : L.HasBoundaryIncidence) (e : edgeRequests L S.cut) {s : V}
    (hstart : (strongSelectedPath U S K (.inr e)).start = .old s) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ selectedRawEdges U S K e) ∧
    ∀ x, edgeBalance (selectedRawEdges U S K e) x =
      edgeBalance (L.familyEdges \ GroundingCut.CE L S.cut) x +
        propInt (x = s) - propInt (x = e.1.2) := by
  let p := strongSelectedPath U S K (.inr e)
  have hs : p.start ∈ L.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source ⟨.inr e, rfl⟩
  exact hL.rawEdgeEntrySwitch_biUnique_and_balance p hs hstart e.1.1 e.1.2
    (strongSelectedPath_finish U S K (.inr e)) (GroundingCut.CE L S.cut)
    (selectedEdge_mem_CE U S K e) (selected_edgeCut_gadget_unique U S K e)

/-- The complete actual selected raw relation has a path/ray realization
with exact edge accounting and boundary, after discarding whole cycles. -/
theorem exists_selectedRawEdgeSwitchWarp
    (hL : L.HasBoundaryIncidence) (e : edgeRequests L S.cut) {s : V}
    (hstart : (strongSelectedPath U S K (.inr e)).start = .old s) :
    ∃ W : Set Gamma.DPath,
      Gamma.IsWarp W ∧
      familyEdges W = selectedRawEdges U S K e \ cyclicEdges (selectedRawEdges U S K e) ∧
      isolatedVertices W = ∅ ∧
      ∀ x, edgeBalance (familyEdges W) x =
        edgeBalance (L.familyEdges \ GroundingCut.CE L S.cut) x +
          propInt (x = s) - propInt (x = e.1.2) := by
  let p := strongSelectedPath U S K (.inr e)
  have hs : p.start ∈ L.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source ⟨.inr e, rfl⟩
  have hsub : selectedRawEdges U S K e ⊆ L.rawSwitchedEdges p :=
    rawEdgeEntrySwitchedEdges_subset_raw p hs e.1.1 e.1.2
      (strongSelectedPath_finish U S K (.inr e)) (GroundingCut.CE L S.cut)
      (selectedEdge_mem_CE U S K e)
  have hgraph : selectedRawEdges U S K e ⊆ {f | Gamma.graph.Adj f.1 f.2} :=
    hsub.trans (L.rawSwitchedEdges_subset_adj p)
  have hreverse : ¬ ContainsReverseDirectedRay (selectedRawEdges U S K e) := by
    rintro ⟨r, hr⟩
    exact L.rawSwitchedEdges_not_containsReverseDirectedRay p
      ⟨r, fun n ↦ hsub (hr n)⟩
  obtain ⟨hbi, hbalance⟩ := selectedRawEdges_biUnique_and_balance U S K hL e hstart
  obtain ⟨W, hW, hWE, hWI, hbal⟩ :=
    GroundingFinitePerturbationRooting.exists_warp_with_edges_sdiff_cyclic
      (selectedRawEdges U S K e) hgraph hbi hreverse
  refine ⟨W, hW, hWE, hWI, ?_⟩
  intro x
  rw [hbal]
  exact hbalance x

end GroundingRawSelectedEdgeSwitch
end Erdos599

#print axioms Erdos599.GroundingRawSelectedEdgeSwitch.selectedRawEdges_biUnique_and_balance
#print axioms Erdos599.GroundingRawSelectedEdgeSwitch.exists_selectedRawEdgeSwitchWarp
