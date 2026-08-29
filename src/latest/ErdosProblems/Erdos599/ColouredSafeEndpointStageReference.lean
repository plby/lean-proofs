/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointReference
import ErdosProblems.Erdos599.ColouredSafeReferenceLocalization

/-!
# Stage reference selected by its endpoint-pruned limiting owners

A stage prefix is retained exactly when its full limiting owner avoids the
displayed endpoints. The inherited embedding and one-point owner test give
roofed vertex and incoming-edge reflection. The whole stage subfamily is
not presumed to have finite character: untouched inessential rays may remain.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeEndpointStageReference

open Set Cardinal DirectedPath Alternating Ladder
open DWeb.KappaLadder.Deferred ColouredSafeEndpointReference

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa}

def stageReference (hL : HalfwayGeometry L) (a : Stage kappa) (s : V) (e : Option V) :
    Set Gamma.DPath :=
  {p | ∃ hp : p ∈ L.warpAt a, hL.limitOwner a ⟨p, hp⟩ ∈ reference L.limitWarp s e}

variable {hL : HalfwayGeometry L} {a : Stage kappa} {s : V} {e : Option V}

def stageMember (p : stageReference hL a s e) : L.warpAt a :=
  ⟨p.1, p.2.choose⟩

theorem stageReference_subset : stageReference hL a s e ⊆ L.warpAt a :=
  fun _ hp ↦ hp.choose

theorem stageReference_isWarp : Gamma.IsWarp (stageReference hL a s e) :=
  (hL.warpStages (Stage.toExtended a)).subset stageReference_subset

/-- The original owner map, restricted to the actual retained prefixes. -/
def embedding (hL : HalfwayGeometry L) (a : Stage kappa) (s : V) (e : Option V) :
    ReferenceSubpathEmbedding Gamma (stageReference hL a s e) (reference L.limitWarp s e) where
  owner p := ⟨hL.limitOwner a (stageMember p), p.2.choose_spec⟩
  owner_injective := by
    intro p q hpq
    have hlocal := hL.limitOwner_injective a
      (congrArg (fun r : reference L.limitWarp s e ↦ r.1) hpq)
    exact Subtype.ext (congrArg (fun r : L.warpAt a ↦ r.1) hlocal)
  support_subset p := Gamma.support_mono_of_extends (hL.extends_limitOwner a (stageMember p))
  edgeSet_subset p := Path.edgeSet_mono_of_extends (hL.extends_limitOwner a (stageMember p))
  global_isWarp := ColouredSafeEndpointReference.isWarp (hL.warpStages (finalStage kappa))

/-- A single contact identifies the original limiting owner, so the prefix
is retained whenever that owner is retained. -/
theorem mem_stageReference_of_common_vertex
    {p q : Gamma.DPath} (hp : p ∈ L.warpAt a) (hq : q ∈ reference L.limitWarp s e)
    {x : V} (hxp : x ∈ p.support) (hxq : x ∈ q.support) :
    p ∈ stageReference hL a s e := by
  have howner : hL.limitOwner a ⟨p, hp⟩ = q :=
    DWeb.IsWarp.eq_of_mem_support (hL.warpStages (finalStage kappa))
      (hL.limitOwner_mem a ⟨p, hp⟩) hq.1
      (Gamma.support_mono_of_extends (hL.extends_limitOwner a ⟨p, hp⟩) hxp) hxq
  exact ⟨hp, howner ▸ hq⟩

theorem vertexSet_reflect (hL : HalfwayGeometry L)
    {x : V} (hx : x ∈ Gamma.vertexSet (reference L.limitWarp s e))
    (hxRoof : x ∈ Gamma.roof (L.frontier a)) :
    x ∈ Gamma.vertexSet (stageReference hL a s e) := by
  obtain ⟨q, hq, hxq⟩ := hx
  obtain ⟨p, hp, hxp⟩ := ColouredSafeReferenceTransport.limitWarp_inter_roof_subset_warpAt
    hL ⟨⟨q, hq.1, hxq⟩, hxRoof⟩
  exact ⟨p, mem_stageReference_of_common_vertex hp hq hxp hxq, hxp⟩

theorem incoming_edge_reflect (hL : HalfwayGeometry L)
    {x y : V} (hxy : (x, y) ∈ familyEdges (reference L.limitWarp s e))
    (hyRoof : y ∈ Gamma.roof (L.frontier a)) :
    (x, y) ∈ familyEdges (stageReference hL a s e) := by
  have hglobal : (x, y) ∈ familyEdges L.limitWarp := by
    simp only [familyEdges, Set.mem_iUnion] at hxy ⊢
    obtain ⟨q, hq, hqe⟩ := hxy
    exact ⟨q, hq.1, hqe⟩
  have hlocal := ColouredSafeReferenceTransport.incoming_referenceEdge_reflect hL hglobal hyRoof
  simp only [familyEdges, Set.mem_iUnion] at hxy hlocal ⊢
  obtain ⟨q, hq, hqe⟩ := hxy
  obtain ⟨p, hp, hpe⟩ := hlocal
  exact ⟨p, mem_stageReference_of_common_vertex hp hq
    (p.edgeSet_subset_support_prod hpe).2 (q.edgeSet_subset_support_prod hqe).2, hpe⟩

theorem initialSet_subset : Gamma.initialSet (stageReference hL a s e) ⊆
    Gamma.initialSet (reference L.limitWarp s e) := by
  rintro x ⟨p, hp, hpx⟩
  let q : stageReference hL a s e := ⟨p, hp⟩
  exact ⟨hL.limitOwner a (stageMember q), hp.choose_spec,
    (Gamma.extends_initial (hL.extends_limitOwner a (stageMember q))).symm.trans hpx⟩

/-- The no-late-entry property still holds after deleting whole limiting
owners: a retained edge with roofed head has a roofed tail. -/
theorem edge_tail_roof_of_head_roof (hL : HalfwayGeometry L)
    {x y : V} (hxy : (x, y) ∈ familyEdges (reference L.limitWarp s e))
    (hyRoof : y ∈ Gamma.roof (L.frontier a)) :
    x ∈ Gamma.roof (L.frontier a) := by
  have hstage := incoming_edge_reflect hL hxy hyRoof
  have hfull : (x, y) ∈ Gamma.pathFamilyEdgeSet (L.warpAt a) := by
    simp only [familyEdges, Set.mem_iUnion] at hstage
    obtain ⟨p, hp, hep⟩ := hstage
    exact ⟨p, stageReference_subset hp, hep⟩
  have hxRaw := edge_tail_mem_strictRoof_of_mem_warpAt hL a hfull
  rw [L.frontier_eq_essential_terminalFrontier hL.roofsSourceAtStages,
    Gamma.roof_essential]
  exact hxRaw.1

theorem vertexSet_disjoint_endpoints :
    Disjoint (Gamma.vertexSet (stageReference hL a s e)) (ColouredSafeHammock.endpoints s e) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨p, hp, hxp⟩ hx
  let E := embedding hL a s e
  exact Set.disjoint_left.mp ColouredSafeEndpointReference.vertexSet_disjoint_endpoints
    ⟨(E.owner ⟨p, hp⟩).1, (E.owner ⟨p, hp⟩).2, E.support_subset ⟨p, hp⟩ hxp⟩ hx

/-- Once all removed edges are local, global contact removal rules out
a forward edge leaving a new local terminal. -/
theorem endpointPure_local_of_removed_edges_local
    {F R : Set (V × V)}
    (hR : R ⊆ familyEdges (stageReference hL a s e))
    (hout : ∀ {x y z}, (x, y) ∈ F →
      (x, z) ∈ familyEdges (reference L.limitWarp s e) → (x, z) ∈ R)
    (hpure : ∀ {x y}, (x, y) ∈ F →
      y ∉ Gamma.initialSet (reference L.limitWarp s e) ∧
      x ∉ Gamma.terminalFrontier (reference L.limitWarp s e)) :
    ∀ {x y}, (x, y) ∈ F → y ∉ Gamma.initialSet (stageReference hL a s e) ∧
      x ∉ Gamma.terminalFrontier (stageReference hL a s e) := by
  intro x y hxy
  refine ⟨fun hy ↦ (hpure hxy).1 (initialSet_subset hy), ?_⟩
  intro hx
  have hlocal := hx
  rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp
    stageReference_isWarp] at hlocal
  have hxGlobal : x ∈ Gamma.vertexSet (reference L.limitWarp s e) := by
    obtain ⟨p, hp, hxp⟩ := hlocal.1
    let E := embedding hL a s e
    exact ⟨(E.owner ⟨p, hp⟩).1, (E.owner ⟨p, hp⟩).2,
      E.support_subset ⟨p, hp⟩ hxp⟩
  have hglobalOut : ∃ y, (x, y) ∈ familyEdges (reference L.limitWarp s e) := by
    by_contra hno
    apply (hpure hxy).2
    rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp
      (embedding hL a s e).global_isWarp]
    exact ⟨hxGlobal, hno⟩
  obtain ⟨z, hxz⟩ := hglobalOut
  exact hlocal.2 ⟨z, hR (hout hxy hxz)⟩

#print axioms embedding
#print axioms incoming_edge_reflect
#print axioms endpointPure_local_of_removed_edges_local

end Erdos599.Blueprint.ColouredSafeEndpointStageReference
