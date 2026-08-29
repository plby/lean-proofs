/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointStageReference

/-!
# The endpoint-pruned stage reference is causal after endpoint capture

Once every displayed endpoint is roofed, a full limiting owner avoids
the endpoints exactly when its stage prefix does. Thus the pruned stage
reference can be computed from the stage warp alone. The second part
proves the boundary and outgoing-incidence reflection needed to promote
native roof-supported occurrences in the reverse direction.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeEndpointStageReference

open Set Cardinal DirectedPath Alternating Ladder
open DWeb.KappaLadder.Deferred ColouredSafeEndpointReference

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {a : Stage kappa} {s : V} {e : Option V}

/-- A roofed point on the limiting owner already lies on its stage prefix. -/
theorem limitOwner_support_inter_roof_subset
    (hL : HalfwayGeometry L) (p : L.warpAt a) :
    (hL.limitOwner a p).support ∩ Gamma.roof (L.frontier a) ⊆ p.1.support :=
  limitComponent_support_inter_roof_subset_prefix hL a
    (hL.limitOwner_mem a p) p.2 (hL.extends_limitOwner a p)

/-- Endpoint capture removes the future-owner dependency completely. -/
theorem stageReference_eq_reference_of_endpoints_roof
    (hL : HalfwayGeometry L)
    (hends : ColouredSafeHammock.endpoints s e ⊆ Gamma.roof (L.frontier a)) :
    stageReference hL a s e = reference (L.warpAt a) s e := by
  ext p
  constructor
  · rintro ⟨hp, howner⟩
    exact ⟨hp, howner.2.mono_left
      (Gamma.support_mono_of_extends (hL.extends_limitOwner a ⟨p, hp⟩))⟩
  · rintro ⟨hp, hdisj⟩
    refine ⟨hp, hL.limitOwner_mem a ⟨p, hp⟩, ?_⟩
    apply Set.disjoint_left.mpr
    intro x hxOwner hxEnd
    exact Set.disjoint_left.mp hdisj
      (limitOwner_support_inter_roof_subset hL ⟨p, hp⟩ ⟨hxOwner, hends hxEnd⟩)
      hxEnd

/-- At an endpoint-captured stage, agreement of stage warps suffices;
the two limiting ladders need not agree. -/
theorem stageReference_congr_of_endpoints_roof
    {L' : Gamma.KappaLadder kappa}
    (hL : HalfwayGeometry L) (hL' : HalfwayGeometry L')
    (hends : ColouredSafeHammock.endpoints s e ⊆ Gamma.roof (L.frontier a))
    (hends' : ColouredSafeHammock.endpoints s e ⊆ Gamma.roof (L'.frontier a))
    (hstage : L.warpAt a = L'.warpAt a) :
    stageReference hL a s e = stageReference hL' a s e := by
  rw [stageReference_eq_reference_of_endpoints_roof hL hends,
    stageReference_eq_reference_of_endpoints_roof hL' hends', hstage]

theorem initialSet_reflect_of_roof (hL : HalfwayGeometry L)
    {x : V} (hx : x ∈ Gamma.initialSet (reference L.limitWarp s e))
    (hxRoof : x ∈ Gamma.roof (L.frontier a)) :
    x ∈ Gamma.initialSet (stageReference hL a s e) := by
  rw [TerminalContactSwitch.initialSet_eq_vertexSet_diff_hasIncoming_anyWarp
    (embedding hL a s e).global_isWarp] at hx
  rw [TerminalContactSwitch.initialSet_eq_vertexSet_diff_hasIncoming_anyWarp
    stageReference_isWarp]
  exact ⟨vertexSet_reflect hL hx.1 hxRoof,
    fun ⟨y, hy⟩ ↦ hx.2 ⟨y, (embedding hL a s e).familyEdges_subset hy⟩⟩

theorem terminalFrontier_reflect_of_roof (hL : HalfwayGeometry L)
    {x : V} (hx : x ∈ Gamma.terminalFrontier (reference L.limitWarp s e))
    (hxRoof : x ∈ Gamma.roof (L.frontier a)) :
    x ∈ Gamma.terminalFrontier (stageReference hL a s e) := by
  rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp
    (embedding hL a s e).global_isWarp] at hx
  rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp
    stageReference_isWarp]
  exact ⟨vertexSet_reflect hL hx.1 hxRoof,
    fun ⟨y, hy⟩ ↦ hx.2 ⟨y, (embedding hL a s e).familyEdges_subset hy⟩⟩

/-- A roofed nonterminal contact has exactly the same reference successor
locally and globally. This does not assert monotonicity of terminals. -/
theorem outgoing_edge_reflect (hL : HalfwayGeometry L)
    {x y : V} (hxy : (x, y) ∈ familyEdges (reference L.limitWarp s e))
    (hxRoof : x ∈ Gamma.roof (L.frontier a))
    (hxNotTerminal : x ∉ Gamma.terminalFrontier (stageReference hL a s e)) :
    (x, y) ∈ familyEdges (stageReference hL a s e) := by
  have hxGlobal := (familyEdges_subset_vertexSet_prod _ hxy).1
  have hxLocal := vertexSet_reflect hL hxGlobal hxRoof
  have hout : ∃ z, (x, z) ∈ familyEdges (stageReference hL a s e) := by
    by_contra hno
    apply hxNotTerminal
    rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp
      stageReference_isWarp]
    exact ⟨hxLocal, hno⟩
  obtain ⟨z, hxz⟩ := hout
  have hzy : z = y := (IsWarp.familyEdges_biUnique
    (embedding hL a s e).global_isWarp).2
      ((embedding hL a s e).familyEdges_subset hxz) hxy
  simpa only [hzy] using hxz

#print axioms stageReference_eq_reference_of_endpoints_roof
#print axioms stageReference_congr_of_endpoints_roof
#print axioms initialSet_reflect_of_roof
#print axioms terminalFrontier_reflect_of_roof
#print axioms outgoing_edge_reflect

end Erdos599.Blueprint.ColouredSafeEndpointStageReference
