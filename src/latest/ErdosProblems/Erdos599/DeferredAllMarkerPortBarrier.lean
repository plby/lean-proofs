/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredPreMarkerRecordRoof
import ErdosProblems.Erdos599.GroundingAllMarkerPorts

/-!
# The concrete pre-marker barrier for canonical deferred records

This instantiates both geometric hypotheses of the port barrier for the
actual canonical ladder. Incoming limiting reference edges reflect to the
pre-marker arrow; its essential boundary lies on the limiting warp. Thus
every residual walk from a finite record terminal, or after a ray-proxy's
first original edge, remains in the record's pre-marker roof.

The result imposes no target-purity or essential-marker hypothesis. The
additional unroofed-marker selection and the contraction/grounding theorem
are separate obligations, not assumed here to obtain confinement.
-/

noncomputable section

namespace Erdos599.DWeb.KappaLadder.Deferred

open Set Cardinal Order Ladder Alternating
open _root_.Erdos599.DirectedPath GroundingAllMarkerPorts

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

/-- The essential pre-marker frontier is carried by the final reference. -/
theorem canonicalDeferredLadder_arrowEssential_subset_limitVertices
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source) (a : Stage kappa) :
    G.essential (G.terminalFrontier
        ((canonicalDeferredLadder G kappa preferred).arrowPart a)) ⊆
      G.vertexSet (canonicalDeferredLadder G kappa preferred).limitWarp := by
  intro z hz
  by_contra hzOff
  have hzStrict :=
    canonicalLadder_mem_strictRoof_arrowPartFrontier_of_not_mem_limit
      preferred hkappa huncountable hNoEnter a
      (G.essential_subset_roof _ hz) hzOff
  exact hzStrict.2 hz

/-- An actual final reference edge entering the pre-marker roof has its
tail in the strict roof, with no auxiliary path hypothesis. -/
theorem canonicalDeferredLadder_referenceEdge_tail_strictRoof_arrowPart
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source) (a : Stage kappa)
    {x y : V}
    (hxy : (x, y) ∈ familyEdges
      (canonicalDeferredLadder G kappa preferred).limitWarp)
    (hy : y ∈ G.roof (G.terminalFrontier
      ((canonicalDeferredLadder G kappa preferred).arrowPart a))) :
    x ∈ G.strictRoof (G.terminalFrontier
      ((canonicalDeferredLadder G kappa preferred).arrowPart a)) := by
  apply canonicalLadder_limitFamilyEdge_tail_mem_strictRoof_arrowPartFrontier
    preferred hkappa huncountable hNoEnter a
  · simp only [familyEdges, Set.mem_iUnion] at hxy
    obtain ⟨p, hp, hpxy⟩ := hxy
    exact ⟨p, hp, hpxy⟩
  · exact hy

/-- All residual port walks from a vertex strictly behind the pre-marker
frontier stay behind that frontier. Receiving endpoints may lie on it. -/
theorem canonicalDeferredLadder_portWalk_receiver_mem_roof_arrowPart
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source) (a : Stage kappa)
    {s : Port V} {y : V}
    (hs : RoofPort (Gamma := G)
      (G.essential (G.terminalFrontier
        ((canonicalDeferredLadder G kappa preferred).arrowPart a))) s)
    (hpath : Relation.ReflTransGen
      (Step (canonicalDeferredLadder G kappa preferred).limitWarp) s (.inr y)) :
    y ∈ G.roof (G.terminalFrontier
      ((canonicalDeferredLadder G kappa preferred).arrowPart a)) := by
  let T := G.terminalFrontier
    ((canonicalDeferredLadder G kappa preferred).arrowPart a)
  have hincoming : ∀ {x z : V}, (x, z) ∈ familyEdges
      (canonicalDeferredLadder G kappa preferred).limitWarp →
      z ∈ G.roof (G.essential T) → x ∈ G.strictRoof (G.essential T) := by
    intro x z hxz hz
    rw [G.strictRoof_essential]
    apply canonicalDeferredLadder_referenceEdge_tail_strictRoof_arrowPart
      preferred hkappa huncountable hNoEnter a hxz
    rwa [G.roof_essential] at hz
  have h := reachable_preserves_roof (G.essential_idem T)
    (canonicalDeferredLadder_arrowEssential_subset_limitVertices
      preferred hkappa huncountable hNoEnter a) hincoming hpath hs
  change y ∈ G.roof (G.essential T) at h
  rwa [G.roof_essential] at h

/-- Finite-record form of the concrete barrier, with every geometric
condition obtained from the actual canonical construction. -/
theorem canonicalDeferredLadder_finiteRecord_portWalk_mem_roof_arrowPart
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    {a : Stage kappa} (f : FinitePath G.graph)
    (hchosen : (canonicalDeferredLadder G kappa preferred).chosen a =
      some (.inl f : G.DPath))
    {y : V} (hpath : Relation.ReflTransGen
      (Step (canonicalDeferredLadder G kappa preferred).limitWarp)
      (.inl f.finish) (.inr y)) :
    y ∈ G.roof (G.terminalFrontier
      ((canonicalDeferredLadder G kappa preferred).arrowPart a)) := by
  apply canonicalDeferredLadder_portWalk_receiver_mem_roof_arrowPart
    preferred hkappa huncountable hNoEnter a ?_ hpath
  change f.finish ∈ G.strictRoof (G.essential _)
  rw [G.strictRoof_essential]
  exact canonicalDeferredLadder_chosen_support_subset_strictRoof_arrowPart
    preferred hkappa huncountable hNoEnter hchosen f.finish_mem_support

/-- Ray-record form of the barrier. The first proxy arc is an actual
original edge from an arbitrary point of the selected ray. -/
theorem canonicalDeferredLadder_rayRecord_portWalk_mem_roof_arrowPart
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    {a : Stage kappa} (r : Ray G.graph)
    (hchosen : (canonicalDeferredLadder G kappa preferred).chosen a =
      some (.inr r : G.DPath))
    {x z y : V} (hx : x ∈ r.support) (hxz : G.graph.Adj x z)
    (hpath : Relation.ReflTransGen
      (Step (canonicalDeferredLadder G kappa preferred).limitWarp)
      (.inr z) (.inr y)) :
    y ∈ G.roof (G.terminalFrontier
      ((canonicalDeferredLadder G kappa preferred).arrowPart a)) := by
  let T := G.terminalFrontier
    ((canonicalDeferredLadder G kappa preferred).arrowPart a)
  have hxStrict : x ∈ G.strictRoof (G.essential T) := by
    rw [G.strictRoof_essential]
    exact canonicalDeferredLadder_chosen_support_subset_strictRoof_arrowPart
      preferred hkappa huncountable hNoEnter hchosen hx
  exact canonicalDeferredLadder_portWalk_receiver_mem_roof_arrowPart
    preferred hkappa huncountable hNoEnter a (s := .inr z)
    (G.adj_mem_roof_of_mem_strictRoof_of_essential (G.essential_idem T) hxz hxStrict)
    hpath

#print axioms canonicalDeferredLadder_finiteRecord_portWalk_mem_roof_arrowPart
#print axioms canonicalDeferredLadder_rayRecord_portWalk_mem_roof_arrowPart

end Erdos599.DWeb.KappaLadder.Deferred
