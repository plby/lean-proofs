/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerIncoming
import ErdosProblems.Erdos599.GroundingAllMarkerPorts

/-!
# All-marker birth-index descent for the actual unroofed ladder

This instantiates the sending/receiving roof barrier with the actual
unroofed-marker construction. All reference-edge and boundary hypotheses
are proved from its recursion. Every marker reached from a finite record,
or after the first original edge of a ray proxy, has strictly earlier birth
index. Markers are not restricted to essential final components; no
target-purity assumption is made on the residual walk.

Converting this residual-graph fact into a full grounding theorem remains
a separate construction, not a hidden premise of the barrier.
-/

noncomputable section

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Order Ladder KappaLadder Alternating GroundingAllMarkerPorts
open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u}

/-- The pre-marker roofs themselves increase, including between two
successive insertion stages. -/
theorem ladder_roof_arrowPart_mono (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    {a b : Stage kappa} (hab : a ≤ b) :
    G.roof (G.terminalFrontier ((ladder G kappa preferred).arrowPart a)) ⊆
      G.roof (G.terminalFrontier ((ladder G kappa preferred).arrowPart b)) := by
  rcases hab.lt_or_eq with hab | rfl
  · let L := ladder G kappa preferred
    have hpreNext : G.roof (G.terminalFrontier (L.arrowPart a)) ⊆
        G.roof (G.terminalFrontier (L.successorWarp a)) := by
      apply G.roof_mono
      rintro z ⟨p, hp, hpz⟩
      exact ⟨p, hp.1, hpz⟩
    have hab' : Stage.succExtended a ≤ Stage.toExtended b := by
      change a.1 + 1 ≤ b.1
      exact (Order.add_one_le_iff).mpr (show a.1 < b.1 from hab)
    have hnextb := roof_mono_of_geometry (ladder_geometry G kappa preferred hNoEnter) hab'
    have hlast : G.roof (G.terminalFrontier (L.warpAt b)) ⊆
        G.roof (G.terminalFrontier (L.arrowPart b)) := by
      rw [ladder_arrowPart_eq_arrow G kappa preferred hNoEnter b]
      have hinv := state_invariant G (extendLadderPreference kappa preferred) hNoEnter b.1
      exact G.roof_terminalFrontier_subset_canonicalArrow hNoEnter
        (state G (extendLadderPreference kappa preferred) b.1)
        hinv.warp hinv.selfRoof hinv.sourceRoof
    exact hpreNext.trans (hnextb.trans hlast)
  · exact Set.Subset.rfl

theorem ladder_futureMarker_not_mem_roof_arrowPart
    (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    {a b : Stage kappa} {y : V} (hab : a ≤ b)
    (hy : (ladder G kappa preferred).marker b = some y) :
    y ∉ G.roof (G.terminalFrontier ((ladder G kappa preferred).arrowPart a)) := by
  intro hyRoof
  exact ladder_marker_not_mem_roof_arrowPart G kappa preferred hNoEnter hy
    (ladder_roof_arrowPart_mono G kappa preferred hNoEnter hab hyRoof)

/-- The actual limiting reference satisfies every geometric input of the
two-sided port barrier. -/
theorem ladder_portWalk_receiver_mem_roof_arrowPart
    (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (a : Stage kappa) {s : Port V} {y : V}
    (hs : RoofPort (Gamma := G)
      (G.essential (G.terminalFrontier ((ladder G kappa preferred).arrowPart a))) s)
    (hpath : Relation.ReflTransGen (Step (ladder G kappa preferred).limitWarp) s (.inr y)) :
    y ∈ G.roof (G.terminalFrontier ((ladder G kappa preferred).arrowPart a)) := by
  let L := ladder G kappa preferred
  let T := G.terminalFrontier (L.arrowPart a)
  have hincoming : ∀ {x z : V}, (x, z) ∈ familyEdges L.limitWarp →
      z ∈ G.roof (G.essential T) → x ∈ G.strictRoof (G.essential T) := by
    intro x z hxz hz
    rw [G.strictRoof_essential]
    apply ladder_limitEdge_tail_strictRoof_arrowPart G kappa preferred hNoEnter a
    · simp only [familyEdges, Set.mem_iUnion] at hxz
      obtain ⟨p, hp, hpxz⟩ := hxz
      exact ⟨p, hp, hpxz⟩
    · rwa [G.roof_essential] at hz
  have h := reachable_preserves_roof (G.essential_idem T)
    (ladder_arrowEssential_subset_limitVertices G kappa preferred hNoEnter a)
    hincoming hpath hs
  change y ∈ G.roof (G.essential T) at h
  rwa [G.roof_essential] at h

/-- A residual walk from a selected finite terminal to any marker has
strictly decreasing birth index, whether that marker is grounded or hanging. -/
theorem ladder_finiteRecord_reachable_marker_index_lt
    (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    {a b : Stage kappa} (f : FinitePath G.graph) {y : V}
    (hchosen : (ladder G kappa preferred).chosen a = some (.inl f : G.DPath))
    (hmarker : (ladder G kappa preferred).marker b = some y)
    (hpath : Relation.ReflTransGen (Step (ladder G kappa preferred).limitWarp)
      (.inl f.finish) (.inr y)) : b < a := by
  have hyRoof := ladder_portWalk_receiver_mem_roof_arrowPart
    G kappa preferred hNoEnter a (s := .inl f.finish) ?_ hpath
  · by_contra hba
    exact ladder_futureMarker_not_mem_roof_arrowPart G kappa preferred hNoEnter
      (le_of_not_gt hba) hmarker hyRoof
  · change f.finish ∈ G.strictRoof (G.essential _)
    rw [G.strictRoof_essential]
    exact ladder_chosen_support_subset_strictRoof_arrowPart
      G kappa preferred hNoEnter hchosen f.finish_mem_support

/-- Ray proxies obey the same strict birth-index descent after their
first original edge, from any vertex of the selected ray. -/
theorem ladder_rayRecord_reachable_marker_index_lt
    (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    {a b : Stage kappa} (r : Ray G.graph) {x z y : V}
    (hchosen : (ladder G kappa preferred).chosen a = some (.inr r : G.DPath))
    (hx : x ∈ r.support) (hxz : G.graph.Adj x z)
    (hmarker : (ladder G kappa preferred).marker b = some y)
    (hpath : Relation.ReflTransGen (Step (ladder G kappa preferred).limitWarp)
      (.inr z) (.inr y)) : b < a := by
  let T := G.terminalFrontier ((ladder G kappa preferred).arrowPart a)
  have hxStrict : x ∈ G.strictRoof (G.essential T) := by
    rw [G.strictRoof_essential]
    exact ladder_chosen_support_subset_strictRoof_arrowPart G kappa preferred hNoEnter hchosen hx
  have hyRoof := ladder_portWalk_receiver_mem_roof_arrowPart G kappa preferred hNoEnter a
    (s := .inr z)
    (G.adj_mem_roof_of_mem_strictRoof_of_essential (G.essential_idem T) hxz hxStrict) hpath
  by_contra hba
  exact ladder_futureMarker_not_mem_roof_arrowPart G kappa preferred hNoEnter
    (le_of_not_gt hba) hmarker hyRoof

#print axioms ladder_roof_arrowPart_mono
#print axioms ladder_finiteRecord_reachable_marker_index_lt
#print axioms ladder_rayRecord_reachable_marker_index_lt

end Erdos599.DWeb.UnroofedMarker
