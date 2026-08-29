/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerLadder
import ErdosProblems.Erdos599.LadderSuccessorBridge

/-!
# Exact successor arrows for the unroofed-marker ladder

The new ladder satisfies the genuine pathwise rung-arrow clause, with
unique images and exact support and edge sets. Its marker is disjoint from
the arrow by the proved roof invariant. This connects the new construction
to the shared geometric API without claiming the historical exhaustion rule.
-/

noncomputable section

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Order Ladder KappaLadder

universe u

variable {V : Type u}

theorem ladder_successor_eq_arrow_union_marker (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (a : Stage kappa) :
    (ladder G kappa preferred).successorWarp a =
      G.arrow ((ladder G kappa preferred).warpAt a)
        ((ladder G kappa preferred).liftedRung a) ∪
      (ladder G kappa preferred).markerPathSet a := by
  change (state G (extendLadderPreference kappa preferred) (a.1 + 1)).1 = _
  rw [state_succ]
  rfl

theorem ladder_marker_outside_arrow (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (a : Stage kappa) {y : V} (hy : (ladder G kappa preferred).marker a = some y) :
    y ∉ G.vertexSet (G.arrow ((ladder G kappa preferred).warpAt a)
      ((ladder G kappa preferred).liftedRung a)) := by
  let pref := extendLadderPreference kappa preferred
  have hinv := state_invariant G pref hNoEnter a.1
  have hself := G.canonicalArrow_self_roofing hNoEnter (state G pref a.1)
    hinv.warp hinv.selfRoof hinv.sourceRoof
  intro hymem
  exact markerAt_not_mem_preMarkerRoof G pref hy (hself hymem)

theorem ladder_arrowPart_eq_arrow (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (a : Stage kappa) :
    (ladder G kappa preferred).arrowPart a =
      G.arrow ((ladder G kappa preferred).warpAt a)
        ((ladder G kappa preferred).liftedRung a) := by
  apply (ladder G kappa preferred).arrowPart_eq_arrow_of_successor_eq a
    (ladder_successor_eq_arrow_union_marker G kappa preferred a)
  apply (ladder G kappa preferred).disjoint_arrow_markerPathSet a
  intro y hy
  exact ladder_marker_outside_arrow G kappa preferred hNoEnter a hy

/-- The complete exact-arrow interface, including uniqueness of each
continuation and surjectivity onto the pre-marker family. -/
theorem ladder_hasExactSuccessorArrows (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source) :
    (ladder G kappa preferred).HasExactSuccessorArrows := by
  let L := ladder G kappa preferred
  have hgeometry := ladder_geometry G kappa preferred hNoEnter
  intro a
  apply L.exactSuccessorArrowAt_of_arrow a
    (L.arrowRealizesRung_of_isWarp_selfRoof a
      (hgeometry.warpStages (Stage.toExtended a))
      (hgeometry.selfRoofing (Stage.toExtended a))
      (ladder_hasWaveRungs G kappa preferred a).1)
    (ladder_successor_eq_arrow_union_marker G kappa preferred a)
  apply L.disjoint_arrow_markerPathSet a
  intro y hy
  exact ladder_marker_outside_arrow G kappa preferred hNoEnter a hy

/-- The new insertion rule is unroofed relative to the actual abstract
`arrowPart`, not merely relative to an unrelated recursive expression. -/
theorem ladder_marker_not_mem_roof_arrowPart (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    {a : Stage kappa} {y : V} (hy : (ladder G kappa preferred).marker a = some y) :
    y ∉ G.roof (G.terminalFrontier ((ladder G kappa preferred).arrowPart a)) := by
  rw [ladder_arrowPart_eq_arrow G kappa preferred hNoEnter]
  exact markerAt_not_mem_preMarkerRoof G (extendLadderPreference kappa preferred) hy

#print axioms ladder_hasExactSuccessorArrows
#print axioms ladder_marker_not_mem_roof_arrowPart

end Erdos599.DWeb.UnroofedMarker
