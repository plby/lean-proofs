/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerAuxiliary
import ErdosProblems.Erdos599.GroundingAllMarkerRecordAvoidance

/-!
# The actual unroofed-ladder residual region misses all surviving records

The popular separator and stationary good indices are the previously
constructed ones. The cut-residual graph deletes their actual reference
edges and off-reference ports and targets their uncut marker ports.
Every surviving index has a whole grounded record disjoint from its
escape region. No additional reachability or grounding premise is used.
-/

noncomputable section

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Order Ladder KappaLadder GroundingAllMarkerAuxiliary

universe u

variable {V : Type u}

def auxiliaryEscapeRegion (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hphi : Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi) : Set V :=
  (auxiliaryInput G kappa preferred hNoEnter).escapeRegion
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi).cut

/-- The stationary good-index set supplies entire uncut owners missing
the concrete residual escape region, including ray owners. -/
theorem exists_uncut_grounded_record_disjoint_escapeRegion
    (G : DWeb V) (kappa : Cardinal.{u}) (preferred : Stage kappa → Option V)
    (hNoEnter : G.NoEdgeEnters G.source) (hkappa : kappa.IsRegular)
    (huncountable : aleph0 < kappa)
    (hphi : Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi)
    {a : Stage kappa}
    (ha : a ∈ auxiliaryGoodRecordIndices G kappa preferred hNoEnter hkappa huncountable hphi) :
    ∃ p : GroundedRecord G kappa preferred,
      groundedRecordStage G kappa preferred p = a ∧
      GroundingAllMarkerAuxiliary.Input.Vertex.source p ∉
        (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi).cut ∧
      Disjoint p.1.edgeSet ((auxiliaryInput G kappa preferred hNoEnter).cutEdges
        (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi).cut) ∧
      Disjoint p.1.support
        (auxiliaryEscapeRegion G kappa preferred hNoEnter hkappa huncountable hphi) := by
  obtain ⟨p, hp, hsource, hedges⟩ := exists_uncut_grounded_record G kappa preferred
    hNoEnter hkappa huncountable hphi ha
  refine ⟨p, hp, hsource, hedges, ?_⟩
  exact (auxiliaryInput G kappa preferred hNoEnter).record_disjoint_escapeRegion _
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi).separates
    hsource hedges

#print axioms auxiliaryEscapeRegion
#print axioms exists_uncut_grounded_record_disjoint_escapeRegion

end Erdos599.DWeb.UnroofedMarker
