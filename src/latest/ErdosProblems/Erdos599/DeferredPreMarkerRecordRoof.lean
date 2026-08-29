/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingCanonicalEqualImpossible

/-!
# Pre-marker confinement of every canonical deferred record

The record selected at stage `a` is inessential already in the pre-marker
arrow, not merely in the successor warp. This is not an index shift to the
old accumulated warp. If a marker is inserted, maximality of the rung
preserves each old essential finite member; if no marker is inserted, the
successor is exactly the arrow. Self-roofing then confines the whole record,
including the initial segment of a finite record, to the strict arrow roof.

This supplies the record-side invariant in the sending/receiving barrier
of the informal repair, Section 1.42. It does not assert the still-missing
all-marker auxiliary grounding theorem.
-/

noncomputable section

namespace Erdos599.DWeb

open Set _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {G : DWeb V}

/-- An inessential component of a self-roofing warp is wholly in the
strict terminal roof. The statement applies equally to finite paths and rays. -/
theorem inessentialPath_support_subset_strictRoof_of_selfRoofing
    {W : Set G.DPath} (hW : G.IsWarp W)
    (hself : G.vertexSet W ⊆ G.roof (G.terminalFrontier W))
    {p : G.DPath} (hp : p ∈ G.inessentialPaths W) :
    p.support ⊆ G.strictRoof (G.terminalFrontier W) := by
  intro x hxp
  refine ⟨hself ⟨p, hp.1, hxp⟩, ?_⟩
  intro hx
  obtain ⟨q, hqW, hqx⟩ := hx.1
  have hqEss : q ∈ G.essentialWarpPart W := ⟨hqW, x, hqx, hx⟩
  exact (G.not_mem_inessentialPaths_of_intersects_essential hW hqEss
    ⟨x, hxp, G.terminal_mem_support hqx⟩) hp

namespace KappaLadder.Deferred

open Cardinal Order Ladder

variable {kappa : Cardinal.{u}}

/-- Canonical deferred selection creates no new inessential pre-marker
component. The absence of a marker is handled explicitly. -/
theorem canonicalDeferredLadder_chosen_mem_inessential_arrowPart
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    {a : Stage kappa} {p : G.DPath}
    (hchosen : (canonicalDeferredLadder G kappa preferred).chosen a = some p) :
    p ∈ G.inessentialPaths
      ((canonicalDeferredLadder G kappa preferred).arrowPart a) := by
  let L := canonicalDeferredLadder G kappa preferred
  have hlegal : IsDeferredLegal L :=
    canonicalDeferredLadder_isDeferredLegal preferred hkappa huncountable hNoEnter
  have hpArrow : p ∈ L.arrowPart a :=
    canonicalDeferredLadder_chosen_mem_arrowPart preferred hkappa huncountable
      hNoEnter hchosen
  refine ⟨hpArrow, ?_⟩
  intro hpEss
  cases hm : L.marker a with
  | none =>
      have hsuccessor : L.successorWarp a = L.arrowPart a := by
        rw [(hlegal.exactSuccessorArrows a).2]
        simp [markerPathSet, hm]
      have hpIE := (chosen_spec hlegal.validBookkeeping hchosen).1
      exact hpIE.2 (hsuccessor.symm ▸ hpEss)
  | some y =>
      rcases p with f | r
      · exact canonicalDeferredLadder_no_chosenFinite_of_essential_arrowPart
          preferred hkappa huncountable hNoEnter f hchosen hpEss hm
      · obtain ⟨_, z, hz, _⟩ := hpEss
        simp at hz

/-- Every vertex of a selected record lies in the strict pre-marker roof.
No target-purity premise and no condition on the existence of a marker occur. -/
theorem canonicalDeferredLadder_chosen_support_subset_strictRoof_arrowPart
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    {a : Stage kappa} {p : G.DPath}
    (hchosen : (canonicalDeferredLadder G kappa preferred).chosen a = some p) :
    p.support ⊆ G.strictRoof (G.terminalFrontier
      ((canonicalDeferredLadder G kappa preferred).arrowPart a)) := by
  have hsplit : (canonicalLadder G kappa preferred).IsSplitLegal :=
    canonicalLadder_isSplitLegal preferred hkappa huncountable hNoEnter
  exact inessentialPath_support_subset_strictRoof_of_selfRoofing (G := G)
    (hsplit.arrowPart_isWarp a)
    (canonicalLadder_arrowPart_selfRoofing preferred hkappa huncountable hNoEnter a)
    (canonicalDeferredLadder_chosen_mem_inessential_arrowPart
      preferred hkappa huncountable hNoEnter hchosen)

#print axioms canonicalDeferredLadder_chosen_mem_inessential_arrowPart
#print axioms canonicalDeferredLadder_chosen_support_subset_strictRoof_arrowPart

end KappaLadder.Deferred
end Erdos599.DWeb
