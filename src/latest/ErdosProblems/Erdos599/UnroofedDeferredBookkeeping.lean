/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerLadder
import ErdosProblems.Erdos599.DeferredHindranceGrounding

/-!
# Deferred and ordinary bookkeeping on the actual unroofed ladder

The current marker is essential when inserted. Every successor-inessential
path therefore avoids it, and filtering by current-marker initial removes
nothing. The concrete bookkeeping structures, with the same actual chosen
records, are equal. This is not an identification of two ladder constructions.
-/

noncomputable section

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Ladder KappaLadder

universe u

variable {V : Type u} (G : DWeb V) (kappa : Cardinal.{u})
  (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)

include hNoEnter in
theorem ladder_inessential_avoids_current_marker
    {a : Stage kappa} {p : G.DPath} {y : V}
    (hp : p ∈ G.inessentialPaths ((ladder G kappa preferred).successorWarp a))
    (hy : (ladder G kappa preferred).marker a = some y) : y ∉ p.support := by
  let L := ladder G kappa preferred
  have hyMem : G.trivialPath y ∈ L.successorWarp a :=
    markerAt_trivial_mem_successor G (extendLadderPreference kappa preferred) hy
  have hyEss : G.trivialPath y ∈ G.essentialWarpPart (L.successorWarp a) :=
    ⟨hyMem, y, G.terminal?_trivialPath y,
      ladder_marker_essential_successor G kappa preferred hy⟩
  intro hyp
  exact (G.not_mem_inessentialPaths_of_intersects_essential
    ((ladder_geometry G kappa preferred hNoEnter).warpStages (Stage.succExtended a))
    hyEss ⟨y, hyp, by simp⟩) hp

include hNoEnter in
theorem ladder_deferred_selectable_eq (a : Stage kappa) :
    Deferred.selectable (ladder G kappa preferred) a =
      G.inessentialPaths ((ladder G kappa preferred).successorWarp a) := by
  ext p
  constructor
  · exact And.left
  · intro hp
    refine ⟨hp, ?_⟩
    intro hm
    exact ladder_inessential_avoids_current_marker G kappa preferred hNoEnter hp hm
      p.initial_mem_support

include hNoEnter in
theorem ladder_deferred_bookkeeping_eq :
    Deferred.bookkeeping (ladder G kappa preferred) =
      (ladder G kappa preferred).bookkeeping := by
  simp only [Deferred.bookkeeping, KappaLadder.bookkeeping,
    ladder_deferred_selectable_eq G kappa preferred hNoEnter]

include hNoEnter in
theorem ladder_deferred_validBookkeeping :
    Deferred.HasValidBookkeeping (ladder G kappa preferred) := by
  change (Deferred.bookkeeping (ladder G kappa preferred)).IsValid
  rw [ladder_deferred_bookkeeping_eq G kappa preferred hNoEnter]
  exact ladder_validBookkeeping G kappa preferred

include hNoEnter in
theorem ladder_deferred_phi_eq :
    Deferred.phi (ladder G kappa preferred) = (ladder G kappa preferred).phi :=
  congrArg Ladder.Bookkeeping.phi (ladder_deferred_bookkeeping_eq G kappa preferred hNoEnter)

include hNoEnter in
theorem ladder_deferred_phiInfinite_eq :
    Deferred.phiInfinite (ladder G kappa preferred) = (ladder G kappa preferred).phiInfinite :=
  congrArg Ladder.Bookkeeping.phiInfinite
    (ladder_deferred_bookkeeping_eq G kappa preferred hNoEnter)

include hNoEnter in
theorem ladder_deferred_phiFinite_eq :
    Deferred.phiFinite (ladder G kappa preferred) = (ladder G kappa preferred).phiFinite :=
  congrArg Ladder.Bookkeeping.phiFinite
    (ladder_deferred_bookkeeping_eq G kappa preferred hNoEnter)

include hNoEnter in
theorem ladder_deferred_phiHanging_eq :
    Deferred.phiHanging (ladder G kappa preferred) = (ladder G kappa preferred).phiHanging := by
  change Deferred.phi (ladder G kappa preferred) \ (ladder G kappa preferred).phiGround =
    (ladder G kappa preferred).phi \ (ladder G kappa preferred).phiGround
  rw [ladder_deferred_phi_eq G kappa preferred hNoEnter]

#print axioms ladder_inessential_avoids_current_marker
#print axioms ladder_deferred_bookkeeping_eq
#print axioms ladder_deferred_validBookkeeping
#print axioms ladder_deferred_phi_eq
#print axioms ladder_deferred_phiInfinite_eq
#print axioms ladder_deferred_phiFinite_eq
#print axioms ladder_deferred_phiHanging_eq

end Erdos599.DWeb.UnroofedMarker
