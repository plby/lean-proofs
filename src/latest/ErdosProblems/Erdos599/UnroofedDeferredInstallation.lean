/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedDeferredBookkeeping

/-!
# Reinstalling deferred bookkeeping on the actual unroofed ladder

The two fixed `ofData` constructions have equal inputs, so their chosen
streams agree. Mere validity of two unrelated choices would not suffice.
This equality concerns only the actual unroofed marker protocol.
-/

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Ladder KappaLadder

universe u

variable {V : Type u}

theorem deferred_withValidBookkeeping_ladder_eq
    (G : DWeb V) (kappa : Cardinal.{u}) (preferred : Stage kappa → Option V)
    (hNoEnter : G.NoEdgeEnters G.source) :
    Deferred.withValidBookkeeping (ladder G kappa preferred) = ladder G kappa preferred := by
  let L := ladder G kappa preferred
  have hfamilies : (fun a ↦ Deferred.selectable L a) =
      (fun a ↦ G.inessentialPaths ((ladderCore G kappa preferred).successorWarp a)) :=
    funext fun a ↦ ladder_deferred_selectable_eq G kappa preferred hNoEnter a
  have hchosen : (Deferred.chosenBookkeeping L).chosen = L.chosen :=
    congrArg (fun f ↦ (Ladder.Bookkeeping.ofData f
      (fun p : G.DPath ↦ G.terminal? p = none)).chosen) hfamilies
  change Deferred.withValidBookkeeping L = L
  dsimp only [Deferred.withValidBookkeeping]
  rw [hchosen]

#print axioms deferred_withValidBookkeeping_ladder_eq

end Erdos599.DWeb.UnroofedMarker
