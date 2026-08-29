/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeSmallBadReference

/-!
# Native linking at an actual club stage

At a club stage outside the ladder obstruction, the inessential reference
carrier is bounded by the predecessor cardinal. Discarding it leaves the
actual finite essential reference whose terminals equal the stage frontier.
The native large-hammock linking theorem therefore applies without an
assumed finite-character statement for the full accumulated stage warp.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry

open Set Cardinal Order DirectedPath Ladder
open ColouredSafeAmbientOccurrence ColouredSafeHammock

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

theorem native_hasCard_exists_frontier_path_avoiding
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club)
    {s : V} {e : Option V}
    {extra : Occurrence (C.ladder.warpAt a) s → Prop}
    (h : HasCard (C.ladder.warpAt a) s e extra (succ kappa))
    (hnondeg : ∀ A, extra A → ∀ t, e = some t → ¬A.HasFiniteSwitchedPathTo t)
    {X : Set V} (hX : #X ≤ kappa) :
    ∃ (A : Occurrence (C.ladder.warpAt a) s) (p : FinitePath Gamma.graph),
      A ∈ goodRoutes (C.ladder.warpAt a) s e extra ∧ p.start = s ∧
      p.finish ∈ C.ladder.frontier a ∧
      p.edgeSet ⊆ A.switchedEdges ∧ p.support ∩ X ⊆ endpoints s e := by
  have hbad : #(Gamma.vertexSet
      (C.ladder.warpAt a \ ladderReference C.ladder a)) ≤ kappa := by
    apply DWeb.KappaLadder.Deferred.mk_vertexSet_inessentialWarpAt_le_of_not_mem_phi
      C.legal C.capacity_infinite a
    intro haPhi
    exact Set.disjoint_left.mp C.club_avoids_phi ha haPhi
  have hsub : ladderReference C.ladder a ⊆ C.ladder.warpAt a :=
    fun _ hp ↦ hp.1
  obtain ⟨A, p, hA, hps, hpt, hpe, havoid⟩ :=
    h.exists_referenceTerminal_path_avoiding_of_small_discard
      (C.legal.warpStages (Stage.toExtended a)) hsub
      ladderReference.finiteCharacter C.capacity_infinite hbad hnondeg hX
  rw [ladderReference.terminalFrontier_eq C.legal] at hpt
  exact ⟨A, p, hA, hps, hpt, hpe, havoid⟩

#print axioms native_hasCard_exists_frontier_path_avoiding

end Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry
