/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayMovingGlobalClosure
import ErdosProblems.Erdos599.DeferredLadderRoofTransport

/-!
# Global reference supports lie in the union of ladder roofs

At the final successor-cardinal limit, every vertex of a thread limit was
already present at an ordinary stage.  Self-roofing of that stage and
invariance of roofs under essential trimming place it in the limiting roof.
No finite-character hypothesis on the limiting reference is used.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Alternating Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace ClubStageGeometry

/-- Every vertex of the limiting warp occurs below an earlier frontier. -/
theorem vertexSet_limitWarp_subset_limitRoof
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) :
    Gamma.vertexSet C.ladder.limitWarp ⊆ C.ladder.limitRoof := by
  have hlimit : Order.IsSuccLimit (succ kappa).ord :=
    Cardinal.isSuccLimit_ord C.legal.regular.aleph0_le
  obtain ⟨D, hstage, hpaths⟩ :=
    C.legal.limitStages (Ladder.finalStage (succ kappa)) hlimit
  change Gamma.vertexSet
    (C.ladder.accumulated (Ladder.finalStage (succ kappa))) ⊆ _
  rw [hpaths, D.vertexSet_limitPaths Gamma]
  intro x hx
  obtain ⟨b, hxb⟩ := Set.mem_iUnion.1 hx
  let a : Ladder.Stage (succ kappa) := ⟨b.1, b.2⟩
  have hxbStage : x ∈ Gamma.vertexSet (C.ladder.warpAt a) := by
    rw [hstage b] at hxb
    exact hxb
  have hxRoofTerminal : x ∈
      Gamma.roof (Gamma.terminalFrontier (C.ladder.warpAt a)) :=
    DWeb.KappaLadder.Deferred.vertexSet_warpAt_subset_roof_terminalFrontier
      C.legal a hxbStage
  apply Set.mem_iUnion.2
  refine ⟨a, ?_⟩
  rw [C.ladder.frontier_eq_essential_terminalFrontier
      C.legal.roofsSourceAtStages a, Gamma.roof_essential]
  exact hxRoofTerminal

/-- Pathwise form needed by the global-reference closing operation. -/
theorem limitWarp_support_subset_limitRoof
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (p : Gamma.DPath) (hp : p ∈ C.ladder.limitWarp) :
    p.support ⊆ C.ladder.limitRoof := by
  intro x hxp
  exact C.vertexSet_limitWarp_subset_limitRoof ⟨p, hp, hxp⟩

end ClubStageGeometry

namespace MovingGlobalClosure

/-- The reference-support premise of the closing operation is discharged
by the actual deferred ladder, including its possible limiting rays. -/
theorem exists_of_roof_hammocks
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (ZBefore T B X0 : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hTarget : ∀ v ∈ T ∩ C.ladder.limitRoof,
      ∃ p : FinitePath Gamma.graph,
        p.start = v ∧ p.finish ∈ B ∧
          p.support ⊆ C.ladder.limitRoof ∧ Preserves p)
    (hRoofHammocks : HammockClosedUpTo Gamma C.ladder.limitWarp
      C.ladder.limitRoof ZBefore C.innerRoof C.ladder.limitRoof kappa)
    (hZBefore : #ZBefore ≤ kappa)
    (hX0card : #X0 ≤ kappa)
    (hX0roof : X0 ⊆ C.ladder.limitRoof) :
    Nonempty (MovingGlobalClosure C ZBefore T B X0 Preserves) :=
  exists_of_limitRoof_geometry C ZBefore T B X0 Preserves hTarget
    C.limitWarp_support_subset_limitRoof hRoofHammocks hZBefore hX0card hX0roof

end MovingGlobalClosure

namespace Moving931GlobalClosure

/-- The actual scheduled-seed closure only needs the preceding maximal
hammock assertion. Reference support follows from the ladder itself. -/
theorem exists_of_roof_hammocks
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (ZBefore X0 : Set V)
    (hRoofHammocks : HammockClosedUpTo Gamma C.ladder.limitWarp
      C.ladder.limitRoof ZBefore C.innerRoof C.ladder.limitRoof kappa)
    (hZBefore : #ZBefore ≤ kappa)
    (hX0card : #X0 ≤ kappa)
    (hX0roof : X0 ⊆ C.ladder.limitRoof) :
    Nonempty (Moving931GlobalClosure C ZBefore X0) :=
  exists_of_scheduledSeed C ZBefore X0 C.limitWarp_support_subset_limitRoof
    hRoofHammocks hZBefore hX0card hX0roof

end Moving931GlobalClosure

#print axioms ClubStageGeometry.vertexSet_limitWarp_subset_limitRoof
#print axioms MovingGlobalClosure.exists_of_roof_hammocks
#print axioms Moving931GlobalClosure.exists_of_roof_hammocks

end Erdos599.Blueprint.LinkageBlueprint
