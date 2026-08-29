/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointBlueprint
import ErdosProblems.Erdos599.ColouredSafeNativeNoStrongReal

/-!
# Endpoint marked edges and the persistent frontier

Forgetting the capture filter gives a strong hammock relative to the same
pruned reference. The existing subdivision-incidence proof then excludes
real edges. Persistence gives current frontier membership only for vertices
already roofed at that stage, not for arbitrary persistent vertices.
-/

namespace Erdos599.Blueprint.ColouredSafeEndpointBlueprint

open Set Cardinal Order DirectedPath Ladder LinkageBlueprint
open _root_.Erdos599.Alternating
open ColouredSafeAmbientOccurrence ColouredSafeHammock ColouredSafeEndpointReference

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {a : Stage (succ kappa)}
variable {s t : V}

theorem marked_isStrong_pruned (h : marked C s t) :
    ColouredSafeShortcutGraph.IsStrong (reference C.ladder.limitWarp s (some t)) kappa s t :=
  ColouredSafeShortcutGraph.hasCard_mono_filter h (fun _ hA ↦ hA.2)

theorem marked_ne (h : marked C s t) : s ≠ t := by
  intro hst
  subst t
  obtain ⟨H, hH, hcard⟩ := marked_isStrong_pruned h
  obtain ⟨A, _hAH, hgood, _hdisjoint⟩ :=
    exists_mem_avoiding (X := (∅ : Set V)) hH hcard (by simp)
  apply hgood.2.2.2.2
  refine ⟨FinitePath.trivial Gamma.graph s, rfl, rfl, ?_⟩
  simp [FinitePath.edgeSet, FinitePath.trivial]

theorem marked_not_real (hinc : HasHereditarySubdivisionIncidence Gamma.graph)
    (h : marked C s t) : ¬Gamma.graph.Adj s t := by
  intro hreal
  exact ColouredSafeShortcutGraph.not_isStrong_of_subdivisionIncidence
    (ColouredSafeEndpointReference.isWarp (C.legal.warpStages (finalStage (succ kappa))))
    (hinc hreal) (marked_isStrong_pruned h)

theorem strictRoof_of_roof_not_frontier
    (hroof : s ∈ Gamma.roof (C.ladder.frontier a)) (hnot : s ∉ C.ladder.frontier a) :
    s ∈ Gamma.strictRoof (C.ladder.frontier a) := by
  refine ⟨hroof, ?_⟩
  rw [C.ladder.frontiersAreEssential_of_roofsSourceAtStages C.legal.roofsSourceAtStages a]
  exact hnot

theorem mem_frontier_of_persistent_of_roof (hpersistent : s ∈ C.persistent)
    (hroof : s ∈ Gamma.roof (C.ladder.frontier a)) : s ∈ C.ladder.frontier a := by
  by_contra hnot
  exact hpersistent.2 (Set.mem_iUnion.mpr ⟨a, strictRoof_of_roof_not_frontier hroof hnot⟩)

#print axioms marked_isStrong_pruned
#print axioms marked_ne
#print axioms marked_not_real
#print axioms mem_frontier_of_persistent_of_roof

end Erdos599.Blueprint.ColouredSafeEndpointBlueprint
