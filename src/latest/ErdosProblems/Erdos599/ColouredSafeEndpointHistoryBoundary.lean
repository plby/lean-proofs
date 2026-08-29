/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointMarkedBoundary
import ErdosProblems.Erdos599.AugmentedAccountedChain

/-!
# The actual endpoint graph satisfies the history boundary conditions

Source coverage excludes incoming edges at original sources. A distinct
endpoint edge leaving the original target is impossible, using the actual
pruned-reference occurrence and its signed balance. Thus augmented rays
miss the target, without identifying endpoint and full-reference graphs.
-/

namespace Erdos599.Blueprint.ColouredSafeEndpointBlueprint

open Set Cardinal Order DirectedPath Ladder LinkageBlueprint
open _root_.Erdos599.Alternating
open ColouredSafeAmbientOccurrence ColouredSafeHammock ColouredSafeEndpointReference
open _root_.Erdos599.ColouredSafeLocalTransactionRealLedger
open _root_.Erdos599.ColouredSafeAugmentedRealReach

universe u v

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}

theorem IsBlueprint.source_no_incoming {a : Stage (succ kappa)} {W : Set (web C).DPath}
    (hW : IsBlueprint C a W) {s : V} (hs : s ∈ Gamma.source) :
    ¬HasIncoming (familyEdges W) s := by
  rintro ⟨x, hxs⟩
  have hsV := (familyEdges_subset_vertexSet_prod W hxs).2
  rcases hW.covers_source hs with hsInitial | hsReference
  · rw [TerminalContactSwitch.initialSet_eq_vertexSet_diff_hasIncoming_anyWarp hW.isWarp]
      at hsInitial
    exact hsInitial.2 ⟨x, hxs⟩
  · obtain ⟨p, hp, hps⟩ := hsReference
    exact hp.2 ⟨hp.1.1, s, hps ▸ p.initial_mem_support, hsV⟩

theorem not_adj_of_target_of_ne {s t : V} (hs : s ∈ Gamma.target) (hne : s ≠ t) :
    ¬(web C).graph.Adj s t := by
  rintro (hreal | ⟨H, hH, hcard⟩)
  · exact (C.normalized hreal).2 hs
  · obtain ⟨A, _hAH, hgood, _hdisjoint⟩ :=
      exists_mem_avoiding (X := (∅ : Set V)) hH hcard (by simp)
    have hPruned := ColouredSafeEndpointReference.isWarp
      (s := s) (e := some t) (C.legal.warpStages (finalStage (succ kappa)))
    obtain ⟨z, hsz⟩ := (hgood.1.forward_endpoint_incidence hPruned hgood.2.1 hne
      hgood.2.2.1 (hgood.2.2.2.1 t rfl)).1
    obtain ⟨W, _hW, _hWfin, hforward⟩ := hgood.1
    exact (C.normalized (familyEdges_subset_adj W (hforward hsz))).2 hs

theorem ray_not_mem_target (r : Ray (web C).graph) (n : Nat) : r n ∉ Gamma.target := by
  intro hn
  apply not_adj_of_target_of_ne hn _ (r.adj_succ n)
  intro heq
  have := r.injective heq
  omega

/-- Construct the graph-explicit history record from actual endpoint
blueprints and the invariants retained by the checked local successor. -/
def accountedChain_of_blueprints {I : Type v} [LinearOrder I]
    (index : I → Stage (succ kappa)) (W : I → Set (web C).DPath)
    (hW : ∀ i, IsBlueprint C (index i) (W i))
    (hV : Monotone fun i ↦ (web C).vertexSet (W i))
    (hE : Monotone fun i ↦ RealEdges (Gamma := web C) Gamma.graph.Adj (W i))
    (hI : Monotone fun i ↦ (web C).initialSet (W i))
    (haccount : ∀ {i j}, i ≤ j → FullAccount Gamma (web C) (W i) (W j) Gamma.target)
    (hpred : ∀ {i j}, i ≤ j → SourcePredecessorRefines Gamma (web C) (W i) (W j)) :
    AugmentedAccountedChain Gamma (web C) I where
  stage := W
  warp := fun i ↦ (hW i).isWarp
  vertices_mono := hV
  edges_mono := hE
  initials_mono := hI
  source_no_incoming := fun i _ hs ↦ (hW i).source_no_incoming hs
  account := haccount
  predecessor := hpred

#print axioms IsBlueprint.source_no_incoming
#print axioms not_adj_of_target_of_ne
#print axioms ray_not_mem_target
#print axioms accountedChain_of_blueprints

end Erdos599.Blueprint.ColouredSafeEndpointBlueprint
