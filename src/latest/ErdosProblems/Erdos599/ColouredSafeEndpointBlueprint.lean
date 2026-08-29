/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafePostClosureEndpointClassification
import ErdosProblems.Erdos599.ColouredSafeWeakBlueprintTransaction

/-!
# Blueprints using the actual endpoint-pruned imaginary predicates

The augmentation keeps the original vertices, source and target. Its
imaginary and marked edges are exactly the endpoint-pruned captured-hammock
predicates used by the checked assignment. The six blueprint conditions
retain full-reference source coverage. The working region is the limiting
roof, not one small closing set chosen for a future interval row.

Every actual blueprint supplies a small seed for a new enriched moving
closure, chosen before that future row. This does not claim that the old
warp already satisfies source coverage at the newly selected frontier.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeEndpointBlueprint

open Set Cardinal Order DirectedPath Ladder LinkageBlueprint
open _root_.Erdos599.Alternating
open ColouredSafeEndpointHammock

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

def graph (C : ClubStageGeometry Gamma Y kappa (succ kappa)) : Digraph V where
  Adj x y := Gamma.graph.Adj x y ∨
    ColouredSafeEndpointHammock.IsImaginary
      C.ladder.limitWarp (CapturedByStageRoof C.ladder) kappa x y

def web (C : ClubStageGeometry Gamma Y kappa (succ kappa)) : DWeb V where
  graph := graph C
  source := Gamma.source
  target := Gamma.target

def marked (C : ClubStageGeometry Gamma Y kappa (succ kappa)) : V → V → Prop :=
  ColouredSafeEndpointHammock.IsMarked C.ladder.limitWarp (CapturedByStageRoof C.ladder) kappa

def popular (C : ClubStageGeometry Gamma Y kappa (succ kappa)) : Set V :=
  {x | ColouredSafeEndpointHammock.IsPopular
    C.ladder.limitWarp (CapturedByStageRoof C.ladder) C.persistent kappa x}

structure IsBlueprint (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a : Stage (succ kappa)) (W : Set (web C).DPath) : Prop where
  isWarp : (web C).IsWarp W
  vertices_roofed : (web C).vertexSet W ⊆ Gamma.roof (C.ladder.frontier a)
  covers_source : Gamma.source ⊆ (web C).initialSet W ∪ Gamma.initialSet
    (referencePathsMeeting C.ladder.limitWarp (C.ladder.frontier a) \
      referencePathsMeeting C.ladder.limitWarp ((web C).vertexSet W))
  vertices_working : (web C).vertexSet W ⊆ C.ladder.limitRoof
  card_paths : #W ≤ kappa
  infinitely_many_marked : (web C).InfinitelyManyMarkedEdges W (marked C)
  terminals_popular : (web C).terminalFrontier W ⊆ popular C ∪ C.ladder.frontier a

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {a : Stage (succ kappa)}
variable {W : Set (web C).DPath}

theorem real_adj {x y : V} (h : Gamma.graph.Adj x y) : (web C).graph.Adj x y := Or.inl h

theorem IsBlueprint.card_vertices (hW : IsBlueprint C a W) :
    #((web C).vertexSet W) ≤ kappa :=
  CardinalInduction.HalfwayFrontierHeight.mk_vertexSet_le_of_mk_family_le
    C.capacity_infinite W hW.card_paths

/-- The explicit working-region field follows from the actual fixed-stage
roof, independently of any small auxiliary closing set. -/
theorem of_roofed_fields (hW : (web C).IsWarp W)
    (hroof : (web C).vertexSet W ⊆ Gamma.roof (C.ladder.frontier a))
    (hcover : Gamma.source ⊆ (web C).initialSet W ∪ Gamma.initialSet
      (referencePathsMeeting C.ladder.limitWarp (C.ladder.frontier a) \
        referencePathsMeeting C.ladder.limitWarp ((web C).vertexSet W)))
    (hcard : #((web C).vertexSet W) ≤ kappa)
    (hmarked : (web C).InfinitelyManyMarkedEdges W (marked C))
    (hterminal : (web C).terminalFrontier W ⊆ popular C ∪ C.ladder.frontier a) :
    IsBlueprint C a W where
  isWarp := hW
  vertices_roofed := hroof
  covers_source := hcover
  vertices_working := fun _ hx ↦ Set.mem_iUnion.mpr ⟨a, hroof hx⟩
  card_paths := (ColouredSafeShortcutGraph.mk_paths_le_vertexSet hW).trans hcard
  infinitely_many_marked := hmarked
  terminals_popular := hterminal

/-- A new small closing set and its later club stage are chosen from the
actual current carrier, before any future interval row is available. -/
theorem IsBlueprint.exists_movingClosure_above (hW : IsBlueprint C a W)
    (lower : Stage (succ kappa)) :
    ∃ R : ColouredSafeEndpointMovingStages.LimitClosure C ((web C).vertexSet W),
      lower < R.later.stage :=
  ColouredSafeEndpointMovingStages.LimitClosure.exists_of_seed_above C _ lower
    hW.card_vertices hW.vertices_working

#print axioms IsBlueprint.card_vertices
#print axioms of_roofed_fields
#print axioms IsBlueprint.exists_movingClosure_above

end Erdos599.Blueprint.ColouredSafeEndpointBlueprint
