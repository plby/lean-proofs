/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCausalEndpointTargetExtension

/-!
# Reusable contained successor at an arbitrary later club stage

The local geometry is reindexed without changing its ladder or augmented
graph. Its bounded local bookkeeping is the current small carrier, not an
assertion that this carrier is already hammock closed. The target successor
still constructs the actual contained moving closure afterwards.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint

open Set Cardinal Order DirectedPath Ladder
open _root_.Erdos599.Alternating
open ColouredSafeEndpointBlueprint
open _root_.Erdos599.ColouredSafeLocalTransactionRealLedger
open _root_.Erdos599.ColouredSafeAugmentedRealReach

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

def ClubStageGeometry.rebaseCurrent
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a : Stage (succ kappa)) (ha : a ∈ C.club) (haOld : C.oldStage < a)
    (X : Set V) (hX : #X ≤ kappa) : ClubStageGeometry Gamma Y kappa (succ kappa) where
  ladder := C.ladder
  legal := C.legal
  hindranceRungs := C.hindranceRungs
  hindranceObstruction := C.hindranceObstruction
  normalized := C.normalized
  club := C.club
  club_isClub := C.club_isClub
  club_avoids_phi := C.club_avoids_phi
  oldStage := C.oldStage
  newStage := a
  old_mem_club := C.old_mem_club
  new_mem_club := ha
  old_lt_new := haOld
  closedStage := fun _ ↦ X
  closedStage_mono := fun _ ↦ Set.Subset.rfl
  before_card := (Cardinal.mk_subtype_mono (by
    rintro x ⟨b, _hb, hx⟩
    exact hx)).trans hX
  capacity_infinite := C.capacity_infinite

@[simp] theorem ClubStageGeometry.web_rebaseCurrent
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a : Stage (succ kappa)) (ha : a ∈ C.club) (haOld : C.oldStage < a)
    (X : Set V) (hX : #X ≤ kappa) : web (C.rebaseCurrent a ha haOld X hX) = web C := rfl

theorem ClubStageGeometry.isBlueprint_rebaseCurrent_iff
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a : Stage (succ kappa)) (ha : a ∈ C.club) (haOld : C.oldStage < a)
    (X : Set V) (hX : #X ≤ kappa) (b : Stage (succ kappa)) (W : Set (web C).DPath) :
    IsBlueprint (C.rebaseCurrent a ha haOld X hX) b W ↔ IsBlueprint C b W := by
  constructor <;> intro h
  · exact ⟨h.isWarp, h.vertices_roofed, h.covers_source, h.vertices_working,
      h.card_paths, h.infinitely_many_marked, h.terminals_popular⟩
  · exact ⟨h.isWarp, h.vertices_roofed, h.covers_source, h.vertices_working,
      h.card_paths, h.infinitely_many_marked, h.terminals_popular⟩

namespace CausalSection9Rows

theorem exists_endpointAdvance_to_target_at
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hC : C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed)
    {a : Stage (succ kappa)} (ha : a ∈ C.club) (haOld : C.oldStage < a)
    {W : Set (web C).DPath} (hW : IsBlueprint C a W)
    (hWZ : (web C).vertexSet W ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed)
    (hstable : (web C).terminalFrontier W ∩ C.ladder.frontier a ⊆ C.persistent)
    (hext : _root_.Erdos599.CardinalInduction.ProtectedCardinalAssembly.ExtensionThroughFor
      Gamma kappa) (hsub : HasHereditarySubdivisionIncidence Gamma.graph)
    {s : V} (hs : s ∈ (web C).vertexSet W) :
    ∃ (b : Stage (succ kappa)) (Q : Set (web C).DPath),
      b ∈ C.club ∧ a < b ∧ IsBlueprint C b Q ∧
      (web C).vertexSet Q ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed ∧
      (web C).vertexSet W ⊆ (web C).vertexSet Q ∧
      RealEdges (Gamma := web C) Gamma.graph.Adj W ⊆
        RealEdges (Gamma := web C) Gamma.graph.Adj Q ∧
      (web C).initialSet W ⊆ (web C).initialSet Q ∧
      (web C).terminalFrontier Q ⊆ popular C ∧
      (web C).terminalFrontier Q ∩ C.ladder.frontier b ⊆ C.persistent ∧
      RealReaches Gamma (web C) Q s Gamma.target ∧
      FullAccount Gamma (web C) W Q Gamma.target ∧
      (∀ x, IsRealTerminal (Gamma := web C) Gamma.graph.Adj W x →
        IsRealTerminal (Gamma := web C) Gamma.graph.Adj Q x ∨
          RealReaches Gamma (web C) Q x Gamma.target) ∧
      SourcePredecessorRefines Gamma (web C) W Q := by
  let C' := C.rebaseCurrent a ha haOld ((web C).vertexSet W) hW.card_vertices
  have hW' : IsBlueprint C' a W :=
    (C.isBlueprint_rebaseCurrent_iff a ha haOld _ hW.card_vertices a W).mpr hW
  obtain ⟨b, Q, hb, hab, hQ, hrest⟩ :=
    exists_endpointAdvance_to_target hkappa hGamma hseed C' hC hW' hWZ hstable hext hsub hs
  exact ⟨b, Q, hb, hab,
    (C.isBlueprint_rebaseCurrent_iff a ha haOld _ hW.card_vertices b Q).mp hQ, hrest⟩

end CausalSection9Rows

#print axioms ClubStageGeometry.web_rebaseCurrent
#print axioms ClubStageGeometry.isBlueprint_rebaseCurrent_iff
#print axioms CausalSection9Rows.exists_endpointAdvance_to_target_at

end Erdos599.Blueprint.LinkageBlueprint
