/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerCausal
import ErdosProblems.Erdos599.UnroofedHalfwayGeometry
import ErdosProblems.Erdos599.UnroofedDeferredInstallation

/-!
# Actual unroofed ladder inputs for the half-way causal rows

The prior scheduler is unchanged. Both prior and final graph constructions
use the unroofed protocol. Deferred reinstallation changes no actual data;
no equality with the historical canonical ladder is asserted.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.UnroofedHalfwayRowLadder

open Set Cardinal Ladder CardinalInduction.RegularRows

universe u

variable {V : Type u}

abbrev core (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) : G.KappaLadder kappa :=
  DWeb.UnroofedMarker.ladder G kappa preferred

def deferred (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) : G.KappaLadder kappa :=
  DWeb.KappaLadder.Deferred.withValidBookkeeping (core G kappa preferred)

def priorLadder (G : DWeb V) {kappa : Cardinal.{u}}
    (a : Stage kappa) (prior : ∀ b : Stage kappa, b < a → CausalState kappa V) :
    G.KappaLadder kappa :=
  core G kappa (CausalRegular.preferredOfPrior a prior)

theorem core_warpAt_eq_of_forall_lt (G : DWeb V) {kappa : Cardinal.{u}}
    (p q : Stage kappa → Option V) (a : Stage kappa)
    (h : ∀ b, b < a → p b = q b) :
    (core G kappa p).warpAt a = (core G kappa q).warpAt a :=
  DWeb.UnroofedMarker.warpAt_eq_of_forall_lt G kappa p q a h

theorem core_frontier_eq_of_forall_lt (G : DWeb V) {kappa : Cardinal.{u}}
    (p q : Stage kappa → Option V) (a : Stage kappa)
    (h : ∀ b, b < a → p b = q b) :
    (core G kappa p).frontier a = (core G kappa q).frontier a :=
  DWeb.UnroofedMarker.frontier_eq_of_forall_lt G kappa p q a h

theorem core_warpAt_isWarp_of_normalized (G : DWeb V) (hG : G.IsNormalized)
    (kappa : Cardinal.{u}) (preferred : Stage kappa → Option V) (a : Stage kappa) :
    G.IsWarp ((core G kappa preferred).warpAt a) := by
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hG hxy).1 hy
  exact (DWeb.UnroofedMarker.ladder_geometry G kappa preferred hNoEnter).warpStages
    (Stage.toExtended a)

theorem deferred_eq_core (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source) :
    deferred G kappa preferred = core G kappa preferred :=
  DWeb.UnroofedMarker.deferred_withValidBookkeeping_ladder_eq G kappa preferred hNoEnter

theorem deferred_halfwayGeometry {G : DWeb V} {kappa : Cardinal.{u}}
    (preferred : Stage kappa → Option V)
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source) :
    DWeb.KappaLadder.Deferred.HalfwayGeometry (deferred G kappa preferred) := by
  rw [deferred_eq_core G kappa preferred hNoEnter]
  exact DWeb.UnroofedMarker.ladder_halfwayGeometry
    G kappa preferred hNoEnter hregular huncountable

/-- Literal history is determined by the strict-prior record and marker streams. -/
theorem history_eq_of_chosen_marker_eq {G : DWeb V} {kappa : Cardinal.{u}}
    (P F : G.KappaLadder kappa) (a : Stage kappa)
    (hchosen : ∀ b, b < a → P.chosen b = F.chosen b)
    (hmarker : ∀ b, b < a → P.marker b = F.marker b) :
    G.vertexSet ((DWeb.KappaLadder.Deferred.bookkeeping P).recordedBefore a) ∪
        P.markerSetBelow a =
      G.vertexSet ((DWeb.KappaLadder.Deferred.bookkeeping F).recordedBefore a) ∪
        F.markerSetBelow a := by
  have hrecords : (DWeb.KappaLadder.Deferred.bookkeeping P).recordedBefore a =
      (DWeb.KappaLadder.Deferred.bookkeeping F).recordedBefore a := by
    ext p
    change (∃ b, b < a ∧ P.chosen b = some p) ↔
      (∃ b, b < a ∧ F.chosen b = some p)
    constructor <;> rintro ⟨b, hba, hp⟩
    · exact ⟨b, hba, (hchosen b hba).symm.trans hp⟩
    · exact ⟨b, hba, (hchosen b hba).trans hp⟩
  have hmarkers : P.markerSetBelow a = F.markerSetBelow a := by
    ext x
    constructor <;> rintro ⟨b, hba, hx⟩
    · exact ⟨b, hba, (hmarker b hba).symm.trans hx⟩
    · exact ⟨b, hba, (hmarker b hba).trans hx⟩
  rw [hrecords, hmarkers]

#print axioms history_eq_of_chosen_marker_eq
#print axioms core_warpAt_eq_of_forall_lt
#print axioms core_warpAt_isWarp_of_normalized
#print axioms deferred_halfwayGeometry

end Erdos599.Blueprint.LinkageBlueprint.UnroofedHalfwayRowLadder
