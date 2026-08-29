/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerRecursion

/-!
# A concrete ladder with unroofed markers and actual bookkeeping

This restricts the constructed ordinal recursion to a cardinal, and installs
the already-proved ray-preferring bookkeeping. Geometry, source separation,
frontier chronology, maximal rungs and marker uniqueness are proved for this
specific construction. No identification with the historical canonical
ladder or its stronger marker-exhaustion predicate is made.
-/

noncomputable section

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Order Ladder KappaLadder

universe u

variable {V : Type u}

def ladderCore (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) : G.KappaLadder kappa where
  accumulated a := (state G (extendLadderPreference kappa preferred) a.1).1
  rung a := G.ladderRungOfState
    (state G (extendLadderPreference kappa preferred) a.1)
  marker a := markerAt G (extendLadderPreference kappa preferred) a.1
  chosen _ := none

/-- The final construction uses ordinary successor-inessential bookkeeping.
The current marker cannot be recorded, because it is essential at insertion. -/
def ladder (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) : G.KappaLadder kappa :=
  (ladderCore G kappa preferred).withValidBookkeeping

theorem ladder_validBookkeeping (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) :
    (ladder G kappa preferred).HasValidBookkeeping :=
  (ladderCore G kappa preferred).withValidBookkeeping_hasValidBookkeeping

theorem ladder_hasInitialStage (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) :
    (ladder G kappa preferred).HasInitialStage := by
  change (state G (extendLadderPreference kappa preferred) 0).1 = G.trivialWave
  simp only [state, DWeb.ladderAccumulatedStateAux, Ordinal.limitRecOn_zero]

theorem ladder_hasWaveRungs (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) :
    (ladder G kappa preferred).HasWaveRungs := by
  intro a
  exact ((ladder G kappa preferred).stageWeb a).chosenMaximalWave.property

theorem ladder_hasRoofMaximalRungs (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) :
    (ladder G kappa preferred).HasRoofMaximalRungs := by
  intro a W hW
  exact ((ladder G kappa preferred).stageWeb a).roofLE_chosenMaximalWave W hW

/-- The structural interface includes actual threadwise limit stages. -/
theorem ladder_geometry (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V)
    (hNoEnter : G.NoEdgeEnters G.source) :
    CanonicalLadderGeometry (ladder G kappa preferred) := by
  let pref := extendLadderPreference kappa preferred
  let L := ladder G kappa preferred
  have hinv (o : Ordinal.{u}) := state_invariant G pref hNoEnter o
  have hwarp : L.HasWarpStages := fun a ↦ (hinv a.1).warp
  have hlimit : L.HasLimitStages := by
    intro a ha
    apply G.exists_ladderLimitChain kappa (step G pref) a ha
    apply G.hasMatchingLadderChain_of_invariants (step G pref) a.1
    intro b _hb
    exact ⟨(hinv b).warp, (hinv b).grows⟩
  have hroof : L.RoofsSourceAtStages := fun a ↦ (hinv a.1).sourceRoof
  have hself : ∀ a : ExtendedStage kappa,
      G.vertexSet (L.accumulated a) ⊆ G.roof (G.terminalFrontier (L.accumulated a)) :=
    fun a ↦ (hinv a.1).selfRoof
  have hgrows : ∀ {a b : ExtendedStage kappa}, a ≤ b →
      G.LadderGrows (L.accumulated a) (L.accumulated b) := by
    intro a b hab
    exact state_grows G pref hNoEnter hab
  have hchronology : L.HasFrontierChronology := by
    apply L.hasFrontierChronology_of_grows_of_selfRoofing hroof
    · intro a b hab
      exact hgrows hab.le
    · intro b
      exact hself (Stage.toExtended b)
  exact ⟨hwarp, hlimit, hroof, hself, hgrows, hchronology⟩

theorem ladder_markersInjective (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source) :
    (ladder G kappa preferred).MarkersInjective := by
  intro a b y ha hb
  apply Subtype.ext
  exact markerAt_stage_unique G (extendLadderPreference kappa preferred) hNoEnter ha hb

theorem ladder_marker_essential_successor (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) {a : Stage kappa} {y : V}
    (hy : (ladder G kappa preferred).marker a = some y) :
    y ∈ G.essential (G.terminalFrontier ((ladder G kappa preferred).successorWarp a)) :=
  markerAt_essential_successor G (extendLadderPreference kappa preferred) hy

/-- Every recorded component avoids the current marker, without imposing
that avoidance as an extra choice restriction. -/
theorem ladder_chosen_avoids_current_marker (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    {a : Stage kappa} {p : G.DPath} {y : V}
    (hp : (ladder G kappa preferred).chosen a = some p)
    (hy : (ladder G kappa preferred).marker a = some y) : y ∉ p.support := by
  let L := ladder G kappa preferred
  have hpIE : p ∈ G.inessentialPaths (L.successorWarp a) :=
    (L.bookkeeping.chosen_mem_available (ladder_validBookkeeping G kappa preferred) hp).1
  have hyMem : G.trivialPath y ∈ L.successorWarp a :=
    markerAt_trivial_mem_successor G (extendLadderPreference kappa preferred) hy
  have hyEss : G.trivialPath y ∈ G.essentialWarpPart (L.successorWarp a) :=
    ⟨hyMem, y, G.terminal?_trivialPath y,
      ladder_marker_essential_successor G kappa preferred hy⟩
  intro hyp
  exact (G.not_mem_inessentialPaths_of_intersects_essential
    ((ladder_geometry G kappa preferred hNoEnter).warpStages (Stage.succExtended a))
    hyEss ⟨y, hyp, by simp⟩) hpIE

#print axioms ladder_geometry
#print axioms ladder_markersInjective
#print axioms ladder_chosen_avoids_current_marker

end Erdos599.DWeb.UnroofedMarker
