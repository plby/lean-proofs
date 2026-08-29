/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerStationarity
import ErdosProblems.Erdos599.UnroofedMarkerPortBarrier

/-!
# Concrete reference and record data for all-marker grounding

The final warp has exactly the original sources and the inserted markers
as its initial vertices, and those two sets are disjoint. Grounded records
are represented by actual paths, keeping their carrier in the original
vertex universe. Their chosen-stage map is injective with exactly the
grounded obstruction stages as its range; those paths are inessential
members of the actual final warp.

These data do not assert the still-unfinished fragmentwise grounding
criterion or an ordinary hindrance.
-/

noncomputable section

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Order Ladder KappaLadder

universe u

variable {V : Type u}

/-- There are no unexplained new initial vertices in the final warp, and
none of the original initials or inserted markers is lost at a limit. -/
theorem ladder_initialSet_limitWarp (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source) :
    G.initialSet (ladder G kappa preferred).limitWarp =
      G.source ∪ (ladder G kappa preferred).markerSet := by
  let L := ladder G kappa preferred
  have hgeometry := ladder_geometry G kappa preferred hNoEnter
  apply Set.Subset.antisymm
  · rintro x ⟨p, hp, hpx⟩
    rcases ladder_hasAccumulatedInitialProvenance G kappa preferred hNoEnter
        (finalStage kappa) p hp with hsource | ⟨a, _, hmarker⟩
    · exact Or.inl (hpx ▸ hsource)
    · exact Or.inr ⟨a, by simpa only [hpx] using hmarker⟩
  · rintro x (hx | ⟨a, hmarker⟩)
    · have hxZero : x ∈ G.initialSet (L.accumulated (zeroStage kappa)) := by
        rw [ladder_hasInitialStage G kappa preferred, G.initialSet_trivialWave]
        exact hx
      obtain ⟨p, hp, hpx⟩ := hxZero
      obtain ⟨q, hq, hpq⟩ := hgeometry.grows
        (a := zeroStage kappa) (b := finalStage kappa)
        (by change (0 : Ordinal.{u}) ≤ kappa.ord; exact bot_le) p hp
      exact ⟨q, hq, (G.extends_initial hpq).symm.trans hpx⟩
    · have hxNext : G.trivialPath x ∈ L.successorWarp a :=
        markerAt_trivial_mem_successor G (extendLadderPreference kappa preferred) hmarker
      obtain ⟨q, hq, hpq⟩ := hgeometry.grows
        (a := Stage.succExtended a) (b := finalStage kappa)
        (Stage.succExtended a).2 (G.trivialPath x) hxNext
      exact ⟨q, hq, (G.extends_initial hpq).symm⟩

theorem ladder_source_disjoint_markers (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source) :
    Disjoint G.source (ladder G kappa preferred).markerSet := by
  apply Set.disjoint_left.mpr
  rintro y hy ⟨a, ha⟩
  have hinv := state_invariant G (extendLadderPreference kappa preferred) hNoEnter a.1
  have hyRoof := G.roof_terminalFrontier_subset_canonicalArrow hNoEnter
    (state G (extendLadderPreference kappa preferred) a.1)
    hinv.warp hinv.selfRoof hinv.sourceRoof (hinv.sourceRoof hy)
  exact markerAt_not_mem_preMarkerRoof G (extendLadderPreference kappa preferred) ha hyRoof

/-- Actual selected paths with original-source initials. The index is
recovered from valid bookkeeping, rather than added as a second copy. -/
def GroundedRecord (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) :=
  {p : G.DPath // ∃ a : Stage kappa,
    (ladder G kappa preferred).chosen a = some p ∧ p.initial ∈ G.source}

def groundedRecordStage (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (p : GroundedRecord G kappa preferred) :
    Stage kappa := Classical.choose p.2

theorem groundedRecordStage_spec (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (p : GroundedRecord G kappa preferred) :
    (ladder G kappa preferred).chosen (groundedRecordStage G kappa preferred p) = some p.1 ∧
      p.1.initial ∈ G.source := Classical.choose_spec p.2

theorem groundedRecordStage_injective (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) :
    Function.Injective (groundedRecordStage G kappa preferred) := by
  intro p q hpq
  apply Subtype.ext
  exact Option.some.inj ((groundedRecordStage_spec G kappa preferred p).1.symm.trans
    ((congrArg (ladder G kappa preferred).chosen hpq).trans
      (groundedRecordStage_spec G kappa preferred q).1))

theorem range_groundedRecordStage (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) :
    Set.range (groundedRecordStage G kappa preferred) = (ladder G kappa preferred).phiGround := by
  ext a
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1, groundedRecordStage_spec G kappa preferred p⟩
  · rintro ⟨p, hp, hsource⟩
    let q : GroundedRecord G kappa preferred := ⟨p, a, hp, hsource⟩
    refine ⟨q, ?_⟩
    exact (ladder G kappa preferred).bookkeeping.chosen_stage_unique
      (ladder_validBookkeeping G kappa preferred)
      (groundedRecordStage_spec G kappa preferred q).1 hp

theorem groundedRecord_mem_final_inessential (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (p : GroundedRecord G kappa preferred) :
    p.1 ∈ G.inessentialPaths (ladder G kappa preferred).limitWarp :=
  ladder_recordedPathsPersist G kappa preferred hNoEnter
    (groundedRecordStage G kappa preferred p) p.1
    (groundedRecordStage_spec G kappa preferred p).1 (finalStage kappa)
    (Stage.succExtended (groundedRecordStage G kappa preferred p)).2

theorem groundedRecordStage_range_stationary (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hphi : Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi) :
    Stationary.IsStationaryBelow kappa (Set.range (groundedRecordStage G kappa preferred)) := by
  rw [range_groundedRecordStage]
  exact ladder_phiGround_isStationary G kappa preferred hNoEnter hkappa huncountable hphi

#print axioms ladder_initialSet_limitWarp
#print axioms ladder_source_disjoint_markers
#print axioms groundedRecord_mem_final_inessential
#print axioms groundedRecordStage_range_stationary

end Erdos599.DWeb.UnroofedMarker
