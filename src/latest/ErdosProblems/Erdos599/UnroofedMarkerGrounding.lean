/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerLocalGrounding
import ErdosProblems.Erdos599.GroundingAllMarkerGlobalGrounding

/-!
# Actual global grounding and hindrance for the unroofed ladder

A stationary record set on the genuine unroofed ladder supplies its
popular auxiliary separator, independent transactions, leftover prefixes,
and an omitted grounded record. Their assembled path family is a finite-
character ordinary hindrance. All construction premises are discharged by
the ladder; the theorem has no grounding or extension-engine assumption.
-/

noncomputable section

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Order Ladder KappaLadder GroundingAllMarkerAuxiliary
open _root_.Erdos599.DirectedPath Alternating

universe u

variable {V : Type u} (G : DWeb V) (kappa : Cardinal.{u})
  (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
  (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
  (hphi : Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi)

local notation "A" => auxiliaryInput G kappa preferred hNoEnter
local notation "S" => auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi
local notation "hi" => auxiliary_record_initial_not_marker G kappa preferred hNoEnter
local notation "his" => auxiliary_reference_initial_profile G kappa preferred hNoEnter
local notation "hm" => ladder_source_disjoint_markers G kappa preferred hNoEnter

theorem auxiliary_records_grounded (i : GroundedRecord G kappa preferred) :
    ((A).record i).initial ∈ G.source := (groundedRecordStage_spec G kappa preferred i).2

local notation "hr" => auxiliary_records_grounded G kappa preferred hNoEnter

def auxiliaryGlobalGroundingWarp : Popular.XSWarp G
    (auxiliaryBlockingSet G kappa preferred hNoEnter hkappa huncountable hphi) :=
  (A).globalGroundingWarp S hi his hr hNoEnter hm

theorem auxiliaryGlobalGroundingWarp_covers :
    ∀ b ∈ auxiliaryBlockingSet G kappa preferred hNoEnter hkappa huncountable hphi,
      ∃ p ∈ (auxiliaryGlobalGroundingWarp G kappa preferred hNoEnter
        hkappa huncountable hphi).paths, p.finish = b :=
  (A).globalGroundingWarp_covers S hi his hr hNoEnter hm

theorem auxiliaryGlobalGroundingWarp_one_hit {p : FinitePath G.graph}
    (hp : p ∈ (auxiliaryGlobalGroundingWarp G kappa preferred hNoEnter
      hkappa huncountable hphi).paths) :
    p.support ∩ auxiliaryBlockingSet G kappa preferred hNoEnter hkappa huncountable hphi =
      {p.finish} :=
  (A).globalGroundingWarp_one_hit S hi his hr hNoEnter hm hp

def auxiliaryGroundingFamily : Set G.DPath := PopularSwitching.pathFamily
  (auxiliaryGlobalGroundingWarp G kappa preferred hNoEnter hkappa huncountable hphi)

theorem auxiliaryGroundingFamily_finiteCharacter : G.HasFiniteCharacter
    (auxiliaryGroundingFamily G kappa preferred hNoEnter hkappa huncountable hphi) := by
  rintro p ⟨q, _hq, rfl⟩
  exact ⟨q, rfl⟩

theorem auxiliaryGroundingFamily_terminalFrontier : G.terminalFrontier
    (auxiliaryGroundingFamily G kappa preferred hNoEnter hkappa huncountable hphi) =
      auxiliaryBlockingSet G kappa preferred hNoEnter hkappa huncountable hphi :=
  PopularSwitching.pathFamily_terminalFrontier_eq _
    (auxiliaryGlobalGroundingWarp_covers G kappa preferred hNoEnter hkappa huncountable hphi)

theorem auxiliaryGroundingFamily_isHindrance : G.IsHindrance
    (auxiliaryGroundingFamily G kappa preferred hNoEnter hkappa huncountable hphi) := by
  refine ⟨PopularSwitching.pathFamily_isWave _
    (auxiliaryGlobalGroundingWarp_covers G kappa preferred hNoEnter hkappa huncountable hphi)
    (auxiliaryBlockingSet_separates G kappa preferred hNoEnter hkappa huncountable hphi), ?_⟩
  obtain ⟨i, hiUntouched, hiSource, _hiK⟩ :=
    exists_untouched_grounded_record G kappa preferred hNoEnter hkappa huncountable hphi
  intro heq
  have hiInitial : i.1.initial ∈ G.initialSet
      (auxiliaryGroundingFamily G kappa preferred hNoEnter hkappa huncountable hphi) :=
    heq.symm ▸ hiSource
  obtain ⟨p, ⟨q, hq, rfl⟩, hqi⟩ := hiInitial
  have hstart : q.start = i.1.initial := hqi
  exact Set.disjoint_left.mp
    ((A).globalGroundingWarp_avoids_untouched S hi his hr hNoEnter hm i hiUntouched hq)
    q.start_mem_support (hstart.symm ▸ i.1.initial_mem_support)

include hNoEnter hkappa huncountable in
/-- Unconditional nonstationarity for the actual unroofed ladder in an
unhindered source-normalized web. No supplied grounding engine is needed. -/
theorem ladder_phi_not_stationary (hG : G.IsUnhindered) :
    ¬ Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi := by
  intro hstat
  exact hG ⟨auxiliaryGroundingFamily G kappa preferred hNoEnter hkappa huncountable hstat,
    auxiliaryGroundingFamily_isHindrance G kappa preferred hNoEnter hkappa huncountable hstat⟩

#print axioms auxiliaryGlobalGroundingWarp_covers
#print axioms auxiliaryGlobalGroundingWarp_one_hit
#print axioms auxiliaryGroundingFamily_finiteCharacter
#print axioms auxiliaryGroundingFamily_isHindrance
#print axioms ladder_phi_not_stationary

end Erdos599.DWeb.UnroofedMarker
