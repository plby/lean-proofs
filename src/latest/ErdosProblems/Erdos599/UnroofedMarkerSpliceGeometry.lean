/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerGrounding
import ErdosProblems.Erdos599.SliceSpliceConstructor
import ErdosProblems.Erdos599.LadderLemma76

/-!
# Splice geometry and a club of unhindered stages for the actual ladder

All generic splice geometry comes from the unroofed-marker construction.
Its actual Lemma 7.6 data puts every hindered stage in the obstruction set.
The completed grounding theorem therefore supplies a club of unhindered
stages, without identifying this ladder with the historical marker rule.
-/

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Order Ladder KappaLadder

universe u

variable {V : Type u} (G : DWeb V) (kappa : Cardinal.{u})
  (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)

include hNoEnter in
theorem ladder_spliceGeometry (hkappa : kappa.IsRegular) :
    CardinalInduction.SliceSpliceConstructor.SpliceLadderGeometry G
      (ladder G kappa preferred) := by
  have hg := ladder_geometry G kappa preferred hNoEnter
  exact ⟨hkappa, ladder_hasInitialStage G kappa preferred, hg.limitStages, hg.warpStages,
    (ladder G kappa preferred).frontiersAreEssential_of_roofsSourceAtStages hg.roofsSourceAtStages,
    hg.frontierChronology, ladder_hasStrictFrontierChronology G kappa preferred hNoEnter⟩

include hNoEnter in
theorem ladder_lemma76Data : (ladder G kappa preferred).Lemma76Data :=
  ⟨ladder_hasWaveRungs G kappa preferred,
    ladder_hasExactSuccessorArrows G kappa preferred hNoEnter,
    (ladder_geometry G kappa preferred hNoEnter).roofsSourceAtStages,
    ladder_recordedPathsPersist G kappa preferred hNoEnter⟩

include hNoEnter in
theorem ladder_stage_unhindered_of_not_mem_phi (hNorm : G.IsNormalized)
    {a : Stage kappa} (ha : a ∉ (ladder G kappa preferred).phi) :
    ((ladder G kappa preferred).stageWeb a).IsUnhindered := by
  by_contra hh
  apply ha
  apply phiHindrance_subset_phi_of_lemma76Data hNorm
    (ladder_lemma76Data G kappa preferred hNoEnter)
  exact ((ladder G kappa preferred).stageWeb a).chosenMaximalWave_isHindrance_of_not_isUnhindered hh

include hNoEnter in
theorem exists_club_unhindered_stages (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized) (hG : G.IsUnhindered) :
    ∃ C : Set (Stage kappa), Stationary.IsClubBelow kappa C ∧
      Disjoint C (ladder G kappa preferred).phi ∧
      ∀ a ∈ C, ((ladder G kappa preferred).stageWeb a).IsUnhindered := by
  obtain ⟨C, hC, hdisj⟩ := not_isStationary_iff.mp
    (ladder_phi_not_stationary G kappa preferred hNoEnter hkappa huncountable hG)
  refine ⟨C, hC, hdisj.symm, ?_⟩
  intro a ha
  apply ladder_stage_unhindered_of_not_mem_phi G kappa preferred hNoEnter hNorm
  exact fun hphi ↦ Set.disjoint_left.mp hdisj hphi ha

#print axioms ladder_spliceGeometry
#print axioms ladder_lemma76Data
#print axioms ladder_stage_unhindered_of_not_mem_phi
#print axioms exists_club_unhindered_stages

end Erdos599.DWeb.UnroofedMarker
