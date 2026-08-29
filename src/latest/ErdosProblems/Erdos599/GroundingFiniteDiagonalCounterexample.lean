/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingObstructionCharacterization
import ErdosProblems.Erdos599.LadderExistence
import ErdosProblems.Erdos599.LadderExhaustionLoose

/-!
# A zero-stage counterexample to unconditional finite-diagonal classification

The one-vertex web below has one source, no edges, and empty target.  Its
canonical `aleph-one` ladder is legal, but the unique source path is already
an inessential finite path at the first successor stage.  The stage web has
empty source, hence its rung cannot be a hindrance.  Thus diagonal emergence
alone does not imply membership in `phiHindrance`.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

private def zeroTargetUnitWeb : DWeb Unit where
  graph := ⟨fun _ _ ↦ False⟩
  source := Set.univ
  target := ∅

private abbrev counterKappa : Cardinal := ℵ₁

private noncomputable abbrev counterLadder :
    zeroTargetUnitWeb.KappaLadder counterKappa :=
  KappaLadder.canonicalLadder zeroTargetUnitWeb counterKappa (fun _ ↦ none)

private def zeroCounterStage : Ladder.Stage counterKappa :=
  ⟨0, Cardinal.isRegular_aleph_one.ord_pos⟩

private abbrev zeroCounterPath : zeroTargetUnitWeb.DPath :=
  zeroTargetUnitWeb.trivialPath ()

theorem zeroTargetUnitWeb_isNormalized : zeroTargetUnitWeb.IsNormalized := by
  intro x y hxy
  exact hxy.elim

private theorem zeroTargetUnitWeb_noAdj {x y : Unit} :
    zeroTargetUnitWeb.graph.Adj x y → False := by
  intro hxy
  exact hxy

private theorem zeroTargetUnitWeb_essential_eq_empty (S : Set Unit) :
    zeroTargetUnitWeb.essential S = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  apply hx.2
  intro p hp
  exact hp.2.elim

private theorem counterLadder_isLegal : counterLadder.IsLegal := by
  apply KappaLadder.canonicalLadderWithBookkeeping_isLegal
  · exact Cardinal.isRegular_aleph_one
  · exact Cardinal.aleph0_lt_aleph_one
  · intro x y hxy hy
    exact hxy.elim

private theorem counter_stageWeb_source_empty :
    (counterLadder.stageWeb zeroCounterStage).source = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  exact hx.2.choose_spec.2.elim

private theorem zeroCounterPath_mem_warpAt :
    zeroCounterPath ∈ counterLadder.warpAt zeroCounterStage := by
  have hzero : Ladder.Stage.toExtended zeroCounterStage =
      Ladder.zeroStage counterKappa := by
    exact Subtype.ext rfl
  change zeroCounterPath ∈ counterLadder.accumulated
    (Ladder.Stage.toExtended zeroCounterStage)
  rw [hzero, counterLadder_isLegal.initialStage]
  exact ⟨(), Set.mem_univ (), rfl⟩

private theorem zeroCounterPath_mem_successorWarp :
    zeroCounterPath ∈ counterLadder.successorWarp zeroCounterStage := by
  obtain ⟨q, hq, hpq⟩ := counterLadder_isLegal.successorExtensions
    zeroCounterStage zeroCounterPath zeroCounterPath_mem_warpAt
  have hqtrivial : q = zeroTargetUnitWeb.trivialPath q.initial :=
    zeroTargetUnitWeb.path_eq_trivialPath_of_not_adj
      zeroTargetUnitWeb_noAdj q
  have hqunit : q.initial = () := Subsingleton.elim _ _
  have hqp : q = zeroCounterPath := by
    simpa only [zeroCounterPath, hqunit] using hqtrivial
  exact hqp ▸ hq

private theorem zeroCounterPath_mem_inessentialNext :
    zeroCounterPath ∈
      zeroTargetUnitWeb.inessentialPaths
        (counterLadder.successorWarp zeroCounterStage) := by
  refine ⟨zeroCounterPath_mem_successorWarp, ?_⟩
  rintro ⟨_, t, _ht, htEssential⟩
  rw [zeroTargetUnitWeb_essential_eq_empty] at htEssential
  exact htEssential

private theorem counter_markerCandidates_empty :
    counterLadder.markerCandidates zeroCounterStage = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  exact hx.1.1.choose_spec.2.elim

private theorem counter_marker_none :
    counterLadder.marker zeroCounterStage = none := by
  exact (counterLadder_isLegal.freshMarkers.1 zeroCounterStage).2
    counter_markerCandidates_empty

private theorem zeroCounterPath_not_recordedBefore :
    zeroCounterPath ∉ counterLadder.bookkeeping.recordedBefore zeroCounterStage := by
  rintro ⟨b, hb, _⟩
  exact (not_lt_of_ge (bot_le : (0 : Ordinal) ≤ b.1)) hb

private theorem zeroCounterPath_mem_available :
    zeroCounterPath ∈ counterLadder.bookkeeping.available zeroCounterStage := by
  refine ⟨⟨zeroCounterPath_mem_inessentialNext,
    zeroCounterPath_not_recordedBefore⟩, ?_⟩
  change zeroCounterPath ∉ counterLadder.markerPathSet zeroCounterStage
  rw [KappaLadder.markerPathSet, counter_marker_none]
  simp only [Set.mem_empty_iff_false, not_false_eq_true]

private theorem counter_chosen_zero :
    counterLadder.chosen zeroCounterStage = some zeroCounterPath := by
  obtain ⟨q, hqChosen, _hqAvailable, _⟩ :=
    (counterLadder_isLegal.validBookkeeping zeroCounterStage).1
      ⟨zeroCounterPath, zeroCounterPath_mem_available⟩
  have hqtrivial : q = zeroTargetUnitWeb.trivialPath q.initial :=
    zeroTargetUnitWeb.path_eq_trivialPath_of_not_adj
      zeroTargetUnitWeb_noAdj q
  have hqunit : q.initial = () := Subsingleton.elim _ _
  have hqp : q = zeroCounterPath := by
    simpa only [zeroCounterPath, hqunit] using hqtrivial
  exact hqp ▸ hqChosen

private theorem zeroCounterStage_mem_phi :
    zeroCounterStage ∈ counterLadder.phi := by
  exact (counterLadder.bookkeeping.mem_phi_iff_exists_chosen
    counterLadder_isLegal.validBookkeeping).2
      ⟨zeroCounterPath, counter_chosen_zero⟩

private theorem counter_emergenceIndex_zero :
    counterLadder.emergenceIndex
      counterLadder_isLegal.validBookkeeping zeroCounterStage =
        zeroCounterStage := by
  apply le_antisymm
  · exact counterLadder.emergenceIndex_le
      counterLadder_isLegal.validBookkeeping zeroCounterStage_mem_phi
  · change (0 : Ordinal) ≤ _
    exact bot_le

private theorem zeroCounterStage_mem_diagonalEmergenceStages :
    zeroCounterStage ∈
      counterLadder.diagonalEmergenceStages counterLadder_isLegal :=
  ⟨zeroCounterStage_mem_phi, counter_emergenceIndex_zero⟩

private theorem zeroCounterStage_not_mem_phiHindrance :
    zeroCounterStage ∉ counterLadder.phiHindrance := by
  intro hhindrance
  apply hhindrance.2
  apply Set.Subset.antisymm hhindrance.1.2.1
  intro x hx
  rw [counter_stageWeb_source_empty] at hx
  exact hx.elim

/-- The concrete zero-stage data refute finite-diagonal classification for
the legal canonical ladder on the normalized one-source, empty-target web. -/
theorem counterLadder_not_finiteDiagonalEmergenceClassified :
    ¬ counterLadder.FiniteDiagonalEmergenceClassified
      counterLadder_isLegal := by
  intro hclassified
  exact zeroCounterStage_not_mem_phiHindrance
    (hclassified zeroCounterStage
      zeroCounterStage_mem_diagonalEmergenceStages
      zeroCounterPath () counter_chosen_zero rfl)

/-- There is a normalized web and a fully legal `aleph-one` ladder for which
unconditional finite-diagonal classification is false.  The legality proof
is quantified explicitly because `FiniteDiagonalEmergenceClassified` is
indexed by that proof. -/
theorem exists_normalized_legal_not_finiteDiagonalEmergenceClassified :
    ∃ (Gamma : DWeb Unit)
      (L : Gamma.KappaLadder (ℵ₁ : Cardinal))
      (hlegal : L.IsLegal),
        Gamma.IsNormalized ∧
          ¬ L.FiniteDiagonalEmergenceClassified hlegal := by
  exact ⟨zeroTargetUnitWeb, counterLadder, counterLadder_isLegal,
    zeroTargetUnitWeb_isNormalized,
    counterLadder_not_finiteDiagonalEmergenceClassified⟩

#print axioms exists_normalized_legal_not_finiteDiagonalEmergenceClassified

end DWeb
end Erdos599
