/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedHalfwayGeometry
import ErdosProblems.Erdos599.HalfwayClubGeometry

/-!
# Club-stage geometry on the actual unroofed ladder

The club comes from the proved actual obstruction theorem. The resulting
record retains the exact ladder and supplied bounded closing family.
There is no assumed deferred-grounding implication and no identification
with the historical canonical marker protocol.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.UnroofedHalfwayClub

open Set Cardinal Order Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

theorem exists_clubStageGeometry
    (hkappa : aleph0 ≤ kappa) (hNorm : Gamma.IsNormalized) (hG : Gamma.IsUnhindered)
    (preferred : Stage (succ kappa) → Option V)
    (closedStage : Stage (succ kappa) → Set V)
    (hmono : ∀ {a b}, a ≤ b → closedStage a ⊆ closedStage b)
    (hcard : ∀ a, #(closedStage a) ≤ kappa) :
    ∃ C : ClubStageGeometry Gamma Y kappa (succ kappa),
      C.ladder = DWeb.UnroofedMarker.ladder Gamma (succ kappa) preferred ∧
      C.closedStage = closedStage := by
  let L := DWeb.UnroofedMarker.ladder Gamma (succ kappa) preferred
  have hregular : (succ kappa).IsRegular := Cardinal.isRegular_succ hkappa
  have huncountable : aleph0 < succ kappa := hkappa.trans_lt (lt_succ kappa)
  have hNoEnter : Gamma.NoEdgeEnters Gamma.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L :=
    DWeb.UnroofedMarker.ladder_halfwayGeometry Gamma (succ kappa) preferred
      hNoEnter hregular huncountable
  obtain ⟨Sigma, hSigma, havoid, _hstage⟩ :=
    DWeb.UnroofedMarker.exists_deferred_club_unhindered_stages Gamma (succ kappa) preferred
      hNoEnter hregular huncountable hNorm hG
  let zero : Stage (succ kappa) := ⟨0, hregular.ord_pos⟩
  let oldStage := RegularCardinal.nextInClub hregular Sigma hSigma zero
  let newStage := RegularCardinal.nextInClub hregular Sigma hSigma oldStage
  let C : ClubStageGeometry Gamma Y kappa (succ kappa) :=
    { ladder := L
      legal := hL
      hindranceRungs := fun a hh ↦
        (L.stageWeb a).chosenMaximalWave_isHindrance_of_not_isUnhindered hh
      hindranceObstruction := DWeb.UnroofedMarker.ladder_deferred_phiHindrance_subset_phi
        Gamma (succ kappa) preferred hNoEnter hNorm
      normalized := hNorm
      club := Sigma
      club_isClub := hSigma
      club_avoids_phi := havoid
      oldStage := oldStage
      newStage := newStage
      old_mem_club := RegularCardinal.nextInClub_mem hregular Sigma hSigma zero
      new_mem_club := RegularCardinal.nextInClub_mem hregular Sigma hSigma oldStage
      old_lt_new := RegularCardinal.lt_nextInClub hregular Sigma hSigma oldStage
      closedStage := closedStage
      closedStage_mono := hmono
      before_card := ClubStageGeometry.mk_closedBefore_le closedStage hmono hcard newStage
      capacity_infinite := hkappa }
  exact ⟨C, rfl, rfl⟩

theorem exists_clubStageGeometry_of_constant
    (hkappa : aleph0 ≤ kappa) (hNorm : Gamma.IsNormalized) (hG : Gamma.IsUnhindered)
    (preferred : Stage (succ kappa) → Option V) (base : Set V) (hbase : #base ≤ kappa) :
    ∃ C : ClubStageGeometry Gamma Y kappa (succ kappa),
      C.ladder = DWeb.UnroofedMarker.ladder Gamma (succ kappa) preferred ∧
      C.closedStage = (fun _ ↦ base) :=
  exists_clubStageGeometry hkappa hNorm hG preferred (fun _ ↦ base)
    (fun {_ _} _ ↦ Set.Subset.rfl) (fun _ ↦ hbase)

#print axioms exists_clubStageGeometry
#print axioms exists_clubStageGeometry_of_constant

end Erdos599.Blueprint.LinkageBlueprint.UnroofedHalfwayClub
