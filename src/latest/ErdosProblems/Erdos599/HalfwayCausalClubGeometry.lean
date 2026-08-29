/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedHalfwayClub
import ErdosProblems.Erdos599.HalfwayCausalGlobalHammockClosure

/-!
# Club geometry on the actual causal Section 9 ladder

The actual unroofed obstruction theorem supplies the avoiding club. The
record retains the exact final causal ladder, so all previously proved row,
reference and hammock certificates apply to the same construction.
No canonical deferred-grounding implication is assumed.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace CausalSection9Rows

/-- Build the club-stage geometry on the actual final causal ladder from a
specified avoiding club.  Besides preserving the ladder definitionally, the
conclusion records the chosen club and closing family, so downstream causal
closure theorems require no transport through an unspecified `Nonempty` witness. -/
theorem exists_clubStageGeometry_of_avoidingClub
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (Sigma : Set (Ladder.Stage (succ kappa)))
    (hSigma : Stationary.IsClubBelow (succ kappa) Sigma)
    (havoid : Disjoint Sigma
      (DWeb.KappaLadder.Deferred.phi
        (finalLadder Gamma kappa hkappa hGamma seed hseed)))
    (closedStage : Ladder.Stage (succ kappa) → Set V)
    (hmono : ∀ {a b}, a ≤ b → closedStage a ⊆ closedStage b)
    (hcard : ∀ a, #(closedStage a) ≤ kappa) :
    ∃ C : ClubStageGeometry Gamma Y kappa (succ kappa),
      C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed ∧
      C.club = Sigma ∧ C.closedStage = closedStage := by
  let L := finalLadder Gamma kappa hkappa hGamma seed hseed
  let hsucc : aleph0 ≤ succ kappa := hkappa.trans (le_succ kappa)
  let preferred :=
    (rule Gamma kappa hkappa hGamma seed hseed).preferred hsucc
  have hregular : (succ kappa).IsRegular := Cardinal.isRegular_succ hkappa
  have hNoEnter : Gamma.NoEdgeEnters Gamma.source := by
    intro x y hxy hy
    exact (hGamma hxy).1 hy
  have hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L :=
    finalLadder_halfwayGeometry
      (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed
  have hRungs : ∀ a, ¬ (L.stageWeb a).IsUnhindered →
      (L.stageWeb a).IsHindrance (L.rung a) := by
    intro a hstage
    exact (L.stageWeb a).chosenMaximalWave_isHindrance_of_not_isUnhindered hstage
  have hEq : L = DWeb.UnroofedMarker.ladder Gamma (succ kappa) preferred :=
    UnroofedHalfwayRowLadder.deferred_eq_core Gamma (succ kappa) preferred hNoEnter
  have hindranceObstruction : L.phiHindrance ⊆
      DWeb.KappaLadder.Deferred.phi L := by
    rw [hEq]
    exact DWeb.UnroofedMarker.ladder_deferred_phiHindrance_subset_phi
      Gamma (succ kappa) preferred hNoEnter hGamma
  let zero : Ladder.Stage (succ kappa) := ⟨0, hregular.ord_pos⟩
  let oldStage := RegularCardinal.nextInClub hregular Sigma hSigma zero
  let newStage := RegularCardinal.nextInClub hregular Sigma hSigma oldStage
  let C : ClubStageGeometry Gamma Y kappa (succ kappa) := {
    ladder := L
    legal := hL
    hindranceRungs := hRungs
    hindranceObstruction := hindranceObstruction
    normalized := hGamma
    club := Sigma
    club_isClub := hSigma
    club_avoids_phi := by simpa only [L] using havoid
    oldStage := oldStage
    newStage := newStage
    old_mem_club := RegularCardinal.nextInClub_mem
      hregular Sigma hSigma zero
    new_mem_club := RegularCardinal.nextInClub_mem
      hregular Sigma hSigma oldStage
    old_lt_new := RegularCardinal.lt_nextInClub
      hregular Sigma hSigma oldStage
    closedStage := closedStage
    closedStage_mono := hmono
    before_card := ClubStageGeometry.mk_closedBefore_le
      closedStage hmono hcard newStage
    capacity_infinite := hkappa }
  exact ⟨C, rfl, rfl, rfl⟩

/-- The actual causal ladder has a genuine avoiding club, with its identity
and the supplied closing family retained. -/
theorem exists_clubStageGeometry_preserving_finalLadder
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (hUnhindered : Gamma.IsUnhindered)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (closedStage : Ladder.Stage (succ kappa) → Set V)
    (hmono : ∀ {a b}, a ≤ b → closedStage a ⊆ closedStage b)
    (hcard : ∀ a, #(closedStage a) ≤ kappa) :
    ∃ C : ClubStageGeometry Gamma Y kappa (succ kappa),
      C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed ∧
      C.closedStage = closedStage := by
  let preferred := (rule Gamma kappa hkappa hGamma seed hseed).preferred
    (hkappa.trans (le_succ kappa))
  have hNoEnter : Gamma.NoEdgeEnters Gamma.source := by
    intro x y hxy hy
    exact (hGamma hxy).1 hy
  obtain ⟨C, hC, hclosed⟩ := UnroofedHalfwayClub.exists_clubStageGeometry
    (Y := Y) hkappa hGamma hUnhindered preferred closedStage hmono hcard
  refine ⟨C, ?_, hclosed⟩
  exact hC.trans
    (UnroofedHalfwayRowLadder.deferred_eq_core
      Gamma (succ kappa) preferred hNoEnter).symm

/-- Constant-base specialization used when the selected club stages should
share one already closed `kappa`-small set. -/
theorem exists_clubStageGeometry_of_constantBase
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (hUnhindered : Gamma.IsUnhindered)
    {seed base : Set V} (hseed : #seed ≤ succ kappa)
    (hbase : #base ≤ kappa) :
    ∃ C : ClubStageGeometry Gamma Y kappa (succ kappa),
      C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed ∧
      C.closedStage = (fun _ ↦ base) := by
  apply exists_clubStageGeometry_preserving_finalLadder
    (Gamma := Gamma) (Y := Y) (kappa := kappa)
    hkappa hGamma hUnhindered hseed (fun _ ↦ base)
  · intro _a _b _hab
    exact Set.Subset.rfl
  · intro _a
    exact hbase

#print axioms CausalSection9Rows.exists_clubStageGeometry_of_avoidingClub
#print axioms CausalSection9Rows.exists_clubStageGeometry_preserving_finalLadder
#print axioms CausalSection9Rows.exists_clubStageGeometry_of_constantBase

end CausalSection9Rows
end Erdos599.Blueprint.LinkageBlueprint
