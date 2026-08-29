/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UncountableWarpLimitAttainment
import ErdosProblems.Erdos599.HalfwayMovingGlobalReferenceRoof

/-!
# Capturing a small family of global reference paths at a later club stage

Literal attainment at an uncountable regular direct limit applies to finite
paths and rays alike. A bounded family of global reference paths therefore
occurs at one later club stage, without claiming that a raw interval linkage
contains their prefixes or tails.
-/

noncomputable section

open Set Cardinal Order

namespace Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry

open DirectedPath Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- A `kappa`-bounded family of global reference paths is literally present
at one later club stage and at every subsequent ordinary stage. -/
theorem exists_later_club_containing_limitFamily
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {P : Set Gamma.DPath} (hP : P ⊆ C.ladder.limitWarp) (hPcard : #P ≤ kappa) :
    ∃ a ∈ C.club, C.newStage < a ∧
      ∀ b : Ladder.Stage (succ kappa), a ≤ b → P ⊆ C.ladder.warpAt b := by
  have hlimit : Order.IsSuccLimit (succ kappa).ord :=
    Cardinal.isSuccLimit_ord C.legal.regular.aleph0_le
  obtain ⟨D, hstage, hpaths⟩ :=
    C.legal.limitStages (Ladder.finalStage (succ kappa)) hlimit
  have hP_D : P ⊆ D.limitPaths Gamma := by
    change P ⊆ C.ladder.accumulated (Ladder.finalStage (succ kappa)) at hP
    rwa [hpaths] at hP
  obtain ⟨a, ha⟩ := D.exists_stage_subset_of_small_limitFamily
    C.legal.regular C.legal.uncountable hP_D (lt_succ_iff.mpr hPcard)
  let beta : Ladder.Stage (succ kappa) :=
    RegularCardinal.aboveInClub C.legal.regular C.club C.club_isClub
      C.newStage a
  have hbetaClub : beta ∈ C.club :=
    RegularCardinal.aboveInClub_mem C.legal.regular C.club C.club_isClub
      C.newStage a
  have hcurrentBeta : C.newStage < beta :=
    RegularCardinal.left_lt_aboveInClub C.legal.regular C.club C.club_isClub
      C.newStage a
  have haBeta : a < beta :=
    RegularCardinal.right_lt_aboveInClub C.legal.regular C.club C.club_isClub
      C.newStage a
  refine ⟨beta, hbetaClub, hcurrentBeta, ?_⟩
  intro b hbetaB p hp
  have hpD := ha b (haBeta.le.trans hbetaB) hp
  rw [hstage b] at hpD
  exact hpD

#print axioms exists_later_club_containing_limitFamily

end Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry
