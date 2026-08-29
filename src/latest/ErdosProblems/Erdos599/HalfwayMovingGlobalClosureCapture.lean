/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayStageGeometryCore
import ErdosProblems.Erdos599.SliceSpliceConstructor

/-!
# Moving a closed Assertion 9.31 seed to a later club roof

In the source proof the small closing set is constructed before the
`T_alpha`--`T_beta` row which is subsequently fractured.  The later stage
`beta` must therefore be chosen *after* the closing set is known.  This file
packages that dependency-correct step.

The only geometric premise on the set is membership in the union of the
ladder roofs.  In particular, a closed set may contain vertices of the
possibly infinite limiting reference warp; no finite-character hypothesis
on that warp occurs here.  Regularity and the `kappa` bound put the whole set
below one club frontier, and `aboveInClub` moves that frontier strictly past
the current transaction stage.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- The source-order output obtained after a small global-reference closed
set has been built: one club stage strictly beyond the current stage whose
ordinary roof contains the entire set. -/
structure LaterClubRoofCapture
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) (X : Set V) where
  stage : Ladder.Stage (succ kappa)
  mem_club : stage ∈ C.club
  current_lt : C.newStage < stage
  subset_roof : X ⊆ Gamma.roof (C.ladder.frontier stage)

namespace LaterClubRoofCapture

/-- Deferred legality contains exactly the ladder geometry used by the
regular roof-capture lemma. -/
private def spliceGeometry
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) :
    CardinalInduction.SliceSpliceConstructor.SpliceLadderGeometry
      Gamma C.ladder :=
  ⟨C.legal.regular, C.legal.initialStage, C.legal.limitStages,
    C.legal.warpStages, C.legal.frontiersEssential,
    C.legal.frontierChronology, C.legal.strictFrontierChronology⟩

/-- A `kappa`-bounded subset of the limiting roof is captured by a club
frontier strictly later than the currently selected stage.

This is the formal version of the `beta := sup gamma_x` step in Claim 9.31.
The successor-cardinal inequality is derived from `#X <= kappa`; it is not a
new smallness premise. -/
theorem exists_of_subset_limitRoof
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (X : Set V) (hXcard : #X ≤ kappa)
    (hXroof : X ⊆ C.ladder.limitRoof) :
    Nonempty (LaterClubRoofCapture C X) := by
  have hEventually :
      CardinalInduction.SliceSpliceConstructor.IsEventuallyRoofed
        Gamma C.ladder X :=
    CardinalInduction.SliceSpliceConstructor.isEventuallyRoofed_of_subset_limitRoof
      (spliceGeometry C) hXroof
  have hXsmall : #X < succ kappa := lt_succ_iff.mpr hXcard
  obtain ⟨a, haClub, hXa⟩ :=
    CardinalInduction.SliceSpliceConstructor.exists_club_roof_superset
      C.legal.regular C.club_isClub hEventually
      (Set.Subset.rfl : X ⊆ X) hXsmall
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
  exact ⟨{
    stage := beta
    mem_club := hbetaClub
    current_lt := hcurrentBeta
    subset_roof := hXa.trans
      (Gamma.roof_cut (C.legal.frontierChronology haBeta)) }⟩

/-- The captured stage web is unhindered, because it belongs to the same
club which avoids the ladder obstruction.  This is the exact input needed
to select the crossing row only after `X` has been closed. -/
theorem stageWeb_isUnhindered
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {X : Set V}
    (R : LaterClubRoofCapture C X) :
    (C.ladder.stageWeb R.stage).IsUnhindered :=
  C.stageWeb_isUnhindered R.mem_club

end LaterClubRoofCapture

#print axioms LaterClubRoofCapture.exists_of_subset_limitRoof
#print axioms LaterClubRoofCapture.stageWeb_isUnhindered

end Erdos599.Blueprint.LinkageBlueprint

