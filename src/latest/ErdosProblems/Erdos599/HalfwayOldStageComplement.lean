/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayStageGeometry
import ErdosProblems.Erdos599.SliceStageIntervalBridge

/-!
# The small exceptional part of a half-way club interval

The old ladder frontier itself need not have cardinal at most `kappa`: the
ambient web may have many more sources than the designated `kappa`-set.
What the Section 9 extension step uses is the standard ladder decomposition.
Outside the small family of sources whose accumulated component becomes
inessential, the literal intervals of the accumulated warp already link the
old frontier to the new frontier.  Since the new stage belongs to the club
disjoint from `phi`, the omitted source set has cardinal at most `kappa`.

This file packages that exact complement linkage.  It is the source-faithful
replacement for an unsupported hypothesis `#C.oldSlice <= kappa`.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open CardinalInduction
open CardinalInduction.SliceCandidate

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- The sources of the old frontier whose chosen extension is inessential
at the selected new stage. -/
def ClubStageGeometry.oldStageExceptional
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) : Set V :=
  inessentialExtensionSources C.legal C.old_lt_new.le

namespace ClubStageGeometry

variable (C : ClubStageGeometry Gamma Y kappa (succ kappa))

/-- The selected new club stage is outside the ladder obstruction set. -/
theorem newStage_not_mem_phi : C.newStage ∉ C.ladder.phi := by
  intro hphi
  exact Set.disjoint_left.1 C.club_avoids_phi C.new_mem_club hphi

/-- The exceptional old-frontier source set has the required current-
cardinal bound.  No cardinal bound on the whole old frontier is asserted. -/
theorem mk_oldStageExceptional_le : #C.oldStageExceptional ≤ kappa := by
  exact (lt_succ_iff.mp
    (mk_inessentialExtensionSources_lt_of_not_mem_phi
      C.legal C.old_lt_new.le C.newStage_not_mem_phi))

/-- The literal ordinary interval family between the two selected stages. -/
def oldStageOrdinaryFamily :
    Set (C.ladder.stageWeb C.oldStage).DPath :=
  ordinaryStageFamily C.legal C.old_lt_new.le

/-- Every nonexceptional old-frontier source is already linked to the new
frontier by a literal interval of the accumulated ladder warp. -/
theorem oldStageOrdinaryFamily_isLinkageBetween :
    IsLinkageBetween (C.ladder.stageWeb C.oldStage)
      (C.oldSlice \ C.oldStageExceptional) C.newSlice
      C.oldStageOrdinaryFamily := by
  exact ordinaryStageFamily_isLinkageBetween C.legal C.old_lt_new.le

/-- The ordinary complement meets the new frontier only at the terminal of
each member.  This is the tightness needed when the eventual full linkage is
stopped or lifted to the ambient web. -/
theorem oldStageOrdinaryFamily_meetsOnlyAtTerminal :
    SliceSpliceSource.MeetsOnlyAtTerminal
      (C.ladder.stageWeb C.oldStage) C.oldStageOrdinaryFamily C.newSlice := by
  exact ordinaryStageFamily_meetsOnlyAtTerminal C.legal C.old_lt_new.le

/-- Ambient lifting preserves the literal ordinary interval family. -/
@[simp] theorem liftStageFamily_oldStageOrdinaryFamily :
    SliceSegmentCore.liftStageFamily C.ladder C.oldStage
        C.oldStageOrdinaryFamily =
      SliceSegmentCore.segmentFamily
        (ordinaryStageIntervalRealization C.legal C.old_lt_new.le
          |>.toSegmentRealization) := by
  exact liftStageFamily_ordinaryStageFamily C.legal C.old_lt_new.le

end ClubStageGeometry

end LinkageBlueprint
end Blueprint
end Erdos599
