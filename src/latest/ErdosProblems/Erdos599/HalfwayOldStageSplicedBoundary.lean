/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayOldStageIntervalSplice
import ErdosProblems.Erdos599.Halfway930ReferenceAvoidance

/-!
# The exact left boundary of the old-reference interval splice

The source-faithful row which crosses one club interval begins with the
essential reference at the old club stage.  That reference has two genuinely
different kinds of roots: roots in the ambient web source and roots introduced
by ladder markers.  This file records the literal split.  In particular it
does not identify the marker roots with the ambient source.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Ladder

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace OldStageIntervalTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {z : V}

/-- Initials of the source-starting part of the old essential reference. -/
def sourceInitials (T : OldStageIntervalTransaction C z) : Set V :=
  Gamma.initialSet
    (ladderReference.sourceStarting
      (Gamma := Gamma) (L := C.ladder) (a := C.oldStage))

/-- Initials of the marker-starting part of the old essential reference. -/
def markerInitials (T : OldStageIntervalTransaction C z) : Set V :=
  Gamma.initialSet
    (ladderReference.markerStarting
      (Gamma := Gamma) (L := C.ladder) (a := C.oldStage))

/-- The source-star row has exactly the honest source/marker initial split. -/
theorem initialSet_splicedIntervalRow_eq_source_union_marker
    (T : OldStageIntervalTransaction C z) :
    Gamma.initialSet T.splicedIntervalRow =
      T.sourceInitials ∪ T.markerInitials := by
  rw [T.initialSet_splicedIntervalRow, oldReference,
    ← ladderReference.sourceStarting_union_markerStarting,
    Gamma.initialSet_union]
  rfl

/-- Every source-starting reference root is an ambient source vertex. -/
theorem sourceInitials_subset_source
    (T : OldStageIntervalTransaction C z) :
    T.sourceInitials ⊆ Gamma.source := by
  rintro x ⟨p, hp, rfl⟩
  exact hp.2

/-- Every marker-starting reference root is outside the ambient source. -/
theorem markerInitials_subset_source_compl
    (T : OldStageIntervalTransaction C z) :
    T.markerInitials ⊆ Gamma.sourceᶜ := by
  rintro x ⟨p, hp, rfl⟩
  exact hp.2

/-- The two kinds of roots are disjoint for the reason encoded in their
definitions, rather than by a cardinality argument. -/
theorem disjoint_sourceInitials_markerInitials
    (T : OldStageIntervalTransaction C z) :
    Disjoint T.sourceInitials T.markerInitials := by
  apply Set.disjoint_left.2
  intro x hxSource hxMarker
  exact T.markerInitials_subset_source_compl hxMarker
    (T.sourceInitials_subset_source hxSource)

/-- The exact terminal boundary is the terminal boundary of the old-to-new
interval row.  It is contained in the later slice; surjectivity onto the
whole later slice is neither assumed nor needed. -/
theorem terminalFrontier_splicedIntervalRow_subset_newSlice
    (T : OldStageIntervalTransaction C z) :
    Gamma.terminalFrontier T.splicedIntervalRow ⊆ C.newSlice := by
  rw [T.terminalFrontier_splicedIntervalRow]
  exact T.ambientInterval_linkage.terminalFrontier_subset

end OldStageIntervalTransaction

#print axioms OldStageIntervalTransaction.initialSet_splicedIntervalRow_eq_source_union_marker
#print axioms OldStageIntervalTransaction.disjoint_sourceInitials_markerInitials

end LinkageBlueprint
end Blueprint
end Erdos599

