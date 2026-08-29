/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshReachableSinkOutcome
import ErdosProblems.Erdos599.SplitGroundingGroundedReservedRouteDisjoint

/-!
# Removing the reserved source from full-source frontier roots

The final simultaneous switch is analyzed from the whole ambient source.
Nevertheless, the distinguished unused grounded record cannot reach the
source-first relevant stopping frontier: its edges survive, its support is
forward closed, and its whole trace was selected disjoint from the popular
cut.  Thus every full-source root of a stopping-frontier point automatically
starts away from the reserved record.  This is the source-faithful bridge
from the global all-source exchange to the protected pruning compiler.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open PopularGroundingBridge GroundingErasedDecode GroundingErasedSwitchRelation
  GroundingErasedForwardConflict

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev FullSourceRootFrontier : Set V :=
  L.splitGroundedFreshRelevantStoppingFrontier (hL := hL) (S := S)

private abbrev FullSourceRootEdges : Set (V × V) :=
  L.splitGroundedFreshRelevantSwitchedEdges
    (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)

private abbrev FullSourceRootRecord :=
  L.splitGroundedFreshAvoidingCanonicalUnusedRecord
    hL hground hnotFresh S

/-- Any full-source root of a vertex outside the reserved record already
starts at an allowed source.  This is the unrestricted form used by the
native-frontier control and deleted-head recursions. -/
theorem splitGroundedFresh_root_from_source_avoids_reserved_of_not_mem_record
    {T : Set V} {x : V}
    (hx : x ∉ (FullSourceRootRecord (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh)
      (S := S)).record.support)
    (hroot : ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ erasedSelectedSwitchedEdgesAt
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
          (L.splitGroundedFreshAvoidingCanonicalControls
            hL hground hnotFresh S) T) a x) :
    ∃ a ∈ Gamma.source \ {
        (FullSourceRootRecord (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh)
          (S := S)).record.initial},
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ erasedSelectedSwitchedEdgesAt
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
          (L.splitGroundedFreshAvoidingCanonicalControls
            hL hground hnotFresh S) T) a x := by
  obtain ⟨a, haSource, hax⟩ := hroot
  let R := L.splitGroundedFreshAvoidingBaseUnusedRecord
    hL hground hnotFresh S
  have haNe : a ≠ R.record.initial := by
    intro ha
    subst a
    apply hx
    simpa only [FullSourceRootRecord,
      splitGroundedFreshAvoidingCanonicalUnusedRecord,
      SplitGroundedUnusedRecord.forReservedControlsFrom] using
      (R.reservedSwitched_reachable_mem_record
        (L.splitGroundedFreshAvoidingBaseUnusedRecord_trace_disjoint
          hL hground hnotFresh S) T hax)
  refine ⟨a, ⟨haSource, ?_⟩, hax⟩
  simpa only [Set.mem_singleton_iff,
    FullSourceRootRecord,
    splitGroundedFreshAvoidingCanonicalUnusedRecord,
    SplitGroundedUnusedRecord.forReservedControlsFrom] using haNe

/-- A source-first frontier point rooted in the stopped canonical relation
from some ambient source is rooted from a source other than the reserved
grounded record's initial vertex. -/
theorem splitGroundedFresh_frontierRoot_from_source_avoids_reserved
    {t : V}
    (ht : t ∈ FullSourceRootFrontier (L := L) (hL := hL) (S := S))
    (hroot : ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ FullSourceRootEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a t) :
    ∃ a ∈ Gamma.source \ {
        (FullSourceRootRecord (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh)
          (S := S)).record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ FullSourceRootEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a t := by
  let R := L.splitGroundedFreshAvoidingBaseUnusedRecord
    hL hground hnotFresh S
  refine L.splitGroundedFresh_root_from_source_avoids_reserved_of_not_mem_record
    (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S) ?_ hroot
  intro htRecord
  exact Set.disjoint_left.mp
    (R.relevantBB_disjoint_record_of_trace_disjoint
      (L.splitGroundedFreshAvoidingBaseUnusedRecord_trace_disjoint
        hL hground hnotFresh S))
    (L.splitGroundedRelevantSourceFirstBB_subset hL.legal S.cut ht)
    htRecord

/-- Pointwise full-source rooting of the actual source-first frontier can be
fed directly to the protected reachable-sink compiler.  The omitted-source
condition is a theorem of the reserved-record geometry, not an extra global
rooting premise. -/
theorem exists_hindrance_of_splitGroundedFreshFrontierRootedFromSource
    (hC : Popular.IsSeparator
      (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda S.cut)
    (hroot : ∀ t ∈ FullSourceRootFrontier
        (L := L) (hL := hL) (S := S),
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ FullSourceRootEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a t) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.exists_hindrance_of_splitGroundedFreshFrontierRootedOutcome
    (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S) hC
  right
  intro t ht
  exact L.splitGroundedFresh_frontierRoot_from_source_avoids_reserved
    (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S) ht (hroot t ht)

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFresh_root_from_source_avoids_reserved_of_not_mem_record
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFresh_frontierRoot_from_source_avoids_reserved
#print axioms
  Erdos599.DWeb.KappaLadder.exists_hindrance_of_splitGroundedFreshFrontierRootedFromSource
