/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshAvoidingControls
import ErdosProblems.Erdos599.SplitGroundingGroundedPreStoppedOutcome
import ErdosProblems.Erdos599.SplitGroundingGroundedCutAvoidingSelection

/-!
# Canonical grounded switch after removing the fresh diagonal

This fixes the omitted grounded record before the final request selection,
reserves its complete auxiliary carrier, and uses the refined controls which
forbid every original-hanging collision.  In this branch every selected
backward owner has a literal finite prefix from an allowed original source;
there is no residual equal-stage provider seam.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath Stationary PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode
open GroundingErasedSwitchRelation GroundingErasedForwardConflict
  GroundingRootedReachabilityWarp

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Initial omitted record for the full-hanging-avoiding controls. -/
noncomputable def splitGroundedFreshAvoidingBaseUnusedRecord
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : IsStationaryBelow kappa L.phiGround)
    (hnotFresh : ¬ IsStationaryBelow kappa
      L.freshInessentialGroundStages)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    L.SplitGroundedUnusedRecord hL hground S
      (splitGroundedFreshAvoidingControls (L := L) (hL := hL)
        (hground := hground) (S := S) hnotFresh) :=
  Classical.choose (L.exists_splitGroundedUnusedRecord_trace_disjoint hL hground S
    (splitGroundedFreshAvoidingControls (L := L) (hL := hL)
      (hground := hground) (S := S) hnotFresh))

/-- The omitted record is selected away from the entire popular cut,
not only away from selected auxiliary initial vertices. -/
theorem splitGroundedFreshAvoidingBaseUnusedRecord_trace_disjoint
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : IsStationaryBelow kappa L.phiGround)
    (hnotFresh : ¬ IsStationaryBelow kappa L.freshInessentialGroundStages)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    Disjoint (PopularSwitching.ladderTrace
      (L.splitGroundedPopularAuxiliaryInput hL.legal)
      (L.splitGroundedFreshAvoidingBaseUnusedRecord hL hground hnotFresh S).record)
      S.cut :=
  Classical.choose_spec (L.exists_splitGroundedUnusedRecord_trace_disjoint
    hL hground S (splitGroundedFreshAvoidingControls (L := L) (hL := hL)
      (hground := hground) (S := S) hnotFresh))

/-- Canonical final controls in the nonstationary-fresh branch. -/
noncomputable def splitGroundedFreshAvoidingCanonicalControls
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : IsStationaryBelow kappa L.phiGround)
    (hnotFresh : ¬ IsStationaryBelow kappa
      L.freshInessentialGroundStages)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    GroundingSelection.Controls S :=
  splitGroundedReservedControlsFrom
    (L.splitGroundedFreshAvoidingBaseUnusedRecord
      hL hground hnotFresh S)

/-- The same omitted record certified for the final canonical controls. -/
noncomputable def splitGroundedFreshAvoidingCanonicalUnusedRecord
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : IsStationaryBelow kappa L.phiGround)
    (hnotFresh : ¬ IsStationaryBelow kappa
      L.freshInessentialGroundStages)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    L.SplitGroundedUnusedRecord hL hground S
      (L.splitGroundedFreshAvoidingCanonicalControls
        hL hground hnotFresh S) :=
  (L.splitGroundedFreshAvoidingBaseUnusedRecord
    hL hground hnotFresh S).forReservedControlsFrom

/-- Re-reserving the final controls leaves the cut-avoiding record itself
unchanged, so the stronger cut avoidance survives the final selection. -/
theorem splitGroundedFreshAvoidingCanonicalUnusedRecord_trace_disjoint
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : IsStationaryBelow kappa L.phiGround)
    (hnotFresh : ¬ IsStationaryBelow kappa L.freshInessentialGroundStages)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    Disjoint (PopularSwitching.ladderTrace
      (L.splitGroundedPopularAuxiliaryInput hL.legal)
      (L.splitGroundedFreshAvoidingCanonicalUnusedRecord hL hground hnotFresh S).record)
      S.cut :=
  L.splitGroundedFreshAvoidingBaseUnusedRecord_trace_disjoint hL hground hnotFresh S

/-- The canonical pre-stopped switched relation for the
nonstationary-fresh branch. -/
abbrev splitGroundedFreshAvoidingCanonicalEdges
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : IsStationaryBelow kappa L.phiGround)
    (hnotFresh : ¬ IsStationaryBelow kappa
      L.freshInessentialGroundStages)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) : Set (V × V) :=
  erasedSelectedSwitchedEdgesAt
    (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
    (L.splitGroundedFreshAvoidingCanonicalControls
      hL hground hnotFresh S) ∅

theorem splitGroundedFreshAvoidingCanonicalEdges_subset_adj
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : IsStationaryBelow kappa L.phiGround)
    (hnotFresh : ¬ IsStationaryBelow kappa
      L.freshInessentialGroundStages)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    L.splitGroundedFreshAvoidingCanonicalEdges hL hground hnotFresh S ⊆
      {e | Gamma.graph.Adj e.1 e.2} :=
  erasedSelectedSwitchedEdgesAt_subset_adj
    (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
    (L.splitGroundedFreshAvoidingCanonicalControls
      hL hground hnotFresh S) ∅

theorem splitGroundedFreshAvoidingCanonicalEdges_biUnique
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : IsStationaryBelow kappa L.phiGround)
    (hnotFresh : ¬ IsStationaryBelow kappa
      L.freshInessentialGroundStages)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈
      L.splitGroundedFreshAvoidingCanonicalEdges
        hL hground hnotFresh S) :=
  erasedSelectedSwitchedEdgesAt_biUnique
    (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
    (L.splitGroundedFreshAvoidingCanonicalControls
      hL hground hnotFresh S) ∅
    (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)

/-- The final canonical route for each request avoids every original
hanging limiting-ladder component. -/
theorem splitGroundedFreshAvoidingCanonicalPath_no_hangingCollision
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : IsStationaryBelow kappa L.phiGround)
    (hnotFresh : ¬ IsStationaryBelow kappa
      L.freshInessentialGroundStages)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : Request (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) :
    ¬ GroundingConcreteControls.hangingLadderCollision
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r
      (strongSelectedPath
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
        (L.splitGroundedFreshAvoidingCanonicalControls
          hL hground hnotFresh S) r) :=
  splitGroundedFreshAvoidingReservedStrongSelectedPath_no_hangingCollision
    hnotFresh
    (L.splitGroundedFreshAvoidingBaseUnusedRecord
      hL hground hnotFresh S) r

/-- Every selected backward owner has a finite allowed-source prefix in the
final canonical selection. -/
theorem splitGroundedFreshAvoidingCanonicalBackwardOwner_rootPrefix
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : IsStationaryBelow kappa L.phiGround)
    (hnotFresh : ¬ IsStationaryBelow kappa
      L.freshInessentialGroundStages)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : Request (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (l : Alternating.Link Gamma.graph)
    (hl : l ∈ (selectedErasedCompression
      (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
      (L.splitGroundedFreshAvoidingCanonicalControls
        hL hground hnotFresh S) r).path.links)
    (hldir : l.direction = .backward)
    (parent : Gamma.DPath) (hparent : parent ∈ L.limitWarp)
    (hsub : l.path.IsSubpathOf parent) :
    ∃ q : FinitePath Gamma.graph,
      q.start ∈ Gamma.source \ {
        (L.splitGroundedFreshAvoidingCanonicalUnusedRecord
          hL hground hnotFresh S).record.initial} ∧
      q.finish = l.path.start ∧ q.support ⊆ parent.support ∧
      q.edgeSet ⊆ parent.edgeSet := by
  simpa only [splitGroundedFreshAvoidingCanonicalControls,
    splitGroundedFreshAvoidingCanonicalUnusedRecord,
    SplitGroundedUnusedRecord.forReservedControlsFrom] using
    (splitGroundedFreshAvoidingReservedBackwardOwner_rootPrefix
      hnotFresh
      (L.splitGroundedFreshAvoidingBaseUnusedRecord
        hL hground hnotFresh S)
      r l hl hldir parent hparent hsub)

/-- Assumption-free canonical outcome for the nonstationary-fresh branch.
The relation already has full hanging avoidance and allowed-source backward
owners; the two residual alternatives are the literal root and ordered
boundary obstructions for that concrete relation. -/
theorem splitGroundedFreshAvoidingCanonicalAssertion822Output_or_obstruction
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : IsStationaryBelow kappa L.phiGround)
    (hnotFresh : ¬ IsStationaryBelow kappa
      L.freshInessentialGroundStages)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) ∨
    Nonempty (L.SplitGroundedPreStoppedRootObstruction
      (L.splitGroundedFreshAvoidingCanonicalUnusedRecord
        hL hground hnotFresh S)) ∨
    Nonempty (L.SplitGroundedPreStoppedBoundaryObstruction
      (L.splitGroundedFreshAvoidingCanonicalUnusedRecord
        hL hground hnotFresh S)) :=
  L.splitGroundedAssertion822Output_or_preStoppedObstruction
    (L.splitGroundedFreshAvoidingCanonicalUnusedRecord
      hL hground hnotFresh S)

end KappaLadder
end DWeb
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.splitGroundedFreshAvoidingCanonicalEdges_biUnique
#print axioms Erdos599.DWeb.KappaLadder.splitGroundedFreshAvoidingCanonicalPath_no_hangingCollision
#print axioms Erdos599.DWeb.KappaLadder.splitGroundedFreshAvoidingCanonicalBackwardOwner_rootPrefix
#print axioms Erdos599.DWeb.KappaLadder.splitGroundedFreshAvoidingCanonicalAssertion822Output_or_obstruction
