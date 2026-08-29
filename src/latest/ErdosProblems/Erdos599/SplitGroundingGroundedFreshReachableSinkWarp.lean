/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingSourceReachableSinkWarp
import ErdosProblems.Erdos599.GroundingErasedForwardConflict
import ErdosProblems.Erdos599.HindranceGrounding
import ErdosProblems.Erdos599.SplitGroundingGroundedFreshAvoidingCanonical
import ErdosProblems.Erdos599.SplitGroundingGroundedRelevantSourceFirst

/-!
# The actual source-reachable warp of the canonical grounded switch

This specializes the generic reachable-sink relation compiler to the
canonical fresh-avoiding selected relation, stopped at the source-first
relevant boundary.  Unlike a full-relation realization, the construction is
unconditional: cycles and reverse rays in components not reached from the
allowed original sources are simply irrelevant.  The produced family is an
honest finite warp and its edges are actual switched edges.

The remaining Assertion 8.22 geometry is now stated on its truthful dynamic
frontier: prove that this reachable-sink boundary is contained in the
relevant bookkeeping boundary and separates the ambient source and target.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating PopularGroundingBridge GroundingErasedDecode
open GroundingErasedForwardConflict
open GroundingSourceReachableSinkWarp

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev FreshReachableSinkIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev FreshReachableSinkControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev FreshReachableSinkRecord :=
  L.splitGroundedFreshAvoidingCanonicalUnusedRecord
    hL hground hnotFresh S

/-- The source-first relevant frontier at which the canonical relation is
stopped. -/
abbrev splitGroundedFreshRelevantStoppingFrontier : Set V :=
  L.splitGroundedRelevantSourceFirstBB hL.legal S.cut

/-- The actual stopped canonical switched relation. -/
abbrev splitGroundedFreshRelevantSwitchedEdges : Set (V × V) :=
  erasedSelectedSwitchedEdgesAt
    (FreshReachableSinkIndexed (L := L) (hL := hL)
      (hground := hground)) S
    (FreshReachableSinkControls (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (L.splitGroundedFreshRelevantStoppingFrontier
      (hL := hL) (S := S))

/-- The true terminal boundary of the allowed-source part of the canonical
switched relation. -/
abbrev splitGroundedFreshReachableSinkBoundary : Set V :=
  sourceReachableSinkBoundary
    (L.splitGroundedFreshRelevantSwitchedEdges
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (Gamma.source \ {
      (FreshReachableSinkRecord (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S)).record.initial})

/-- Unconditional genuine path-family realization of the source-reachable
part of the canonical switch.  This is the simultaneous family object to
which the remaining relevant-boundary coverage proof must be applied. -/
theorem exists_splitGroundedFreshReachableSinkWarp :
    ∃ W : Set Gamma.DPath,
      Gamma.IsWarp W ∧
        familyEdges W ⊆
          L.splitGroundedFreshRelevantSwitchedEdges
            (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S) ∧
        Gamma.initialSet W ⊆ Gamma.source \ {
          (FreshReachableSinkRecord (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh)
            (S := S)).record.initial} ∧
        Gamma.initialSet W ⊆ Gamma.source ∧
        Gamma.terminalFrontier W =
          L.splitGroundedFreshReachableSinkBoundary
            (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S) := by
  apply exists_sourceReachableSinkWarp
  · exact
      erasedSelectedSwitchedEdgesAt_subset_adj
        (FreshReachableSinkIndexed (L := L) (hL := hL)
          (hground := hground)) S
        (FreshReachableSinkControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (L.splitGroundedFreshRelevantStoppingFrontier
          (hL := hL) (S := S))
  · exact
      erasedSelectedSwitchedEdgesAt_biUnique
        (FreshReachableSinkIndexed (L := L) (hL := hL)
          (hground := hground)) S
        (FreshReachableSinkControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (L.splitGroundedFreshRelevantStoppingFrontier
          (hL := hL) (S := S))
        (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)
  · exact Set.sdiff_subset

/-- Full realization of the allowed-source component of the canonical
switched relation.  Under the ambient source-normalization hypothesis this
keeps not only its finite sink paths, but also every source-reachable forward
ray.  Cycles and reverse rays outside the source-reachable carrier remain
irrelevant. -/
theorem exists_splitGroundedFreshReachableComponentWarp
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source) :
    ∃ W : Set Gamma.DPath,
      Gamma.IsWarp W ∧
        familyEdges W = RootReachableRelation.edges
          (L.splitGroundedFreshRelevantSwitchedEdges
            (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S))
          (Gamma.source \ {
            (FreshReachableSinkRecord (L := L) (hL := hL)
              (hground := hground) (hnotFresh := hnotFresh)
              (S := S)).record.initial}) ∧
        Gamma.vertexSet W = RootReachableRelation.carrier
          (L.splitGroundedFreshRelevantSwitchedEdges
            (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S))
          (Gamma.source \ {
            (FreshReachableSinkRecord (L := L) (hL := hL)
              (hground := hground) (hnotFresh := hnotFresh)
              (S := S)).record.initial}) ∧
        Gamma.initialSet W = Gamma.source \ {
          (FreshReachableSinkRecord (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh)
            (S := S)).record.initial} ∧
        Gamma.terminalFrontier W =
          L.splitGroundedFreshReachableSinkBoundary
            (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S) := by
  apply exists_sourceReachableComponentWarp
  · exact
      erasedSelectedSwitchedEdgesAt_subset_adj
        (FreshReachableSinkIndexed (L := L) (hL := hL)
          (hground := hground)) S
        (FreshReachableSinkControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (L.splitGroundedFreshRelevantStoppingFrontier
          (hL := hL) (S := S))
  · exact
      erasedSelectedSwitchedEdgesAt_biUnique
        (FreshReachableSinkIndexed (L := L) (hL := hL)
          (hground := hground)) S
        (FreshReachableSinkControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (L.splitGroundedFreshRelevantStoppingFrontier
          (hL := hL) (S := S))
        (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)
  · intro x hx hin
    obtain ⟨y, hyx⟩ := hin
    exact hNoEnter
      (erasedSelectedSwitchedEdgesAt_subset_adj
        (FreshReachableSinkIndexed (L := L) (hL := hL)
          (hground := hground)) S
        (FreshReachableSinkControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (L.splitGroundedFreshRelevantStoppingFrontier
          (hL := hL) (S := S)) hyx) hx.1

/-- Once the concrete reachable-sink boundary is shown to separate, the
actual compiled warp is already a hindrance: all of its initials avoid the
reserved grounded source.  No inessential-component or full-relation
realization premise is needed. -/
theorem exists_hindrance_of_splitGroundedFreshReachableSinkSeparator
    (hseparator : Popular.IsSeparator Gamma
      (L.splitGroundedFreshReachableSinkBoundary
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  obtain ⟨W, hwarp, _hedges, hallowed, hsource, hfrontier⟩ :=
    L.exists_splitGroundedFreshReachableSinkWarp
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S)
  refine ⟨W, DWeb.isWave_of_terminalFrontier_isSeparator
    hwarp hsource ?_, ?_⟩
  · simpa only [hfrontier] using hseparator
  · intro heq
    let R := FreshReachableSinkRecord (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S)
    have hreserved : R.record.initial ∈ Gamma.initialSet W := by
      rw [heq]
      exact R.grounded
    exact (hallowed hreserved).2 (Set.mem_singleton R.record.initial)

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.exists_splitGroundedFreshReachableSinkWarp
#print axioms
  Erdos599.DWeb.KappaLadder.exists_hindrance_of_splitGroundedFreshReachableSinkSeparator
#print axioms
  Erdos599.DWeb.KappaLadder.exists_splitGroundedFreshReachableComponentWarp
