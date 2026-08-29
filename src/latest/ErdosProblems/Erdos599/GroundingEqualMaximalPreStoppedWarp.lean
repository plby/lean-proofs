/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualMaximalCollisionIntegration
import ErdosProblems.Erdos599.GroundingEqualMaximalPreStoppedCompiler
import ErdosProblems.Erdos599.GroundingWarpPruning

/-!
# Source-faithful pre-stopped output for the maximal equal closure

The source proof of Assertion 8.22 switches first, proves that the resulting
components form a warp and meet the decoded boundary at most once, and only
then truncates them.  It does not require every boundary vertex to be rooted
in one static relation.  This file gives the equal-stage maximal collision
cut the same source-faithful interface.

All auxiliary and original separator facts are already unconditional.  The
remaining construction data are exactly a pre-stopped component warp,
allowed roots for the components that meet the boundary, coverage, and the
one-hit property.  Generic first-hit pruning then produces the grounding
warp and the reserved source makes its essential part a hindrance.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace DWeb.KappaLadder

open GroundingEqualActiveSelection

variable {kappa : Cardinal.{u}}

/-- The literal pre-stopped component geometry for the corrected
target-plus-collision boundary. -/
structure EqualMaximalPreStoppedWarp
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (q : FinitePath (EqualInput L hL).lambda.graph)
    (hqsource : q.start ∈ (EqualInput L hL).lambda.source)
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) where
  paths : Set Gamma.DPath
  isWarp : Gamma.IsWarp paths
  meeting_initial_allowed : ∀ (p : Gamma.DPath), p ∈ paths →
    (∃ x ∈ p.support,
      x ∈ GroundingCut.BB (EqualInput L hL)
        (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths)) →
    p.initial ∈ Gamma.source \ {R.parent.initial}
  covers : GroundingCut.BB (EqualInput L hL)
      (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths) ⊆
    Gamma.vertexSet paths
  one_hit : ∀ (p : Gamma.DPath), p ∈ paths →
    (p.support ∩ GroundingCut.BB (EqualInput L hL)
      (reservedMaximalTargetCollisionCut
        (EqualInput L hL) M.paths)).Subsingleton

namespace EqualMaximalPreStoppedWarp

variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
  {q : FinitePath (EqualInput L hL).lambda.graph}
  {hqsource : q.start ∈ (EqualInput L hL).lambda.source}
  {R : L.ReservedGroundedParent hL q hqsource}
  {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
    (EqualInput L hL)
    ((EqualInput L hL).lambda.source \ {q.start})
    (collisionCarrier (EqualInput L hL) q)}

/-- First-hit pruning of the pre-stopped components gives the exact
Assertion 8.22 output over the corrected equal-stage cut. -/
theorem assertion822Output
    (O : L.EqualMaximalPreStoppedWarp hL q hqsource R M) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
      (EqualInput L hL)
      (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths)) := by
  let B := GroundingCut.BB (EqualInput L hL)
    (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths)
  have hsource : ∀ (p : Gamma.DPath), p ∈ O.paths →
      (∃ x ∈ p.support, x ∈ B) → p.initial ∈ Gamma.source := by
    intro p hp hmeet
    exact (O.meeting_initial_allowed p hp hmeet).1
  have hinitial : Gamma.initialSet
      (GroundingWarpPruning.prunedFamily O.paths B hsource O.isWarp) ⊆
        Gamma.source \ {R.parent.initial} := by
    exact GroundingWarpPruning.prunedFamily_initialSet_subset_of
      O.paths B (Gamma.source \ {R.parent.initial}) hsource O.isWarp
      O.meeting_initial_allowed
  refine ⟨GroundingWarpPruning.assertion822OutputOfPruning
    (EqualInput L hL)
    (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths)
    O.paths O.isWarp hsource O.covers O.one_hit
    (reservedMaximalTargetCollisionCut_BB_isSeparator L hL M.paths)
    R.parent.initial R.parent_initial_source ?_⟩
  intro hreserved
  obtain ⟨p, hpEssential, hpInitial⟩ := hreserved
  have hallowed : R.parent.initial ∈
      Gamma.source \ {R.parent.initial} :=
    hinitial ⟨p, hpEssential.1, hpInitial⟩
  exact hallowed.2 (Set.mem_singleton R.parent.initial)

/-- The source-faithful equal pre-stopped geometry compiles directly to an
ordinary hindrance. -/
theorem exists_hindrance
    (O : L.EqualMaximalPreStoppedWarp hL q hqsource R M) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  let A := O.assertion822Output.some
  exact A.exists_hindrance
    (reservedMaximalTargetCollisionCut_isSeparator
      (EqualInput L hL) M.paths)
    (L.popularAuxiliaryInput_terminalCut_isSeparator hL.legal)
    (GroundingAssertion818Decoder.finiteDescentDecoder
      L hL.legal
      (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths)
      (reservedMaximalTargetCollisionCut_isSeparator
        (EqualInput L hL) M.paths))

end EqualMaximalPreStoppedWarp

/-- End-to-end stationary equal-stage reduction to the literal pre-stopped
component warp.  All stationary thinning, reservation, maximal extension,
separator decoding, pruning, and unused-source arguments are internal. -/
theorem exists_hindrance_of_targetPure_stationary_equalSubwarp_of_preStoppedWarp
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (hpure : ∀ p ∈ P.paths, (EqualInput L hL).IsTargetPure p)
    (hstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source))
    (build : ∀
      (q : FinitePath (EqualInput L hL).lambda.graph)
      (hq : q ∈ ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths)
      (Q : Popular.XSWarp
        (EqualInput L hL).lambda (EqualInput L hL).lambda.target),
      Q.paths ⊆ ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths →
      (∀ p ∈ Q.paths, (EqualInput L hL).IsTargetPure p) →
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
          ((L.popularAuxiliaryIndexed hL).equalSubwarp Q).paths
          ((L.popularAuxiliaryIndexed hL).equalSubwarp Q).starts_in_source) →
      Q.paths.PairwiseDisjoint (EqualInput L hL).decodedVertexCarrier →
      (∀ p ∈ Q.paths,
        Disjoint p.support (collisionCarrier (EqualInput L hL) q)) →
      ∀ R : L.ReservedGroundedParent hL q
          (((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source hq),
      ∀ M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
          (EqualInput L hL)
          ((EqualInput L hL).lambda.source \ {q.start})
          (collisionCarrier (EqualInput L hL) q),
      Q.paths ⊆ M.paths →
        Nonempty (L.EqualMaximalPreStoppedWarp hL q
          (((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source hq)
          R M)) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  obtain ⟨q, hq, Q, hQP, hQpure, hQstat, hQdisjoint, hQavoid⟩ :=
    L.exists_reserved_targetPure_stationary_equalSubwarp hL P hpure hstat
  obtain ⟨R⟩ := L.reservedGroundedParent_nonempty hL q
    (((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source hq)
  obtain ⟨M, hQM⟩ :=
    L.exists_reservedMaximalDecodedTargetPureAvoidingSupply hL q Q
      hQdisjoint hQpure hQavoid
  exact (build q hq Q hQP hQpure hQstat hQdisjoint hQavoid R M hQM).some
    |>.exists_hindrance

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.EqualMaximalPreStoppedWarp.assertion822Output
#print axioms
  Erdos599.DWeb.KappaLadder.EqualMaximalPreStoppedWarp.exists_hindrance
#print axioms
  Erdos599.DWeb.KappaLadder.exists_hindrance_of_targetPure_stationary_equalSubwarp_of_preStoppedWarp
