/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualCollisionBoundaryOwners
import ErdosProblems.Erdos599.GroundingEqualMaximalActiveSupply
import ErdosProblems.Erdos599.GroundingAssertion818Decoder

/-!
# Final integration interface for the equal-stage maximal collision cut

This file combines the stationary collision-safe thinning, reservation of
one grounded inessential parent, the decoded-compatible maximal Zorn
extension, and the corrected Assertion 8.18 collision boundary.

The remaining ambient construction is recorded by
`EqualMaximalCollisionCutOutput`.  Its fields are exactly the four facts
needed from the switched relation: adjacency, bi-uniqueness, no outgoing
edge at the collision boundary, and source reachability of that boundary
without the reserved original source.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder

open _root_.Erdos599.DirectedPath
open GroundingEqualActiveSelection

/-- Assertion 8.18 decodes the target-plus-selected-collision cut to an
original-web separator. -/
theorem reservedMaximalTargetCollisionCut_BB_isSeparator
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Set (FinitePath (EqualInput L hL).lambda.graph)) :
    Popular.IsSeparator Gamma
      (GroundingCut.BB (EqualInput L hL)
        (reservedMaximalTargetCollisionCut (EqualInput L hL) P)) := by
  exact GroundingAssertion818Decoder.assertion8_18 L hL.legal _
    (reservedMaximalTargetCollisionCut_isSeparator (EqualInput L hL) P)

/-- The exact ambient relation output required by the maximal collision-cut
compiler. -/
structure EqualMaximalCollisionCutOutput
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (q : FinitePath (EqualInput L hL).lambda.graph)
    (hqsource : q.start ∈ (EqualInput L hL).lambda.source)
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) where
  edges : Set (V × V)
  edges_subset_adj : edges ⊆ {e | Gamma.graph.Adj e.1 e.2}
  biUnique : Relator.BiUnique fun x y ↦ (x, y) ∈ edges
  noOutgoing : ∀ b ∈
      GroundingCut.BB (EqualInput L hL)
        (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths),
    ¬ Alternating.HasOutgoing edges b
  boundary_rooted : ∀ b ∈
      GroundingCut.BB (EqualInput L hL)
        (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths),
    ∃ a ∈ Gamma.source \ {R.parent.initial},
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ edges) a b

namespace EqualMaximalCollisionCutOutput

variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
  {q : FinitePath (EqualInput L hL).lambda.graph}
  {hqsource : q.start ∈ (EqualInput L hL).lambda.source}
  {R : L.ReservedGroundedParent hL q hqsource}
  {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
    (EqualInput L hL)
    ((EqualInput L hL).lambda.source \ {q.start})
    (collisionCarrier (EqualInput L hL) q)}

/-- Compile the packaged relation output to an ordinary hindrance. -/
theorem exists_hindrance
    (O : L.EqualMaximalCollisionCutOutput hL q hqsource R M) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  apply
    GroundingRootedReachabilityHindrance.exists_hindrance_of_rootedSeparatingAntichain
      O.edges (Gamma.source \ {R.parent.initial})
      (GroundingCut.BB (EqualInput L hL)
        (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths))
      (unused := R.parent.initial)
  · exact O.edges_subset_adj
  · exact O.biUnique
  · exact Set.sdiff_subset
  · exact isReachabilityAntichain_of_noOutgoing O.noOutgoing
  · exact O.boundary_rooted
  · exact reservedMaximalTargetCollisionCut_BB_isSeparator L hL M.paths
  · exact R.parent_initial_source
  · simp

end EqualMaximalCollisionCutOutput

/-- End-to-end reduction of the stationary target-pure equal branch to the
corrected maximal collision-cut relation output.

The callback sees the complete stationary selection, the reserved grounded
parent, and a decoded-compatible maximal extension.  It only has to build
the concrete ambient relation output; all selection, maximality, separator,
unused-source, and final hindrance arguments are internal to this theorem. -/
theorem exists_hindrance_of_targetPure_stationary_equalSubwarp_of_maximalCollisionCut
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (hpure : ∀ p ∈ P.paths, (EqualInput L hL).IsTargetPure p)
    (hstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source))
    (buildOutput : ∀
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
      Nonempty (L.EqualMaximalCollisionCutOutput hL q
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
  exact
    (buildOutput q hq Q hQP hQpure hQstat hQdisjoint hQavoid R M hQM).some
      |>.exists_hindrance

end KappaLadder
end DWeb
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.EqualMaximalCollisionCutOutput.exists_hindrance
#print axioms Erdos599.DWeb.KappaLadder.exists_hindrance_of_targetPure_stationary_equalSubwarp_of_maximalCollisionCut
