/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualMaximalCollisionRecursion
import ErdosProblems.Erdos599.GroundingEqualMaximalCollisionFrontier

/-!
# Pre-stopped compiler for the maximal equal collision forest

This is the construction boundary immediately above the ordered local
transactions.  A concrete pre-stopped relation has to preserve the
strictly-before-owner root at self nodes, absorb a node whose owner is
properly earlier, and connect every literal corrected-boundary point to one
of the resulting collision stops.  The well-founded recursion then roots
the whole boundary from original sources other than the reserved one.

The final compiler uses the full corrected `BB` literally.  It does not
pretend that the collision hull is already a one-hit transversal: the
`boundary_antichain` field is the precise component-uniqueness fact produced
by the pre-stopped construction.  Once that fact is present, finite rooted
paths give the desired hindrance directly.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace DWeb.KappaLadder

open GroundingEqualActiveSelection
open GroundingEqualMaximalCollisionForest
open GroundingEqualMaximalCollisionRecursion
open GroundingRootedReachabilityWarp

variable {kappa : Cardinal.{u}}

private abbrev MaximalWarp
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {q : FinitePath (EqualInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :=
  ReservedMaximalDecodedActiveSupply.toXSWarp M

/-- A collision stop is rooted in `E` from an allowed original source. -/
def CollisionStopRooted
    {L : Gamma.KappaLadder kappa} (hL : L.IsKappaHindrance)
    {q : FinitePath (EqualInput L hL).lambda.graph}
    {hqsource : q.start ∈ (EqualInput L hL).lambda.source}
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    (E : Set (V × V)) (r : WarpPath (MaximalWarp M)) : Prop :=
  ∃ a ∈ Gamma.source \ {R.parent.initial},
    Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a
      (collisionStop hL (MaximalWarp M) r)

/-- Concrete relation-level data produced by the ordered active closure.

`self_beforeOwner_subset` is deliberately restricted to self nodes: at a
proper node the earlier owner's transaction may replace part of the
original grounded prefix, and the `absorb_stop` field records exactly that
local replacement. -/
structure EqualMaximalPreStoppedCompiler
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
  edges_biUnique : Relator.BiUnique fun x y ↦ (x, y) ∈ edges
  boundary_antichain : IsReachabilityAntichain edges
    (GroundingCut.BB (EqualInput L hL)
      (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths))
  self_beforeOwner_subset : ∀ r : WarpPath (MaximalWarp M),
    collisionOwner hL (MaximalWarp M) r = r →
      canonicalErasedRepairedEdges (EqualInput L hL)
        (routesBeforeIndex L hL (MaximalWarp M)
          (warpPathIndex (L.popularAuxiliaryIndexed hL)
            (MaximalWarp M) (collisionOwner hL (MaximalWarp M) r))) ⊆ edges
  absorb_stop : ∀ r : WarpPath (MaximalWarp M),
    collisionOwner hL (MaximalWarp M) r ≠ r →
      CollisionStopRooted hL R M edges
        (collisionOwner hL (MaximalWarp M) r) →
      CollisionStopRooted hL R M edges r
  boundary_absorbed : ∀ b ∈
    GroundingCut.BB (EqualInput L hL)
      (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths),
    ∃ r : WarpPath (MaximalWarp M),
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ edges)
        (collisionStop hL (MaximalWarp M) r) b

namespace EqualMaximalPreStoppedCompiler

variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
  {q : FinitePath (EqualInput L hL).lambda.graph}
  {hqsource : q.start ∈ (EqualInput L hL).lambda.source}
  {R : L.ReservedGroundedParent hL q hqsource}
  {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
    (EqualInput L hL)
    ((EqualInput L hL).lambda.source \ {q.start})
    (collisionCarrier (EqualInput L hL) q)}

/-- The grounded parent chosen at a maximal route node is different from
the reserved inessential parent.  Otherwise the canonical route initial
would belong both to its decoded carrier and to the forbidden reserved
parent. -/
theorem collisionRoot_ne_reserved
    (r : WarpPath (MaximalWarp M)) :
    collisionRoot hL (MaximalWarp M) r ≠ R.parent.initial := by
  let N := activeCollisionNode hL (MaximalWarp M) r
  intro hroot
  have hparents : N.rootPrefix.parent = R.parent := by
    by_contra hne
    let J := EqualInput L hL
    have hNmem : N.rootPrefix.parent ∈ J.ladder.paths := by
      simpa only [J, EqualInput, KappaLadder.popularAuxiliaryInput] using
        N.rootPrefix.parent_inessential.1
    have hRmem : R.parent ∈ J.ladder.paths := by
      simpa only [J, EqualInput, KappaLadder.popularAuxiliaryInput] using
        R.parent_inessential.1
    have hdisj := J.ladder.disjoint hNmem hRmem hne
    exact Set.disjoint_left.1 hdisj
      N.rootPrefix.parent.initial_mem_support
      (by
        have hinit : N.rootPrefix.parent.initial = R.parent.initial :=
          (collisionRoot_eq_parent_initial
            (hL := hL) (W := MaximalWarp M) r).symm.trans hroot
        exact hinit ▸ R.parent.initial_mem_support)
  have hrouteParent :
      (canonicalErasedRoute (EqualInput L hL) (MaximalWarp M) r).initial ∈
        N.rootPrefix.parent.support := by
    rw [← N.rootPrefix.finish_eq]
    exact N.rootPrefix.support_subset N.rootPrefix.path.finish_mem_support
  have hrouteCarrier :
      (canonicalErasedRoute (EqualInput L hL) (MaximalWarp M) r).initial ∈
        (EqualInput L hL).decodedVertexCarrier r.1 :=
    (canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
      (EqualInput L hL) (MaximalWarp M) r)
        (canonicalErasedRoute (EqualInput L hL) (MaximalWarp M) r).initial_mem_vertexSet
  exact Set.disjoint_left.1
    (ReservedMaximalDecodedActiveSupply.decodedCarriers_disjoint_reservedParent
      R M r.1 r.2)
    hrouteCarrier (hparents ▸ hrouteParent)

/-- A self-owned node is rooted in the final pre-stopped relation by its
literal strict-before-owner witness. -/
theorem self_collisionStopRooted
    (C : L.EqualMaximalPreStoppedCompiler hL q hqsource R M)
    (r : WarpPath (MaximalWarp M))
    (hself : collisionOwner hL (MaximalWarp M) r = r) :
    CollisionStopRooted hL R M C.edges r := by
  refine ⟨collisionRoot hL (MaximalWarp M) r, ⟨
    collisionRoot_mem_source (hL := hL) (W := MaximalWarp M) r, ?_⟩, ?_⟩
  · simpa only [Set.mem_singleton_iff] using
      collisionRoot_ne_reserved (R := R) (M := M) r
  · exact Relation.ReflTransGen.mono
      (fun _ _ hxy ↦ C.self_beforeOwner_subset r hself hxy)
      _ _ (collisionRoot_reaches_stop_before_owner
        (hL := hL) (W := MaximalWarp M) r)

/-- Every collision stop is rooted by well-founded owner absorption. -/
theorem all_collisionStops_rooted
    (C : L.EqualMaximalPreStoppedCompiler hL q hqsource R M) :
    ∀ r : WarpPath (MaximalWarp M),
      CollisionStopRooted hL R M C.edges r := by
  exact all_of_self_or_absorb
    (hL := hL) (W := MaximalWarp M)
    (fun r ↦ CollisionStopRooted hL R M C.edges r)
    C.self_collisionStopRooted C.absorb_stop

/-- Hence every point of the literal corrected boundary is rooted from an
original source other than the reserved one. -/
theorem boundary_rooted
    (C : L.EqualMaximalPreStoppedCompiler hL q hqsource R M) :
    ∀ b ∈ GroundingCut.BB (EqualInput L hL)
      (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths),
      ∃ a ∈ Gamma.source \ {R.parent.initial},
        Relation.ReflTransGen (fun x y ↦ (x, y) ∈ C.edges) a b := by
  intro b hb
  obtain ⟨r, hrb⟩ := C.boundary_absorbed b hb
  obtain ⟨a, ha, har⟩ := C.all_collisionStops_rooted r
  exact ⟨a, ha, har.trans hrb⟩

/-- Compile the pre-stopped maximal equal closure to an ordinary
hindrance. -/
theorem exists_hindrance
    (C : L.EqualMaximalPreStoppedCompiler hL q hqsource R M) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  exact
    GroundingRootedReachabilityHindrance.exists_hindrance_of_rootedSeparatingAntichain
      C.edges (Gamma.source \ {R.parent.initial})
      (GroundingCut.BB (EqualInput L hL)
        (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths))
      C.edges_subset_adj C.edges_biUnique Set.sdiff_subset
      C.boundary_antichain C.boundary_rooted
      (reservedMaximalTargetCollisionCut_BB_isSeparator L hL M.paths)
      R.parent.initial R.parent_initial_source (by simp)

end EqualMaximalPreStoppedCompiler

/-- End-to-end stationary equal-stage reduction to the concrete
pre-stopped collision-forest compiler. -/
theorem exists_hindrance_of_targetPure_stationary_equalSubwarp_of_preStoppedCompiler
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
        Nonempty (L.EqualMaximalPreStoppedCompiler hL q
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

#print axioms Erdos599.DWeb.KappaLadder.EqualMaximalPreStoppedCompiler.collisionRoot_ne_reserved
#print axioms Erdos599.DWeb.KappaLadder.EqualMaximalPreStoppedCompiler.all_collisionStops_rooted
#print axioms Erdos599.DWeb.KappaLadder.EqualMaximalPreStoppedCompiler.exists_hindrance
#print axioms Erdos599.DWeb.KappaLadder.exists_hindrance_of_targetPure_stationary_equalSubwarp_of_preStoppedCompiler
