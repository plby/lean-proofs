/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualTargetPreStoppedCompiler
import ErdosProblems.Erdos599.GroundingMinimalSeparatingBoundary

/-!
# Minimal reachable target compiler for the equal grounding branch

The entire source-reachable terminal cut is a separator, but it need not be
the right boundary for one locally bi-unique rooted relation: distinct
reachable terminals may lie beyond a common branching source.  We therefore
first choose an inclusion-minimal separator inside that cut and stop the
active relation only at this selected target boundary.

The collision hull remains routing metadata.  It is not part of the output
boundary.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace DWeb.KappaLadder

open GroundingEqualActiveSelection
open GroundingEqualMaximalCollisionRecursion
open GroundingMinimalSeparatingBoundary
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

/-- A selected minimal separator inside the source-reachable essential
terminal cut. -/
structure MinimalReachableTargetBoundary
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance) where
  vertices : Set V
  subset_reachableTerminalCut : vertices ⊆ reachableTerminalCut L hL
  separates : Popular.IsSeparator Gamma vertices
  minimal : CardinalInduction.IsMinimalSeparatorFrom
    Gamma Gamma.source vertices

/-- The reachable terminal cut contains a minimal separating target
boundary. -/
theorem exists_minimalReachableTargetBoundary
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance) :
    Nonempty (L.MinimalReachableTargetBoundary hL) := by
  obtain ⟨T, hTsub, hTsep, hTmin⟩ :=
    exists_minimalSeparatingSubset (reachableTerminalCut L hL)
      (reachableTerminalCut_isSeparator L hL)
  exact ⟨⟨T, hTsub, hTsep, hTmin⟩⟩

/-- Exact active-closure interface at a selected minimal target boundary.

The well-founded collision-owner recursion roots the routing stops.  The
last field absorbs precisely the selected target boundary, rather than every
reachable terminal. -/
structure EqualMinimalTargetPreStoppedCompiler
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (q : FinitePath (EqualInput L hL).lambda.graph)
    (hqsource : q.start ∈ (EqualInput L hL).lambda.source)
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    (T : L.MinimalReachableTargetBoundary hL) where
  edges : Set (V × V)
  edges_subset_adj : edges ⊆ {e | Gamma.graph.Adj e.1 e.2}
  edges_biUnique : Relator.BiUnique fun x y ↦ (x, y) ∈ edges
  target_noOutgoing : ∀ b ∈ T.vertices,
    ¬ Alternating.HasOutgoing edges b
  self_beforeOwner_subset : ∀ r : WarpPath (MaximalWarp M),
    collisionOwner hL (MaximalWarp M) r = r →
      canonicalErasedRepairedEdges (EqualInput L hL)
        (GroundingEqualMaximalCollisionForest.routesBeforeIndex
          L hL (MaximalWarp M)
          (warpPathIndex (L.popularAuxiliaryIndexed hL)
            (MaximalWarp M) (collisionOwner hL (MaximalWarp M) r))) ⊆ edges
  absorb_stop : ∀ r : WarpPath (MaximalWarp M),
    collisionOwner hL (MaximalWarp M) r ≠ r →
      TargetCollisionStopRooted hL R M edges
        (collisionOwner hL (MaximalWarp M) r) →
      TargetCollisionStopRooted hL R M edges r
  absorb_target : ∀ b ∈ T.vertices,
    ∃ r : WarpPath (MaximalWarp M),
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ edges)
        (collisionStop hL (MaximalWarp M) r) b

namespace EqualMinimalTargetPreStoppedCompiler

variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
  {q : FinitePath (EqualInput L hL).lambda.graph}
  {hqsource : q.start ∈ (EqualInput L hL).lambda.source}
  {R : L.ReservedGroundedParent hL q hqsource}
  {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
    (EqualInput L hL)
    ((EqualInput L hL).lambda.source \ {q.start})
    (collisionCarrier (EqualInput L hL) q)}
  {T : L.MinimalReachableTargetBoundary hL}

/-- A self-owned routing stop is rooted by the literal relation preceding
its owner transaction. -/
theorem self_stop_rooted
    (C : L.EqualMinimalTargetPreStoppedCompiler hL q hqsource R M T)
    (r : WarpPath (MaximalWarp M))
    (hself : collisionOwner hL (MaximalWarp M) r = r) :
    TargetCollisionStopRooted hL R M C.edges r := by
  refine ⟨collisionRoot hL (MaximalWarp M) r, ⟨
    collisionRoot_mem_source (hL := hL) (W := MaximalWarp M) r, ?_⟩, ?_⟩
  · simpa only [Set.mem_singleton_iff] using
      EqualMaximalPreStoppedCompiler.collisionRoot_ne_reserved
        (R := R) (M := M) r
  · exact Relation.ReflTransGen.mono
      (fun _ _ hxy ↦ C.self_beforeOwner_subset r hself hxy)
      _ _ (collisionRoot_reaches_stop_before_owner
        (hL := hL) (W := MaximalWarp M) r)

/-- Every collision stop is rooted by well-founded descent through the
selected route owner. -/
theorem all_stops_rooted
    (C : L.EqualMinimalTargetPreStoppedCompiler hL q hqsource R M T) :
    ∀ r : WarpPath (MaximalWarp M),
      TargetCollisionStopRooted hL R M C.edges r := by
  exact all_of_self_or_absorb
    (hL := hL) (W := MaximalWarp M)
    (fun r ↦ TargetCollisionStopRooted hL R M C.edges r)
    C.self_stop_rooted C.absorb_stop

/-- Every selected target is rooted from a source distinct from the reserved
source. -/
theorem target_rooted
    (C : L.EqualMinimalTargetPreStoppedCompiler hL q hqsource R M T) :
    ∀ b ∈ T.vertices,
      ∃ a ∈ Gamma.source \ {R.parent.initial},
        Relation.ReflTransGen (fun x y ↦ (x, y) ∈ C.edges) a b := by
  intro b hb
  obtain ⟨r, hrb⟩ := C.absorb_target b hb
  obtain ⟨a, ha, har⟩ := C.all_stops_rooted r
  exact ⟨a, ha, har.trans hrb⟩

/-- The selected sink boundary is a reachability antichain. -/
theorem target_isReachabilityAntichain
    (C : L.EqualMinimalTargetPreStoppedCompiler hL q hqsource R M T) :
    IsReachabilityAntichain C.edges T.vertices := by
  intro b hb c _hc hbc
  rcases hbc.cases_head with hcb | ⟨x, hbx, _hxc⟩
  · exact hcb
  · exact False.elim (C.target_noOutgoing b hb ⟨x, hbx⟩)

/-- Compile the minimal target boundary and its collision-routed active
relation to an ordinary hindrance. -/
theorem exists_hindrance
    (C : L.EqualMinimalTargetPreStoppedCompiler hL q hqsource R M T) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  exact
    GroundingRootedReachabilityHindrance.exists_hindrance_of_rootedSeparatingAntichain
      C.edges (Gamma.source \ {R.parent.initial}) T.vertices
      C.edges_subset_adj C.edges_biUnique Set.sdiff_subset
      C.target_isReachabilityAntichain C.target_rooted T.separates
      R.parent.initial R.parent_initial_source (by simp)

end EqualMinimalTargetPreStoppedCompiler

/-- End-to-end stationary equal-stage reduction to a selected minimal
target-only pre-stopped compiler. -/
theorem exists_hindrance_of_targetPure_stationary_equalSubwarp_of_minimalTargetPreStoppedCompiler
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
      ∀ T : L.MinimalReachableTargetBoundary hL,
        Nonempty (L.EqualMinimalTargetPreStoppedCompiler hL q
          (((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source hq)
          R M T)) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  obtain ⟨q, hq, Q, hQP, hQpure, hQstat, hQdisjoint, hQavoid⟩ :=
    L.exists_reserved_targetPure_stationary_equalSubwarp hL P hpure hstat
  obtain ⟨R⟩ := L.reservedGroundedParent_nonempty hL q
    (((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source hq)
  obtain ⟨M, hQM⟩ :=
    L.exists_reservedMaximalDecodedTargetPureAvoidingSupply hL q Q
      hQdisjoint hQpure hQavoid
  obtain ⟨T⟩ := L.exists_minimalReachableTargetBoundary hL
  exact (build q hq Q hQP hQpure hQstat hQdisjoint hQavoid R M hQM T).some
    |>.exists_hindrance

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.exists_minimalReachableTargetBoundary
#print axioms Erdos599.DWeb.KappaLadder.EqualMinimalTargetPreStoppedCompiler.all_stops_rooted
#print axioms Erdos599.DWeb.KappaLadder.EqualMinimalTargetPreStoppedCompiler.target_rooted
#print axioms Erdos599.DWeb.KappaLadder.EqualMinimalTargetPreStoppedCompiler.exists_hindrance
#print axioms Erdos599.DWeb.KappaLadder.exists_hindrance_of_targetPure_stationary_equalSubwarp_of_minimalTargetPreStoppedCompiler
