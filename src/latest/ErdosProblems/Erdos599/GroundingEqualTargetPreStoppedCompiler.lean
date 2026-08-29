/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualMaximalPreStoppedCompiler
import ErdosProblems.Erdos599.GroundingEqualReachableTargetBoundary

/-!
# Target-only pre-stopped collision-closure compiler

The maximal collision hull is routing metadata, not an output cut.  Each
selected route has a collision stop and a strictly decreasing collision
owner.  A concrete active relation roots the self-owned stops, transports
rooting along the owner recursion, and finally absorbs every point of the
source-reachable essential terminal frontier.  That target-only frontier is
the separating antichain compiled to a hindrance.

This is the sound replacement for a compiler which incorrectly used the
target-plus-collision-hull `BB` itself as an antichain.
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

/-- A collision-routing stop is rooted from an allowed source in the final
active relation. -/
def TargetCollisionStopRooted
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

/-- Exact target-only active-closure interface.

The collision hull occurs only through `collisionOwner` and `collisionStop`.
The output boundary is `reachableTerminalCut`.  `absorb_target` is allowed to
route through a collision stop, but no collision point is asserted to be a
boundary point. -/
structure EqualTargetPreStoppedCompiler
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
  target_noOutgoing : ∀ b ∈ reachableTerminalCut L hL,
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
  absorb_target : ∀ b ∈ reachableTerminalCut L hL,
    ∃ r : WarpPath (MaximalWarp M),
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ edges)
        (collisionStop hL (MaximalWarp M) r) b

namespace EqualTargetPreStoppedCompiler

variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
  {q : FinitePath (EqualInput L hL).lambda.graph}
  {hqsource : q.start ∈ (EqualInput L hL).lambda.source}
  {R : L.ReservedGroundedParent hL q hqsource}
  {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
    (EqualInput L hL)
    ((EqualInput L hL).lambda.source \ {q.start})
    (collisionCarrier (EqualInput L hL) q)}

/-- A self-owned routing node is rooted by its literal relation before the
owner transaction. -/
theorem self_stop_rooted
    (C : L.EqualTargetPreStoppedCompiler hL q hqsource R M)
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

/-- Every collision stop is rooted by well-founded descent of the selected
route index. -/
theorem all_stops_rooted
    (C : L.EqualTargetPreStoppedCompiler hL q hqsource R M) :
    ∀ r : WarpPath (MaximalWarp M),
      TargetCollisionStopRooted hL R M C.edges r := by
  exact all_of_self_or_absorb
    (hL := hL) (W := MaximalWarp M)
    (fun r ↦ TargetCollisionStopRooted hL R M C.edges r)
    C.self_stop_rooted C.absorb_stop

/-- Every point of the target-only boundary is rooted from a source other
than the reserved source. -/
theorem target_rooted
    (C : L.EqualTargetPreStoppedCompiler hL q hqsource R M) :
    ∀ b ∈ reachableTerminalCut L hL,
      ∃ a ∈ Gamma.source \ {R.parent.initial},
        Relation.ReflTransGen (fun x y ↦ (x, y) ∈ C.edges) a b := by
  intro b hb
  obtain ⟨r, hrb⟩ := C.absorb_target b hb
  obtain ⟨a, ha, har⟩ := C.all_stops_rooted r
  exact ⟨a, ha, har.trans hrb⟩

/-- A sink set is automatically a reachability antichain. -/
theorem target_isReachabilityAntichain
    (C : L.EqualTargetPreStoppedCompiler hL q hqsource R M) :
    IsReachabilityAntichain C.edges (reachableTerminalCut L hL) := by
  intro b hb c _hc hbc
  rcases hbc.cases_head with hcb | ⟨x, hbx, _hxc⟩
  · exact hcb
  · exact False.elim (C.target_noOutgoing b hb ⟨x, hbx⟩)

/-- Compile the concrete collision-routed active relation to an ordinary
hindrance at the target-only boundary. -/
theorem exists_hindrance
    (C : L.EqualTargetPreStoppedCompiler hL q hqsource R M) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  exact
    GroundingRootedReachabilityHindrance.exists_hindrance_of_rootedSeparatingAntichain
      C.edges (Gamma.source \ {R.parent.initial})
      (reachableTerminalCut L hL)
      C.edges_subset_adj C.edges_biUnique Set.sdiff_subset
      C.target_isReachabilityAntichain C.target_rooted
      (reachableTerminalCut_isSeparator L hL)
      R.parent.initial R.parent_initial_source (by simp)

end EqualTargetPreStoppedCompiler

/-- End-to-end stationary equal-stage reduction to the sound target-only
pre-stopped compiler.  This has the exact `P`, target-purity, and stationary
antecedent consumed by the public grounding assembly. -/
theorem exists_hindrance_of_targetPure_stationary_equalSubwarp_of_targetPreStoppedCompiler
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
        Nonempty (L.EqualTargetPreStoppedCompiler hL q
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

#print axioms Erdos599.DWeb.KappaLadder.EqualTargetPreStoppedCompiler.all_stops_rooted
#print axioms Erdos599.DWeb.KappaLadder.EqualTargetPreStoppedCompiler.target_rooted
#print axioms Erdos599.DWeb.KappaLadder.EqualTargetPreStoppedCompiler.exists_hindrance
#print axioms Erdos599.DWeb.KappaLadder.exists_hindrance_of_targetPure_stationary_equalSubwarp_of_targetPreStoppedCompiler
