/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualMaximalCollisionIntegration
import ErdosProblems.Erdos599.GroundingEqualReservedCutDisjoint
import ErdosProblems.Erdos599.GroundingMinimalSeparatingBoundary

/-!
# Minimal-frontier integration for the equal-stage maximal collision cut

The corrected target-plus-collision boundary is an original-web separator,
but a switched component can meet the full boundary more than once.  The
final relation therefore stops at a globally minimal separating subfrontier.
This file packages that normalization and retains the full-boundary output as
a specialization.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder

open _root_.Erdos599.DirectedPath
open GroundingEqualActiveSelection GroundingSimultaneousDecode

/-- Ambient switched-relation output stopped at one separating subfrontier
of the corrected equal-stage collision boundary. -/
structure EqualMaximalCollisionFrontierOutput
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (q : FinitePath (EqualInput L hL).lambda.graph)
    (hqsource : q.start ∈ (EqualInput L hL).lambda.source)
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    (T : Set V) where
  frontier_subset : T ⊆
    GroundingCut.BB (EqualInput L hL)
      (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths)
  frontier_separator : Popular.IsSeparator Gamma T
  edges : Set (V × V)
  edges_subset_adj : edges ⊆ {e | Gamma.graph.Adj e.1 e.2}
  biUnique : Relator.BiUnique fun x y ↦ (x, y) ∈ edges
  noOutgoing : ∀ t ∈ T, ¬ Alternating.HasOutgoing edges t
  frontier_rooted : ∀ t ∈ T,
    ∃ a ∈ Gamma.source \ {R.parent.initial},
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ edges) a t

namespace EqualMaximalCollisionFrontierOutput

variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
  {q : FinitePath (EqualInput L hL).lambda.graph}
  {hqsource : q.start ∈ (EqualInput L hL).lambda.source}
  {R : L.ReservedGroundedParent hL q hqsource}
  {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
    (EqualInput L hL)
    ((EqualInput L hL).lambda.source \ {q.start})
    (collisionCarrier (EqualInput L hL) q)}
  {T : Set V}

/-- Compile a rooted stopped frontier to an ordinary hindrance. -/
theorem exists_hindrance
    (O : L.EqualMaximalCollisionFrontierOutput hL q hqsource R M T) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  apply
    GroundingRootedReachabilityHindrance.exists_hindrance_of_rootedSeparatingAntichain
      O.edges (Gamma.source \ {R.parent.initial}) T
      (unused := R.parent.initial)
  · exact O.edges_subset_adj
  · exact O.biUnique
  · exact Set.sdiff_subset
  · exact isReachabilityAntichain_of_noOutgoing O.noOutgoing
  · exact O.frontier_rooted
  · exact O.frontier_separator
  · exact R.parent_initial_source
  · simp

end EqualMaximalCollisionFrontierOutput

namespace EqualMaximalCollisionCutOutput

variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
  {q : FinitePath (EqualInput L hL).lambda.graph}
  {hqsource : q.start ∈ (EqualInput L hL).lambda.source}
  {R : L.ReservedGroundedParent hL q hqsource}
  {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
    (EqualInput L hL)
    ((EqualInput L hL).lambda.source \ {q.start})
    (collisionCarrier (EqualInput L hL) q)}

/-- The former whole-boundary interface is the special case whose frontier
is the complete corrected boundary. -/
def toFrontierOutput
    (O : L.EqualMaximalCollisionCutOutput hL q hqsource R M) :
    L.EqualMaximalCollisionFrontierOutput hL q hqsource R M
      (GroundingCut.BB (EqualInput L hL)
        (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths)) where
  frontier_subset := Set.Subset.rfl
  frontier_separator :=
    reservedMaximalTargetCollisionCut_BB_isSeparator L hL M.paths
  edges := O.edges
  edges_subset_adj := O.edges_subset_adj
  biUnique := O.biUnique
  noOutgoing := O.noOutgoing
  frontier_rooted := O.boundary_rooted

end EqualMaximalCollisionCutOutput

/-- Every selected subfrontier of the corrected collision boundary remains
disjoint from the reserved grounded parent. -/
theorem ReservedGroundedParent.frontier_disjoint_parent
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {q : FinitePath (EqualInput L hL).lambda.graph}
    {hqsource : q.start ∈ (EqualInput L hL).lambda.source}
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    {T : Set V}
    (hT : T ⊆ GroundingCut.BB (EqualInput L hL)
      (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths)) :
    Disjoint T R.parent.support :=
  (R.BB_targetCollisionCut_disjoint_parent M).mono hT Set.Subset.rfl

/-! ## The canonical repaired relation stopped at the chosen frontier -/

/-- Remove every outgoing edge whose tail is already in the chosen
frontier.  Unlike a route-local truncation, this definition applies uniformly
to both residual ladder edges and inserted decoded forward edges. -/
def canonicalErasedRepairedEdgesAt
    {I : Type u} (J : PopularAuxiliary.Input Gamma I)
    (Q : Popular.XSWarp J.lambda J.lambda.target) (T : Set V) :
    Set (V × V) :=
  canonicalErasedRepairedEdges J Q \ {e | e.1 ∈ T}

/-- Reachability to an antichain point survives deleting every edge leaving
the antichain.  A simple normalized realization cannot encounter the
antichain earlier: such a point would reach the endpoint and hence equal it,
contradicting simplicity of the remaining outgoing edge. -/
theorem reflTransGen_stopped_of_reachabilityAntichain
    {E : Set (V × V)} {T : Set V} {a t : V}
    (hEadj : E ⊆ {e | Gamma.graph.Adj e.1 e.2})
    (hanti : GroundingRootedReachabilityWarp.IsReachabilityAntichain E T)
    (ht : t ∈ T)
    (hat : Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a t) :
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ E \ {e | e.1 ∈ T}) a t := by
  obtain ⟨P⟩ :=
    GroundingRootedReachabilityWarp.exists_rootedPath_of_reflTransGen
      (Gamma := Gamma) hEadj
      (A := {a}) ⟨a, Set.mem_singleton a, hat⟩
  have hstart : P.path.start = a := by
    simpa only [Set.mem_singleton_iff] using P.start_mem
  have hedges : P.path.edgeSet ⊆ E \ {e | e.1 ∈ T} := by
    intro e hePath
    refine ⟨P.edgeSet_subset hePath, ?_⟩
    intro heTail
    have htailT : e.1 ∈ T := heTail
    have htailSupport : e.1 ∈ P.path.support :=
      (P.path.edgeSet_subset_support_prod hePath).1
    have htailNeFinish : e.1 ≠ P.path.finish :=
      _root_.Erdos599.Alternating.FinitePath.source_ne_finish_of_mem_edgeSet
        P.path hePath
    have htailReach : Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ E) e.1 t := by
      simpa only [P.finish_eq] using
        (GroundingRootedReachabilityWarp.finitePath_reaches_finish_of_mem_support
          P.path P.edgeSet_subset htailSupport)
    have htailEq : e.1 = t := hanti htailT ht htailReach
    exact htailNeFinish (htailEq.trans P.finish_eq.symm)
  have hreach :=
    GroundingRootedReachabilityWarp.finitePath_start_reaches_of_mem_support
      P.path hedges P.path.finish_mem_support
  simpa only [hstart, P.finish_eq] using hreach

theorem canonicalErasedRepairedEdgesAt_subset_adj
    {I : Type u} (J : PopularAuxiliary.Input Gamma I)
    (Q : Popular.XSWarp J.lambda J.lambda.target) (T : Set V) :
    canonicalErasedRepairedEdgesAt J Q T ⊆
      {e | Gamma.graph.Adj e.1 e.2} := by
  exact Set.Subset.trans Set.sdiff_subset
    (canonicalErasedRepairedEdges_subset_adj J Q)

theorem canonicalErasedRepairedEdgesAt_biUnique
    {I : Type u} (J : PopularAuxiliary.Input Gamma I)
    (Q : Popular.XSWarp J.lambda J.lambda.target) (T : Set V)
    (hQ : Q.paths.PairwiseDisjoint J.decodedVertexCarrier) :
    Relator.BiUnique fun x y ↦
      (x, y) ∈ canonicalErasedRepairedEdgesAt J Q T := by
  have hbi := canonicalErasedRepairedEdges_biUnique J Q hQ
  constructor
  · intro x y z hxz hyz
    exact hbi.1 hxz.1 hyz.1
  · intro x y z hxy hxz
    exact hbi.2 hxy.1 hxz.1

theorem canonicalErasedRepairedEdgesAt_noOutgoing
    {I : Type u} (J : PopularAuxiliary.Input Gamma I)
    (Q : Popular.XSWarp J.lambda J.lambda.target) (T : Set V)
    {t : V} (ht : t ∈ T) :
    ¬ Alternating.HasOutgoing (canonicalErasedRepairedEdgesAt J Q T) t := by
  rintro ⟨y, _hty, hnotStopped⟩
  exact hnotStopped ht

/-- Nearest constructor for the minimal-frontier output.  The canonical
maximal decoded relation supplies adjacency and bi-uniqueness, while stopping
at `T` supplies the sink condition.  Only rooted reachability in that stopped
relation remains. -/
theorem ReservedGroundedParent.equalMaximalCollisionFrontierOutput_of_canonicalRooted
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {q : FinitePath (EqualInput L hL).lambda.graph}
    {hqsource : q.start ∈ (EqualInput L hL).lambda.source}
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    (T : Set V)
    (hTsub : T ⊆ GroundingCut.BB (EqualInput L hL)
      (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths))
    (hTsep : Popular.IsSeparator Gamma T)
    (hroot : ∀ t ∈ T,
      ∃ a ∈ Gamma.source \ {R.parent.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdgesAt
            (EqualInput L hL)
            (ReservedMaximalDecodedActiveSupply.toXSWarp M) T) a t) :
    Nonempty (L.EqualMaximalCollisionFrontierOutput
      hL q hqsource R M T) := by
  exact ⟨{
    frontier_subset := hTsub
    frontier_separator := hTsep
    edges := canonicalErasedRepairedEdgesAt (EqualInput L hL)
      (ReservedMaximalDecodedActiveSupply.toXSWarp M) T
    edges_subset_adj := canonicalErasedRepairedEdgesAt_subset_adj
      (EqualInput L hL)
      (ReservedMaximalDecodedActiveSupply.toXSWarp M) T
    biUnique := canonicalErasedRepairedEdgesAt_biUnique
      (EqualInput L hL)
      (ReservedMaximalDecodedActiveSupply.toXSWarp M) T M.decoded_disjoint
    noOutgoing := fun _ ht ↦ canonicalErasedRepairedEdgesAt_noOutgoing
      (EqualInput L hL)
      (ReservedMaximalDecodedActiveSupply.toXSWarp M) T ht
    frontier_rooted := hroot }⟩

/-- Full-source rootedness suffices for the canonical stopped relation.  A
root equal to the reserved source would remain on the reserved parent even
in the unstopped repaired relation, whereas the chosen frontier is disjoint
from that parent. -/
theorem ReservedGroundedParent.equalMaximalCollisionFrontierOutput_of_canonicalSourceRooted
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {q : FinitePath (EqualInput L hL).lambda.graph}
    {hqsource : q.start ∈ (EqualInput L hL).lambda.source}
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    (T : Set V)
    (hTsub : T ⊆ GroundingCut.BB (EqualInput L hL)
      (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths))
    (hTsep : Popular.IsSeparator Gamma T)
    (hroot : ∀ t ∈ T,
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdgesAt
            (EqualInput L hL)
            (ReservedMaximalDecodedActiveSupply.toXSWarp M) T) a t) :
    Nonempty (L.EqualMaximalCollisionFrontierOutput
      hL q hqsource R M T) := by
  apply R.equalMaximalCollisionFrontierOutput_of_canonicalRooted
    M T hTsub hTsep
  intro t ht
  obtain ⟨a, haSource, hat⟩ := hroot t ht
  have haNe : a ≠ R.parent.initial := by
    intro haEq
    subst a
    have hfull : Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (EqualInput L hL)
          (ReservedMaximalDecodedActiveSupply.toXSWarp M))
        R.parent.initial t :=
      Relation.ReflTransGen.mono
        (r := fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdgesAt
          (EqualInput L hL)
          (ReservedMaximalDecodedActiveSupply.toXSWarp M) T)
        (p := fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (EqualInput L hL)
          (ReservedMaximalDecodedActiveSupply.toXSWarp M))
        (fun _ _ hxy ↦ hxy.1) R.parent.initial t hat
    have htParent : t ∈ R.parent.support :=
      R.reachable_mem_support
        (ReservedMaximalDecodedActiveSupply.toXSWarp M)
        (fun _ hp ↦ M.paths_avoid hp) hfull
    exact Set.disjoint_left.1 (R.frontier_disjoint_parent M hTsub)
      ht htParent
  exact ⟨a, ⟨haSource, by simpa only [Set.mem_singleton_iff] using haNe⟩,
    hat⟩

/-- If the selected frontier is already an antichain in the unstopped
canonical repaired relation, it is enough to root it there.  Simple path
normalization transfers those witnesses to the stopped relation. -/
theorem ReservedGroundedParent.equalMaximalCollisionFrontierOutput_of_canonicalAntichainRooted
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {q : FinitePath (EqualInput L hL).lambda.graph}
    {hqsource : q.start ∈ (EqualInput L hL).lambda.source}
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    (T : Set V)
    (hTsub : T ⊆ GroundingCut.BB (EqualInput L hL)
      (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths))
    (hTsep : Popular.IsSeparator Gamma T)
    (hanti : GroundingRootedReachabilityWarp.IsReachabilityAntichain
      (canonicalErasedRepairedEdges (EqualInput L hL)
        (ReservedMaximalDecodedActiveSupply.toXSWarp M)) T)
    (hroot : ∀ t ∈ T,
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
            (EqualInput L hL)
            (ReservedMaximalDecodedActiveSupply.toXSWarp M)) a t) :
    Nonempty (L.EqualMaximalCollisionFrontierOutput
      hL q hqsource R M T) := by
  apply R.equalMaximalCollisionFrontierOutput_of_canonicalSourceRooted
    M T hTsub hTsep
  intro t ht
  obtain ⟨a, haSource, hat⟩ := hroot t ht
  refine ⟨a, haSource, ?_⟩
  exact reflTransGen_stopped_of_reachabilityAntichain
    (canonicalErasedRepairedEdges_subset_adj (EqualInput L hL)
      (ReservedMaximalDecodedActiveSupply.toXSWarp M))
    hanti ht hat

/-- The corrected collision boundary contains a globally minimal separating
subfrontier. -/
theorem exists_reservedMaximalTargetCollisionFrontier
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    {q : FinitePath (EqualInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :
    ∃ T : Set V,
      T ⊆ GroundingCut.BB (EqualInput L hL)
        (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths) ∧
      Popular.IsSeparator Gamma T ∧
      CardinalInduction.IsMinimalSeparatorFrom Gamma Gamma.source T := by
  apply GroundingMinimalSeparatingBoundary.exists_minimalSeparatingSubset
  exact reservedMaximalTargetCollisionCut_BB_isSeparator L hL M.paths

/-- End-to-end reduction of the stationary target-pure equal branch to a
rooted switched relation stopped at a minimal separating subfrontier of the
corrected maximal collision boundary. -/
theorem exists_hindrance_of_targetPure_stationary_equalSubwarp_of_maximalCollisionFrontier
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
      ∀ T : Set V,
      T ⊆ GroundingCut.BB (EqualInput L hL)
        (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths) →
      Popular.IsSeparator Gamma T →
      CardinalInduction.IsMinimalSeparatorFrom Gamma Gamma.source T →
      Nonempty (L.EqualMaximalCollisionFrontierOutput hL q
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
  obtain ⟨T, hTsub, hTsep, hTmin⟩ :=
    L.exists_reservedMaximalTargetCollisionFrontier hL M
  exact
    (buildOutput q hq Q hQP hQpure hQstat hQdisjoint hQavoid R M hQM
      T hTsub hTsep hTmin).some.exists_hindrance

end KappaLadder
end DWeb
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.EqualMaximalCollisionFrontierOutput.exists_hindrance
#print axioms Erdos599.DWeb.KappaLadder.ReservedGroundedParent.equalMaximalCollisionFrontierOutput_of_canonicalRooted
#print axioms Erdos599.DWeb.KappaLadder.ReservedGroundedParent.equalMaximalCollisionFrontierOutput_of_canonicalSourceRooted
#print axioms Erdos599.DWeb.KappaLadder.ReservedGroundedParent.equalMaximalCollisionFrontierOutput_of_canonicalAntichainRooted
#print axioms Erdos599.DWeb.KappaLadder.exists_reservedMaximalTargetCollisionFrontier
#print axioms Erdos599.DWeb.KappaLadder.exists_hindrance_of_targetPure_stationary_equalSubwarp_of_maximalCollisionFrontier
