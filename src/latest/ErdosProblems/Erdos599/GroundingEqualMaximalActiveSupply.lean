/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualActiveClosureOutput
import ErdosProblems.Erdos599.GroundingEqualTargetPureMaximalWarp
import ErdosProblems.Erdos599.GroundingEqualDecodedMaximalWarp

/-!
# Collision-safe maximal route supply for the equal active closure

This file specializes the target-pure avoiding Zorn family to the stationary
equal-stage thinning output.  The thinned warp `Q` avoids the complete
collision carrier of a reserved path `q`.  Hence its maximal extension may
use every auxiliary source except `q.start`, and every path in the extension
still decodes disjointly from the reserved grounded parent.
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

abbrev EqualInput
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance) :=
  L.popularAuxiliaryInput hL.legal

/-- The target-pure maximal avoiding family supplied by a reserved stationary
equal-stage selection. -/
theorem exists_reservedMaximalTargetPureAvoidingSupply
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (q : FinitePath (EqualInput L hL).lambda.graph)
    (Q : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (hQpure : ∀ p ∈ Q.paths, (EqualInput L hL).IsTargetPure p)
    (hQavoid : ∀ p ∈ Q.paths,
      Disjoint p.support (collisionCarrier (EqualInput L hL) q)) :
    ∃ M : Popular.MaximalTargetPureAvoidingRestrictedXSWarp
        (EqualInput L hL)
        ((EqualInput L hL).lambda.source \ {q.start})
        (collisionCarrier (EqualInput L hL) q),
      Q.paths ⊆ M.paths := by
  apply Q.exists_maximalTargetPureAvoiding_reserving
  · exact Or.inl (Or.inl q.start_mem_support)
  · exact fun {_} hp ↦ hQpure _ hp
  · exact fun {_} hp ↦ hQavoid _ hp

/-- Strengthened maximal supply which preserves pairwise decoded-carrier
disjointness and hence directly supports the canonical repaired relation. -/
theorem exists_reservedMaximalDecodedTargetPureAvoidingSupply
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (q : FinitePath (EqualInput L hL).lambda.graph)
    (Q : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (hQdisjoint : Q.paths.PairwiseDisjoint
      (EqualInput L hL).decodedVertexCarrier)
    (hQpure : ∀ p ∈ Q.paths, (EqualInput L hL).IsTargetPure p)
    (hQavoid : ∀ p ∈ Q.paths,
      Disjoint p.support (collisionCarrier (EqualInput L hL) q)) :
    ∃ M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
        (EqualInput L hL)
        ((EqualInput L hL).lambda.source \ {q.start})
        (collisionCarrier (EqualInput L hL) q),
      Q.paths ⊆ M.paths := by
  apply Q.exists_maximalDecodedTargetPureAvoiding_reserving
  · exact hQdisjoint
  · exact Or.inl (Or.inl q.start_mem_support)
  · exact fun {_} hp ↦ hQpure _ hp
  · exact fun {_} hp ↦ hQavoid _ hp

namespace ReservedMaximalTargetPureAvoidingSupply

variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
  {q : FinitePath (EqualInput L hL).lambda.graph}

/-- Forget the maximal supply down to the auxiliary source--target warp used
by the erased decoder. -/
def toXSWarp
    (M : Popular.MaximalTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :
    Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target :=
  M.toXSWarp fun _ hx ↦ hx.1

@[simp] theorem toXSWarp_paths
    (M : Popular.MaximalTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :
    (toXSWarp M).paths = M.paths := rfl

/-- Every route in the maximal supply is target-pure. -/
theorem targetPure
    (M : Popular.MaximalTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :
    ∀ p ∈ (toXSWarp M).paths,
      (EqualInput L hL).IsTargetPure p :=
  fun _ hp ↦ M.paths_targetPure hp

/-- The complete auxiliary carrier of the maximal supply avoids the reserved
collision carrier. -/
theorem carrier_disjoint
    (M : Popular.MaximalTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :
    Disjoint (Popular.finiteVertexSet M.paths)
      (collisionCarrier (EqualInput L hL) q) :=
  M.finiteVertexSet_disjoint

/-- After choosing the grounded parent exposed by `q`, every decoded carrier
in the maximal supply is disjoint from that parent. -/
theorem decodedCarriers_disjoint_reservedParent
    {hqsource : q.start ∈ (EqualInput L hL).lambda.source}
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :
    ∀ p ∈ (toXSWarp M).paths,
      Disjoint ((EqualInput L hL).decodedVertexCarrier p)
        R.parent.support := by
  apply R.decodedCarriers_disjoint (toXSWarp M)
  intro p hp
  exact M.paths_avoid hp

/-- Consequently no canonical inserted forward edge from the maximal supply
is incident with the reserved parent. -/
theorem forwardEdges_endpoints_not_mem_reservedParent
    {hqsource : q.start ∈ (EqualInput L hL).lambda.source}
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    {e : V × V}
    (he : e ∈ canonicalErasedForwardEdges
      (EqualInput L hL) (toXSWarp M)) :
    e.1 ∉ R.parent.support ∧ e.2 ∉ R.parent.support := by
  apply R.forwardEdges_endpoints_not_mem (toXSWarp M)
  · intro p hp
    exact M.paths_avoid hp
  · exact he

end ReservedMaximalTargetPureAvoidingSupply

namespace ReservedMaximalDecodedActiveSupply

variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
  {q : FinitePath (EqualInput L hL).lambda.graph}

def toXSWarp
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :
    Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target :=
  M.toXSWarp fun _ hx ↦ hx.1

@[simp] theorem toXSWarp_paths
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :
    (toXSWarp M).paths = M.paths := rfl

theorem decodedCarriers_pairwiseDisjoint
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :
    (toXSWarp M).paths.PairwiseDisjoint
      (EqualInput L hL).decodedVertexCarrier :=
  M.decoded_disjoint

theorem canonicalRepairedEdges_biUnique
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈
      canonicalErasedRepairedEdges (EqualInput L hL) (toXSWarp M)) :=
  canonicalErasedRepairedEdges_biUnique
    (EqualInput L hL) (toXSWarp M) M.decoded_disjoint

theorem decodedCarriers_disjoint_reservedParent
    {hqsource : q.start ∈ (EqualInput L hL).lambda.source}
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :
    ∀ p ∈ (toXSWarp M).paths,
      Disjoint ((EqualInput L hL).decodedVertexCarrier p)
        R.parent.support := by
  apply R.decodedCarriers_disjoint (toXSWarp M)
  intro p hp
  exact M.paths_avoid hp

theorem forwardEdges_endpoints_not_mem_reservedParent
    {hqsource : q.start ∈ (EqualInput L hL).lambda.source}
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    {e : V × V}
    (he : e ∈ canonicalErasedForwardEdges
      (EqualInput L hL) (toXSWarp M)) :
    e.1 ∉ R.parent.support ∧ e.2 ∉ R.parent.support := by
  apply R.forwardEdges_endpoints_not_mem (toXSWarp M)
  · intro p hp
    exact M.paths_avoid hp
  · exact he

/-- Nearest final constructor for the decoded-compatible maximal family.
Adjacency, bi-uniqueness, terminal sinks, and preservation of the reserved
parent are discharged by the supply invariants.  Only source reachability of
the essential terminal cut remains for the absorption argument. -/
theorem ReservedGroundedParent.equalActiveClosureOutput_of_maximalDecoded_sourceRooted
    {hqsource : q.start ∈ (EqualInput L hL).lambda.source}
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    (hroot : ∀ b ∈ (EqualInput L hL).terminalCut,
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
            (EqualInput L hL) (toXSWarp M)) a b) :
    Nonempty (L.EqualActiveClosureOutput hL) := by
  apply R.equalActiveClosureOutput_of_sourceRooted_of_noOutgoing
    (canonicalErasedRepairedEdges (EqualInput L hL) (toXSWarp M))
  · exact canonicalErasedRepairedEdges_subset_adj
      (EqualInput L hL) (toXSWarp M)
  · exact canonicalRepairedEdges_biUnique M
  · intro b hb
    exact terminalCut_noOutgoing_canonicalErasedRepairedEdges
      L hL (toXSWarp M) hb
  · exact hroot
  · intro e he htail
    exact R.repairedEdge_head_mem (toXSWarp M)
      (fun _ hp ↦ M.paths_avoid hp) htail he

end ReservedMaximalDecodedActiveSupply

/-- End-to-end equal-stage reduction through the collision-safe maximal
decoded supply.  The callback receives the reserved stationary selection and
its maximal extension, but its only geometric obligation is source
reachability of the essential terminal cut in the canonical repaired
relation.  All construction and compatibility fields are supplied here. -/
theorem exists_hindrance_of_targetPure_stationary_equalSubwarp_of_maximalDecoded_sourceRooted
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (hpure : ∀ p ∈ P.paths, (EqualInput L hL).IsTargetPure p)
    (hstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source))
    (sourceRooted : ∀
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
      ∀ b ∈ (EqualInput L hL).terminalCut,
        ∃ a ∈ Gamma.source,
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
              (EqualInput L hL)
              (ReservedMaximalDecodedActiveSupply.toXSWarp M)) a b) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  apply
    L.exists_hindrance_of_targetPure_stationary_equalSubwarp_of_activeClosureOutput
      hL P hpure hstat
  intro q hq Q hQP hQpure hQstat hQdisjoint hQavoid R
  obtain ⟨M, hQM⟩ :=
    L.exists_reservedMaximalDecodedTargetPureAvoidingSupply hL q Q
      hQdisjoint hQpure hQavoid
  exact
    ReservedMaximalDecodedActiveSupply.ReservedGroundedParent.equalActiveClosureOutput_of_maximalDecoded_sourceRooted
      R M
      (sourceRooted q hq Q hQP hQpure hQstat hQdisjoint hQavoid R M hQM)

end KappaLadder
end DWeb
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.exists_reservedMaximalTargetPureAvoidingSupply
#print axioms Erdos599.DWeb.KappaLadder.exists_reservedMaximalDecodedTargetPureAvoidingSupply
#print axioms Erdos599.DWeb.KappaLadder.ReservedMaximalTargetPureAvoidingSupply.decodedCarriers_disjoint_reservedParent
#print axioms Erdos599.DWeb.KappaLadder.ReservedMaximalTargetPureAvoidingSupply.forwardEdges_endpoints_not_mem_reservedParent
#print axioms Erdos599.DWeb.KappaLadder.ReservedMaximalDecodedActiveSupply.canonicalRepairedEdges_biUnique
#print axioms Erdos599.DWeb.KappaLadder.ReservedMaximalDecodedActiveSupply.ReservedGroundedParent.equalActiveClosureOutput_of_maximalDecoded_sourceRooted
#print axioms Erdos599.DWeb.KappaLadder.exists_hindrance_of_targetPure_stationary_equalSubwarp_of_maximalDecoded_sourceRooted
