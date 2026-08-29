/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualActiveClosureOutput
import ErdosProblems.Erdos599.GroundingEqualTargetPureMaximalWarp

/-!
# A maximal collision-safe reservoir for the equal branch

The stationary selector retains a collision-free equal subwarp `Q` and
reserves a different equal path `q`.  This file extends `Q`, by Zorn, to a
target-pure auxiliary warp maximal among paths which avoid the complete
collision carrier of `q` and which do not start at `q.start`.

The resulting family is the largest route reservoir that can be decoded
without entering the reserved grounded parent.  It does not by itself claim
that the decoded relation roots the full essential terminal cut: that is the
remaining active-rerouting assertion.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open GroundingEqualActiveSelection
open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

private abbrev EqualInput
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance) :=
  L.popularAuxiliaryInput hL.legal

/-- The stationary collision-safe seed selected away from `q` has no member
starting at `q.start`. -/
theorem reservedSelection_starts_ne
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp (EqualInput L hL).lambda
      (EqualInput L hL).lambda.target)
    {q : FinitePath (EqualInput L hL).lambda.graph}
    (hq : q ∈ ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths)
    (Q : Popular.XSWarp (EqualInput L hL).lambda
      (EqualInput L hL).lambda.target)
    (hQP : Q.paths ⊆
      ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths)
    (hQavoid : ∀ p ∈ Q.paths,
      Disjoint p.support (collisionCarrier (EqualInput L hL) q)) :
    ∀ p ∈ Q.paths, p.start ≠ q.start := by
  intro p hp hpq
  let E := (L.popularAuxiliaryIndexed hL).equalSubwarp P
  have heq : p = q := E.eq_of_start_eq (hQP hp) hq hpq
  subst p
  have hdisj := hQavoid q hp
  exact Set.disjoint_left.1 hdisj q.start_mem_support
    (Or.inl (Or.inl q.start_mem_support))

/-- Extend the selected stationary seed to a target-pure maximal family
which is still completely isolated from the reserved collision carrier. -/
theorem exists_maximalTargetPureClosure_of_reservedSelection
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp (EqualInput L hL).lambda
      (EqualInput L hL).lambda.target)
    {q : FinitePath (EqualInput L hL).lambda.graph}
    (hq : q ∈ ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths)
    (Q : Popular.XSWarp (EqualInput L hL).lambda
      (EqualInput L hL).lambda.target)
    (hQP : Q.paths ⊆
      ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths)
    (hQpure : ∀ p ∈ Q.paths, (EqualInput L hL).IsTargetPure p)
    (hQavoid : ∀ p ∈ Q.paths,
      Disjoint p.support (collisionCarrier (EqualInput L hL) q)) :
    ∃ M : Popular.MaximalTargetPureAvoidingRestrictedXSWarp
        (EqualInput L hL)
        ((EqualInput L hL).lambda.source \ {q.start})
        (collisionCarrier (EqualInput L hL) q),
      Q.paths ⊆ M.paths := by
  apply Q.exists_maximalTargetPureAvoidingRestricted_extension
  · intro p hp
    exact ⟨Q.starts_in_source hp, by
      simpa only [Set.mem_singleton_iff] using
        L.reservedSelection_starts_ne hL P hq Q hQP hQavoid p hp⟩
  · intro p hp
    exact hQpure p hp
  · intro p hp
    exact hQavoid p hp

/-- Every maximal-reservoir route has decoded carrier disjoint from the
reserved grounded parent. -/
theorem ReservedGroundedParent.maximalClosure_decodedCarriers_disjoint
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {q : FinitePath (EqualInput L hL).lambda.graph}
    {hqsource : q.start ∈ (EqualInput L hL).lambda.source}
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :
    ∀ p ∈ M.paths,
      Disjoint ((EqualInput L hL).decodedVertexCarrier p)
        R.parent.support := by
  let W : Popular.XSWarp (EqualInput L hL).lambda
      (EqualInput L hL).lambda.target :=
    M.toXSWarp Set.diff_subset
  exact R.decodedCarriers_disjoint W (by
    intro p hp
    change p ∈ M.paths at hp
    exact M.paths_avoid hp)

/-- End-to-end reduction of the stationary target-pure equal branch to an
active closure built over a maximal target-pure collision-safe reservoir.

All selection, stationarity, target-purity, reservation, and Zorn-extension
steps are discharged here.  The callback is left only the genuine ambient
construction: it must turn this route reservoir into the relation-level
`EqualActiveClosureOutput`.
-/
theorem exists_hindrance_of_targetPure_stationary_equalSubwarp_of_maximalClosure
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp (EqualInput L hL).lambda
      (EqualInput L hL).lambda.target)
    (hpure : ∀ p ∈ P.paths, (EqualInput L hL).IsTargetPure p)
    (hstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source))
    (activeClosure : ∀
      (q : FinitePath (EqualInput L hL).lambda.graph)
      (hq : q ∈ ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths)
      (Q : Popular.XSWarp (EqualInput L hL).lambda
        (EqualInput L hL).lambda.target),
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
      ∀ M : Popular.MaximalTargetPureAvoidingRestrictedXSWarp
          (EqualInput L hL)
          ((EqualInput L hL).lambda.source \ {q.start})
          (collisionCarrier (EqualInput L hL) q),
        Q.paths ⊆ M.paths → Nonempty (L.EqualActiveClosureOutput hL)) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  obtain ⟨q, hq, Q, hQP, hQpure, hQstat, hQdisjoint, hQavoid⟩ :=
    L.exists_reserved_targetPure_stationary_equalSubwarp hL P hpure hstat
  obtain ⟨R⟩ := L.reservedGroundedParent_nonempty hL q
    (((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source hq)
  obtain ⟨M, hQM⟩ :=
    L.exists_maximalTargetPureClosure_of_reservedSelection
      hL P hq Q hQP hQpure hQavoid
  exact (activeClosure q hq Q hQP hQpure hQstat hQdisjoint hQavoid R M hQM).some
    |>.exists_hindrance

end KappaLadder
end DWeb
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.exists_maximalTargetPureClosure_of_reservedSelection
#print axioms Erdos599.DWeb.KappaLadder.ReservedGroundedParent.maximalClosure_decodedCarriers_disjoint
#print axioms Erdos599.DWeb.KappaLadder.exists_hindrance_of_targetPure_stationary_equalSubwarp_of_maximalClosure
