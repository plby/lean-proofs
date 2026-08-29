/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingEqualSelection
import ErdosProblems.Erdos599.SplitGroundingEqualStrictSelection
import ErdosProblems.Erdos599.SplitGroundingFreshRung
import ErdosProblems.Erdos599.SplitGroundingTargetPureChronology

/-!
# Stationary equal selection retaining the fresh-stage invariant

The grounded equal selector restricts a stationary equal family to grounded
source indices before performing collision thinning.  In the diagonal branch
the available stationary set is smaller: its indices are genuinely fresh
grounded stages.  This module repeats the restriction with that exact set, so
the reserved route and every retained route keep their fresh-stage witness.

This is important for the global augmentation argument.  By
`canonicalLadder_freshInessentialGroundStages_subset_phiHindrance`, every such
index names a hindered canonical rung; forgetting freshness loses precisely
that maximal-rung defect.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Fresh-grounded strengthening of the split stationary equal selector.

Every retained path still lies in the original equal subwarp and is
target-pure.  In addition, its source index lies in
`freshInessentialGroundStages`, rather than merely in `phiGround`. -/
theorem exists_splitReserved_fresh_targetPure_stationary_equalSubwarp
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target)
    (hpure : ∀ p ∈ P.paths,
      (L.splitPopularAuxiliaryInput hL.legal).IsTargetPure p)
    (hstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
          ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths
          ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source ∩
        L.freshInessentialGroundStages)) :
    ∃ q,
      ∃ hq : q ∈ ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths,
      (L.splitPopularAuxiliaryIndexed hL).f
          ⟨q.start,
            ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P)
              |>.starts_in_source hq⟩ ∈ L.freshInessentialGroundStages ∧
      ∃ Q : Popular.XSWarp
          (L.splitPopularAuxiliaryInput hL.legal).lambda
          (L.splitPopularAuxiliaryInput hL.legal).lambda.target,
        Q.paths ⊆
            ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths ∧
        (∀ p ∈ Q.paths,
          (L.splitPopularAuxiliaryInput hL.legal).IsTargetPure p) ∧
        (∀ p, ∀ hp : p ∈ Q.paths,
          (L.splitPopularAuxiliaryIndexed hL).f
            ⟨p.start, Q.starts_in_source hp⟩ ∈
              L.freshInessentialGroundStages) ∧
        Stationary.IsStationaryBelow kappa
          (Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
            ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp Q).paths
            ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp Q).starts_in_source) ∧
        Q.paths.PairwiseDisjoint
          (L.splitPopularAuxiliaryInput hL.legal).decodedVertexCarrier ∧
        (∀ p ∈ Q.paths,
          Disjoint p.support
            (GroundingEqualActiveSelection.collisionCarrier
              (L.splitPopularAuxiliaryInput hL.legal) q)) ∧
        (∀ {p r} (hp : p ∈ Q.paths) (hr : r ∈ Q.paths),
          (L.splitPopularAuxiliaryIndexed hL).f
              ⟨r.start, Q.starts_in_source hr⟩ <
            (L.splitPopularAuxiliaryIndexed hL).f
              ⟨p.start, Q.starts_in_source hp⟩ →
          Disjoint p.support
            (GroundingEqualActiveSelection.collisionCarrier
              (L.splitPopularAuxiliaryInput hL.legal) r)) := by
  let I := L.splitPopularAuxiliaryInput hL.legal
  let U := L.splitPopularAuxiliaryIndexed hL
  let R := U.equalSubwarp P
  obtain ⟨a, haInitial, haFresh⟩ := hstat.nonempty
  obtain ⟨q, hqR, hqa⟩ := haInitial
  let freshPaths : Set (FinitePath I.lambda.graph) :=
    {p | ∃ hp : p ∈ R.paths,
      U.f ⟨p.start, R.starts_in_source hp⟩ ∈
        L.freshInessentialGroundStages}
  let F : Popular.XSWarp I.lambda I.lambda.target :=
    Popular.KappaIndexed.subwarp R freshPaths (by
      rintro p ⟨hp, _⟩
      exact hp)
  have hFstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf U F.paths F.starts_in_source) := by
    apply hstat.mono
    rintro b ⟨⟨p, hpR, hpb⟩, hbFresh⟩
    have hpFresh : U.f ⟨p.start, R.starts_in_source hpR⟩ ∈
        L.freshInessentialGroundStages := hpb ▸ hbFresh
    let hpF : p ∈ F.paths := ⟨hpR, hpFresh⟩
    refine ⟨p, hpF, ?_⟩
    have hs :
        (⟨p.start, F.starts_in_source hpF⟩ : I.lambda.source) =
          ⟨p.start, R.starts_in_source hpR⟩ := Subtype.ext rfl
    exact (congrArg U.f hs).trans hpb
  obtain ⟨Q0, hQ0F, hQ0stat, _hQ0disjoint, hQ0avoid⟩ :=
    GroundingEqualActiveSelection.exists_stationary_decodedCarrierDisjoint_subwarp_avoiding
      I (L.splitPopularAuxiliary_proxyPathsFaithful hL)
      U (L.splitPopularAuxiliaryIndexed_sourceIndexed hL)
      F hFstat q
  let Q :=
    GroundingEqualOrderedActiveSelection.orderedActiveSubwarp I U Q0
  have hQQ0 : Q.paths ⊆ Q0.paths :=
    GroundingEqualOrderedActiveSelection.orderedActiveSubwarp_paths_subset
      I U Q0
  have hQstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf U Q.paths Q.starts_in_source) :=
    GroundingEqualOrderedActiveSelection.orderedActiveSubwarp_initialIndices_isStationary
      I (L.splitPopularAuxiliary_proxyPathsFaithful hL)
      U (L.splitPopularAuxiliaryIndexed_sourceIndexed hL) Q0 hQ0stat
  have hQdisjoint : Q.paths.PairwiseDisjoint I.decodedVertexCarrier :=
    GroundingEqualOrderedActiveSelection.orderedActiveSubwarp_decodedCarriers_pairwiseDisjoint
      I (L.splitPopularAuxiliary_proxyPathsFaithful hL)
      U (L.splitPopularAuxiliaryIndexed_sourceIndexed hL) Q0
  have hQF : ∀ {p}, p ∈ Q.paths → p ∈ F.paths :=
    fun {_} hp ↦ hQ0F (hQQ0 hp)
  have hQR : Q.paths ⊆ R.paths := fun {_} hp ↦ (hQF hp).1
  have hQavoid : ∀ p ∈ Q.paths,
      Disjoint p.support
        (GroundingEqualActiveSelection.collisionCarrier I q) :=
    fun p hp ↦ hQ0avoid p (hQQ0 hp)
  refine ⟨q, hqR, ?_, Q, hQR, ?_, ?_, ?_, hQdisjoint, hQavoid, ?_⟩
  · have hindex : U.f ⟨q.start, R.starts_in_source hqR⟩ = a := hqa
    exact hindex ▸ haFresh
  · intro p hpQ
    apply hpure p
    exact U.equalPaths_subset P (hQR hpQ)
  · intro p hpQ
    have hpFresh :
        U.f ⟨p.start, R.starts_in_source (hQF hpQ).1⟩ ∈
          L.freshInessentialGroundStages := (hQF hpQ).2
    have hs :
        (⟨p.start, Q.starts_in_source hpQ⟩ : I.lambda.source) =
          ⟨p.start, R.starts_in_source (hQF hpQ).1⟩ := Subtype.ext rfl
    exact (congrArg U.f hs) ▸ hpFresh
  · exact
      GroundingEqualActiveSelection.equalSubwarp_initialIndices_isStationary_of_subset
        U P Q hQR hQstat
  · intro p r hp hr hrp
    apply
      GroundingEqualOrderedActiveSelection.orderedActiveSubwarp_orderedAvoidance
        I U Q0 hp hr
    simpa only [GroundingEqualActiveSelection.warpPathIndex] using hrp

/-- Bundled equal selection whose reserved route and every active route are
indexed by genuinely fresh grounded stages. -/
structure SplitReservedStationaryFreshEqualSelection
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target) : Type u
    extends L.SplitReservedStationaryEqualSelection hL P where
  reserved_fresh : (L.splitPopularAuxiliaryIndexed hL).f
    ⟨toSplitReservedStationaryEqualSelection.reserved.start,
      toSplitReservedStationaryEqualSelection.reserved_source⟩ ∈
        L.freshInessentialGroundStages
  routes_fresh : ∀ p,
    ∀ hp : p ∈ toSplitReservedStationaryEqualSelection.routes.paths,
      (L.splitPopularAuxiliaryIndexed hL).f
        ⟨p.start,
          toSplitReservedStationaryEqualSelection.routes.starts_in_source hp⟩ ∈
            L.freshInessentialGroundStages

/-- The fresh-grounded selector and the usual grounded-parent decoder give
the bundled fresh equal selection without any additional provider. -/
theorem splitReservedStationaryFreshEqualSelection_nonempty
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target)
    (hpure : ∀ p ∈ P.paths,
      (L.splitPopularAuxiliaryInput hL.legal).IsTargetPure p)
    (hstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
          ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths
          ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source ∩
        L.freshInessentialGroundStages)) :
    Nonempty (L.SplitReservedStationaryFreshEqualSelection hL P) := by
  obtain ⟨q, hq, hqfresh, Q, hQP, hQpure, hQfresh,
      hQstat, hQdisjoint, hQavoid, hQordered⟩ :=
    L.exists_splitReserved_fresh_targetPure_stationary_equalSubwarp
      hL P hpure hstat
  let hs : q.start ∈
      (L.splitPopularAuxiliaryInput hL.legal).lambda.source :=
    ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source hq
  let R : L.SplitReservedGroundedParent hL q hs :=
    (L.splitReservedGroundedParent_nonempty hL q hs hqfresh.1).some
  exact ⟨{
    reserved := q
    reserved_mem := hq
    reserved_source := hs
    reserved_ground := hqfresh.1
    parent := R
    routes := Q
    routes_subset := hQP
    routes_targetPure := hQpure
    routes_ground := fun p hp ↦ (hQfresh p hp).1
    equal_indices_stationary := hQstat
    decodedCarriers_pairwiseDisjoint := hQdisjoint
    routes_avoid_reserved := hQavoid
    routes_orderedAvoidance := hQordered
    reserved_fresh := hqfresh
    routes_fresh := hQfresh }⟩

/-- Geometry-preserving stationary split of the normalized auxiliary output.

Unlike `splitPopularAuxiliary_targetPure_prior_or_fresh_or_separator`, this
keeps the target-pure equal warp and intersects the two grounded classes with
its actual set of equal source indices.  Thus the fresh alternative is an
input to `splitReservedStationaryFreshEqualSelection_nonempty`, rather than a
bare stationary set with no routes attached. -/
theorem splitPopularAuxiliary_targetPure_priorEqual_or_freshEqual_or_separator
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :
    (∃ P : Popular.XSWarp
        (L.splitPopularAuxiliaryInput hL.legal).lambda
        (L.splitPopularAuxiliaryInput hL.legal).lambda.target,
      (∀ p (_hp : p ∈ P.paths),
        (L.splitPopularAuxiliaryInput hL.legal).IsTargetPure p) ∧
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
            ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths
            ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source ∩
          L.priorInessentialGroundStages)) ∨
      (∃ P : Popular.XSWarp
          (L.splitPopularAuxiliaryInput hL.legal).lambda
          (L.splitPopularAuxiliaryInput hL.legal).lambda.target,
        (∀ p (_hp : p ∈ P.paths),
          (L.splitPopularAuxiliaryInput hL.legal).IsTargetPure p) ∧
        Stationary.IsStationaryBelow kappa
          (Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
              ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths
              ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source ∩
            L.freshInessentialGroundStages)) ∨
        Nonempty
          (Popular.PopularSeparator (L.splitPopularAuxiliaryIndexed hL)) := by
  rcases L.splitPopularAuxiliary_targetPure_groundEqual_or_separator hL with
      ⟨P, hPpure, hgroundEqual⟩ | hseparator
  · let E : Set (Ladder.Stage kappa) :=
      Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
        ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source
    have hsplit : E ∩ L.phiGround =
        (E ∩ L.priorInessentialGroundStages) ∪
          (E ∩ L.freshInessentialGroundStages) := by
      rw [L.phiGround_eq_priorInessential_union_freshInessential
        hL.legal.validBookkeeping, Set.inter_union_distrib_left]
    rw [hsplit] at hgroundEqual
    have hcof : Order.cof (Ladder.Stage kappa) ≠ ℵ₀ := by
      rw [Stationary.cof_below_eq_lift hL.legal.regular]
      rw [← Cardinal.lift_aleph0.{u + 1, u}]
      exact (Cardinal.lift_lt.mpr hL.legal.uncountable).ne'
    rcases (isStationary_union_iff hcof).mp hgroundEqual with
        hprior | hfresh
    · exact Or.inl ⟨P, hPpure, hprior⟩
    · exact Or.inr (Or.inl ⟨P, hPpure, hfresh⟩)
  · exact Or.inr (Or.inr hseparator)

/-- The fresh branch of the geometry-preserving split is immediately
upgraded to a collision-thinned, ordered, reserved equal selection. -/
theorem splitPopularAuxiliary_priorEqual_or_freshSelection_or_separator
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :
    (∃ P : Popular.XSWarp
        (L.splitPopularAuxiliaryInput hL.legal).lambda
        (L.splitPopularAuxiliaryInput hL.legal).lambda.target,
      (∀ p (_hp : p ∈ P.paths),
        (L.splitPopularAuxiliaryInput hL.legal).IsTargetPure p) ∧
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
            ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths
            ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source ∩
          L.priorInessentialGroundStages)) ∨
      (∃ P : Popular.XSWarp
          (L.splitPopularAuxiliaryInput hL.legal).lambda
          (L.splitPopularAuxiliaryInput hL.legal).lambda.target,
        Nonempty (L.SplitReservedStationaryFreshEqualSelection hL P)) ∨
        Nonempty
          (Popular.PopularSeparator (L.splitPopularAuxiliaryIndexed hL)) := by
  rcases
      L.splitPopularAuxiliary_targetPure_priorEqual_or_freshEqual_or_separator
        hL with hprior | ⟨P, hPpure, hfresh⟩ | hseparator
  · exact Or.inl hprior
  · exact Or.inr (Or.inl ⟨P,
      L.splitReservedStationaryFreshEqualSelection_nonempty
        hL P hPpure hfresh⟩)
  · exact Or.inr (Or.inr hseparator)

namespace SplitReservedStationaryFreshEqualSelection

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {P : Popular.XSWarp
    (L.splitPopularAuxiliaryInput hL.legal).lambda
    (L.splitPopularAuxiliaryInput hL.legal).lambda.target}

/-- Strict-collision pruning preserves the exact fresh-stage witness. -/
theorem strictRoutes_fresh
    (S : L.SplitReservedStationaryFreshEqualSelection hL P) :
    ∀ p, ∀ hp : p ∈ S.strictRoutes.paths,
      (L.splitPopularAuxiliaryIndexed hL).f
        ⟨p.start, S.strictRoutes.starts_in_source hp⟩ ∈
          L.freshInessentialGroundStages := by
  intro p hp
  have hpRoutes := S.strictRoutes_subset_routes hp
  have hfresh := S.routes_fresh p hpRoutes
  have hs :
      (⟨p.start, S.strictRoutes.starts_in_source hp⟩ :
        (L.splitPopularAuxiliaryInput hL.legal).lambda.source) =
      ⟨p.start, S.routes.starts_in_source hpRoutes⟩ :=
    Subtype.ext rfl
  exact (congrArg (L.splitPopularAuxiliaryIndexed hL).f hs) ▸ hfresh

/-- The stationary strict family remains stationary after recording that
all of its actual source indices are fresh grounded stages. -/
theorem strictRoutes_fresh_initialIndices_isStationary
    (S : L.SplitReservedStationaryFreshEqualSelection hL P) :
    Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
          S.strictRoutes.paths S.strictRoutes.starts_in_source ∩
        L.freshInessentialGroundStages) := by
  apply S.strictRoutes_initialIndices_isStationary.mono
  rintro a ha
  refine ⟨ha, ?_⟩
  obtain ⟨p, hp, hpa⟩ := ha
  exact hpa ▸ S.strictRoutes_fresh p hp

variable {G : DWeb V} {preferred : Ladder.Stage kappa → Option V}
  {hL : (canonicalLadder G kappa preferred).IsSplitKappaHindrance}
  {P : Popular.XSWarp
    ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
      hL.legal).lambda
    ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
      hL.legal).lambda.target}

/-- Every route retained by the canonical fresh selector is indexed by a
genuine hindrance rung. -/
theorem route_index_mem_phiHindrance
    (S : (canonicalLadder G kappa preferred)
      |>.SplitReservedStationaryFreshEqualSelection hL P)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    {p : FinitePath
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
        hL.legal).lambda.graph}
    (hp : p ∈ S.routes.paths) :
    ((canonicalLadder G kappa preferred).splitPopularAuxiliaryIndexed hL).f
        ⟨p.start, S.routes.starts_in_source hp⟩ ∈
      (canonicalLadder G kappa preferred).phiHindrance := by
  apply canonicalLadder_freshInessentialGroundStages_subset_phiHindrance
    preferred hkappa huncountable hNoEnter
  exact S.routes_fresh p hp

/-- Canonically, the strict selected family has stationarily many actual
source indices which are hindered rungs. -/
theorem strictRoutes_phiHindrance_initialIndices_isStationary
    (S : (canonicalLadder G kappa preferred)
      |>.SplitReservedStationaryFreshEqualSelection hL P)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source) :
    Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf
          ((canonicalLadder G kappa preferred)
            |>.splitPopularAuxiliaryIndexed hL)
          S.strictRoutes.paths S.strictRoutes.starts_in_source ∩
        (canonicalLadder G kappa preferred).phiHindrance) := by
  apply S.strictRoutes_initialIndices_isStationary.mono
  rintro a ha
  refine ⟨ha, ?_⟩
  obtain ⟨p, hp, hpa⟩ := ha
  apply canonicalLadder_freshInessentialGroundStages_subset_phiHindrance
    preferred hkappa huncountable hNoEnter
  exact hpa ▸ S.strictRoutes_fresh p hp

/-- Path-indexed form of the maximal-rung defect.  The omitted stage source
is retained together with the selected route that names its stage. -/
theorem route_exists_rungDefect
    (S : (canonicalLadder G kappa preferred)
      |>.SplitReservedStationaryFreshEqualSelection hL P)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    {p : FinitePath
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
        hL.legal).lambda.graph}
    (hp : p ∈ S.routes.paths) :
    let a :=
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryIndexed hL).f
        ⟨p.start, S.routes.starts_in_source hp⟩
    ∃ z : V,
      z ∈ ((canonicalLadder G kappa preferred).stageWeb a).source ∧
      z ∉ ((canonicalLadder G kappa preferred).stageWeb a).initialSet
        ((canonicalLadder G kappa preferred).rung a) := by
  dsimp only
  exact canonicalLadder_freshInessentialGroundStage_exists_rungDefect
    preferred hkappa huncountable hNoEnter (S.routes_fresh p hp)

/-- Strict-route specialization of the maximal-rung defect. -/
theorem strictRoute_exists_rungDefect
    (S : (canonicalLadder G kappa preferred)
      |>.SplitReservedStationaryFreshEqualSelection hL P)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    {p : FinitePath
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
        hL.legal).lambda.graph}
    (hp : p ∈ S.strictRoutes.paths) :
    let a :=
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryIndexed hL).f
        ⟨p.start, S.strictRoutes.starts_in_source hp⟩
    ∃ z : V,
      z ∈ ((canonicalLadder G kappa preferred).stageWeb a).source ∧
      z ∉ ((canonicalLadder G kappa preferred).stageWeb a).initialSet
        ((canonicalLadder G kappa preferred).rung a) := by
  dsimp only
  exact canonicalLadder_freshInessentialGroundStage_exists_rungDefect
    preferred hkappa huncountable hNoEnter (S.strictRoutes_fresh p hp)

end SplitReservedStationaryFreshEqualSelection

end KappaLadder
end DWeb
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.exists_splitReserved_fresh_targetPure_stationary_equalSubwarp
#print axioms Erdos599.DWeb.KappaLadder.splitReservedStationaryFreshEqualSelection_nonempty
#print axioms Erdos599.DWeb.KappaLadder.splitPopularAuxiliary_priorEqual_or_freshSelection_or_separator
#print axioms Erdos599.DWeb.KappaLadder.SplitReservedStationaryFreshEqualSelection.strictRoutes_fresh_initialIndices_isStationary
#print axioms Erdos599.DWeb.KappaLadder.SplitReservedStationaryFreshEqualSelection.strictRoutes_phiHindrance_initialIndices_isStationary
#print axioms Erdos599.DWeb.KappaLadder.SplitReservedStationaryFreshEqualSelection.route_exists_rungDefect
#print axioms Erdos599.DWeb.KappaLadder.SplitReservedStationaryFreshEqualSelection.strictRoute_exists_rungDefect
