/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingSimultaneous
import ErdosProblems.Erdos599.GroundingEqualOrderedActiveCore

/-!
# Source-faithful stationary selection in the split equal branch

Before collision thinning, restrict the equal family to precisely those
routes whose auxiliary source index belongs to the grounded stationary set.
Thus every retained route, rather than only one reserved route, has a genuine
original-web source parent.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Grounded-source strengthening of the split stationary equal selector. -/
theorem exists_splitReserved_grounded_targetPure_stationary_equalSubwarp
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
        L.phiGround)) :
    ∃ q,
      ∃ hq : q ∈ ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths,
      (L.splitPopularAuxiliaryIndexed hL).f
          ⟨q.start,
            ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P)
              |>.starts_in_source hq⟩ ∈ L.phiGround ∧
      ∃ Q : Popular.XSWarp
          (L.splitPopularAuxiliaryInput hL.legal).lambda
          (L.splitPopularAuxiliaryInput hL.legal).lambda.target,
        Q.paths ⊆
            ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths ∧
        (∀ p ∈ Q.paths,
          (L.splitPopularAuxiliaryInput hL.legal).IsTargetPure p) ∧
        (∀ p, ∀ hp : p ∈ Q.paths,
          (L.splitPopularAuxiliaryIndexed hL).f
            ⟨p.start, Q.starts_in_source hp⟩ ∈ L.phiGround) ∧
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
  obtain ⟨a, haInitial, haGround⟩ := hstat.nonempty
  obtain ⟨q, hqR, hqa⟩ := haInitial
  let groundPaths : Set (FinitePath I.lambda.graph) :=
    {p | ∃ hp : p ∈ R.paths,
      U.f ⟨p.start, R.starts_in_source hp⟩ ∈ L.phiGround}
  let G : Popular.XSWarp I.lambda I.lambda.target :=
    Popular.KappaIndexed.subwarp R groundPaths (by
      rintro p ⟨hp, _⟩
      exact hp)
  have hGstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf U G.paths G.starts_in_source) := by
    apply hstat.mono
    rintro b ⟨⟨p, hpR, hpb⟩, hbGround⟩
    have hpGround : U.f ⟨p.start, R.starts_in_source hpR⟩ ∈
        L.phiGround := hpb ▸ hbGround
    let hpG : p ∈ G.paths := ⟨hpR, hpGround⟩
    refine ⟨p, hpG, ?_⟩
    have hs :
        (⟨p.start, G.starts_in_source hpG⟩ : I.lambda.source) =
          ⟨p.start, R.starts_in_source hpR⟩ := Subtype.ext rfl
    exact (congrArg U.f hs).trans hpb
  obtain ⟨Q0, hQ0G, hQ0stat, _hQ0disjoint, hQ0avoid⟩ :=
    GroundingEqualActiveSelection.exists_stationary_decodedCarrierDisjoint_subwarp_avoiding
      I (L.splitPopularAuxiliary_proxyPathsFaithful hL)
      U (L.splitPopularAuxiliaryIndexed_sourceIndexed hL)
      G hGstat q
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
  have hQG : ∀ {p}, p ∈ Q.paths → p ∈ G.paths :=
    fun {_} hp ↦ hQ0G (hQQ0 hp)
  have hQR : Q.paths ⊆ R.paths := fun {_} hp ↦ (hQG hp).1
  have hQavoid : ∀ p ∈ Q.paths,
      Disjoint p.support
        (GroundingEqualActiveSelection.collisionCarrier I q) :=
    fun p hp ↦ hQ0avoid p (hQQ0 hp)
  refine ⟨q, hqR, ?_, Q, hQR, ?_, ?_, ?_, hQdisjoint, hQavoid, ?_⟩
  · have hindex :
        U.f ⟨q.start, R.starts_in_source hqR⟩ = a := hqa
    exact hindex ▸ haGround
  · intro p hpQ
    apply hpure p
    exact U.equalPaths_subset P (hQR hpQ)
  · intro p hpQ
    have hpGround :
        U.f ⟨p.start, R.starts_in_source (hQG hpQ).1⟩ ∈ L.phiGround :=
      (hQG hpQ).2
    have hs :
        (⟨p.start, Q.starts_in_source hpQ⟩ : I.lambda.source) =
          ⟨p.start, R.starts_in_source (hQG hpQ).1⟩ := Subtype.ext rfl
    exact (congrArg U.f hs) ▸ hpGround
  · exact
      GroundingEqualActiveSelection.equalSubwarp_initialIndices_isStationary_of_subset
        U P Q hQR hQstat
  · intro p r hp hr hrp
    apply
      GroundingEqualOrderedActiveSelection.orderedActiveSubwarp_orderedAvoidance
        I U Q0 hp hr
    simpa only [GroundingEqualActiveSelection.warpPathIndex] using hrp

end KappaLadder
end DWeb
end Erdos599

