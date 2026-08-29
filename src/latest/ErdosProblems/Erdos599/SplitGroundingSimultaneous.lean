/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingAuxiliary
import ErdosProblems.Erdos599.GroundingErasedForwardConflict
import ErdosProblems.Erdos599.GroundingBlockingReachability
import ErdosProblems.Erdos599.GroundingAssertion822Output
import ErdosProblems.Erdos599.GroundingEqualActiveSelection

/-!
# Canonical simultaneous selection for the split grounding auxiliary

The source-faithful selector and the erased switched relation are generic in
the auxiliary input.  This file installs them for the sound split auxiliary.
The only extra geometric fact needed by the generic incidence theorem is that
the split proxies faithfully name distinct members of the limiting ladder.

The controls below have empty exceptional families.  They do not claim the
stronger Assertions 8.19--8.20 collision avoidance: the strengthened selector
independently removes all previously exposed ladder footprints, and the erased
incidence and boundary theorems used here are uniform in the controls.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open GroundingSimultaneousDecode
open GroundingErasedDecode
open GroundingErasedSwitchRelation GroundingErasedForwardConflict
open GroundingRootedReachabilityWarp

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Split proxies are precisely distinct recorded rays in the limiting
ladder. -/
theorem splitPopularAuxiliary_proxyPathsFaithful
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :
    ProxyPathsFaithful (L.splitPopularAuxiliaryInput hL.legal) := by
  constructor
  · intro i
    obtain ⟨a, _ha, hchosen⟩ := i.2
    have hi := L.recorded_mem_inessential
      hL.legal.recordedPathsPersist hchosen
      (b := Ladder.finalStage kappa) (by
        change a.1 + 1 ≤ kappa.ord
        exact (Order.add_one_le_iff).2 a.2)
    change i.1 ∈ L.limitWarp
    exact hi.1
  · intro i j hij
    apply Subtype.ext
    simpa only [splitPopularAuxiliaryInput, splitInfinitePath] using hij

/-- The canonical control package needed by the footprint-recursive
selector.  The exceptional families are empty; all fields are therefore
proved rather than postulated. -/
noncomputable def splitFootprintControls
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (S : Popular.PopularSeparator (L.splitPopularAuxiliaryIndexed hL)) :
    GroundingSelection.Controls S where
  hangingLadder _ := ∅
  hangingFragment _ := ∅
  ladderRank _ a := a
  ladderTrace _ _ := ∅
  ladderRank_regressive := by
    intro r a ha
    rcases ha with ⟨p, hp, _⟩
    exact hp.2.elim
  ladderTrace_countable := by
    intro _ _
    exact Set.countable_empty
  ladderTrace_disjoint_apex := by
    intro _ _
    exact Set.empty_disjoint _
  hangingLadder_meets := by
    intro r p hp
    exact hp.2.elim
  fragmentIndices_nonstationary := by
    intro r hstationary
    have hempty :
        Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
          (PopularSwitching.restrictPaths
            (PopularGroundingBridge.requestFan S r) ∅).paths
          (PopularSwitching.restrictPaths
            (PopularGroundingBridge.requestFan S r) ∅).starts_in_source =
          ∅ := by
      ext a
      simp [Popular.initialIndicesOf, PopularSwitching.restrictPaths]
    rw [hempty] at hstationary
    simpa using hstationary.nonempty

/-- The split erased switch stopped at an arbitrary original-web frontier. -/
abbrev splitSelectedSwitchedEdgesAt
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (S : Popular.PopularSeparator (L.splitPopularAuxiliaryIndexed hL))
    (T : Set V) : Set (V × V) :=
  erasedSelectedSwitchedEdgesAt (L.splitPopularAuxiliaryIndexed hL) S
    (L.splitFootprintControls hL S) T

/-- Every edge of the canonical split switched relation is an original-web
edge. -/
theorem splitSelectedSwitchedEdgesAt_subset_adj
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (S : Popular.PopularSeparator (L.splitPopularAuxiliaryIndexed hL))
    (T : Set V) :
    L.splitSelectedSwitchedEdgesAt hL S T ⊆
      {e | Gamma.graph.Adj e.1 e.2} :=
  erasedSelectedSwitchedEdgesAt_subset_adj
    (L.splitPopularAuxiliaryIndexed hL) S
      (L.splitFootprintControls hL S) T

/-- Footprint avoidance and faithful proxies make the canonical split
switched relation locally bi-unique. -/
theorem splitSelectedSwitchedEdgesAt_biUnique
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (S : Popular.PopularSeparator (L.splitPopularAuxiliaryIndexed hL))
    (T : Set V) :
    Relator.BiUnique
      (fun x y ↦ (x, y) ∈ L.splitSelectedSwitchedEdgesAt hL S T) := by
  exact erasedSelectedSwitchedEdgesAt_biUnique
    (L.splitPopularAuxiliaryIndexed hL) S
      (L.splitFootprintControls hL S) T
      (L.splitPopularAuxiliary_proxyPathsFaithful hL)

/-- Stopping the split switch at the boundary makes it a reachability
antichain. -/
theorem splitSelectedSwitchedEdgesAt_reachabilityAntichain
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (S : Popular.PopularSeparator (L.splitPopularAuxiliaryIndexed hL))
    (T : Set V) :
    IsReachabilityAntichain
      (L.splitSelectedSwitchedEdgesAt hL S T) T := by
  intro b hb c _hc hbc
  exact GroundingBlockingReachability.eq_of_reflTransGen_of_noOutgoing
    (boundary_noOutgoing_switchedAt
      (L.splitPopularAuxiliaryIndexed hL) S
        (L.splitFootprintControls hL S) T hb) hbc


/-- Exact split Assertion 8.22 compiler after choosing a separating stopped
frontier and one original source which is not used as a root.  All incidence
and antichain fields are supplied by the canonical split selector above. -/
theorem splitAssertion822Output_of_frontierGeometry
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (S : Popular.PopularSeparator (L.splitPopularAuxiliaryIndexed hL))
    (unused : V) (hunusedSource : unused ∈ Gamma.source)
    (T : Set V)
    (hTsubset : T ⊆
      GroundingCut.BB (L.splitPopularAuxiliaryInput hL.legal) S.cut)
    (hTseparator : Popular.IsSeparator Gamma T)
    (hroot : ∀ t ∈ T,
      ∃ a ∈ Gamma.source \ {unused},
        Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈ L.splitSelectedSwitchedEdgesAt hL S T) a t) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
      (L.splitPopularAuxiliaryInput hL.legal) S.cut) := by
  apply GroundingAssertion822Output.exists_of_rootedReachability
    (L.splitPopularAuxiliaryInput hL.legal) S.cut
    (L.splitSelectedSwitchedEdgesAt hL S T)
    (Gamma.source \ {unused}) T
    (L.splitSelectedSwitchedEdgesAt_subset_adj hL S T)
    (L.splitSelectedSwitchedEdgesAt_biUnique hL S T)
    Set.sdiff_subset hTsubset hTseparator
    (L.splitSelectedSwitchedEdgesAt_reachabilityAntichain hL S T)
    hroot unused hunusedSource
  simp


/-- The Assertion 8.22 output already contains the full original-web
separation needed for an ordinary hindrance; the finite-descent arguments
are only one way of constructing that output. -/
theorem exists_hindrance_of_splitAssertion822Output
    {I : Type u} {L : PopularAuxiliary.Input Gamma I} {C : Set L.LV}
    (O : GroundingFinalAssembly.Assertion822Output L C) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  have hwave : Gamma.IsWave O.warp :=
    ⟨O.isWarp, O.initial_subset_source, by
      intro x hx p hp
      rw [O.terminalFrontier_eq]
      exact O.frontier_separates p (hp.1 ▸ hx) hp.2⟩
  exact ⟨Gamma.essentialWarpPart O.warp, hwave.essentialWarpPart,
    O.essential_initial_ne_source⟩

/-- A separating source-rooted frontier of the canonical split switched
relation therefore gives an ordinary hindrance immediately. -/
theorem exists_hindrance_of_splitFrontierGeometry
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (S : Popular.PopularSeparator (L.splitPopularAuxiliaryIndexed hL))
    (unused : V) (hunusedSource : unused ∈ Gamma.source)
    (T : Set V)
    (hTsubset : T ⊆
      GroundingCut.BB (L.splitPopularAuxiliaryInput hL.legal) S.cut)
    (hTseparator : Popular.IsSeparator Gamma T)
    (hroot : ∀ t ∈ T,
      ∃ a ∈ Gamma.source \ {unused},
        Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈ L.splitSelectedSwitchedEdgesAt hL S T) a t) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  exact exists_hindrance_of_splitAssertion822Output
    (L.splitAssertion822Output_of_frontierGeometry hL S unused
      hunusedSource T hTsubset hTseparator hroot).some



/-- In the grounded equal branch, reserve one genuinely grounded route before
the carrier-disjoint thinning.  The remaining stationary family is
target-pure, same-index, decoded-carrier disjoint, and avoids the complete
collision carrier of the reserved route. -/
theorem exists_splitReserved_targetPure_stationary_equalSubwarp
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
        Stationary.IsStationaryBelow kappa
          (Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
            ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp Q).paths
            ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp Q).starts_in_source) ∧
        Q.paths.PairwiseDisjoint
          (L.splitPopularAuxiliaryInput hL.legal).decodedVertexCarrier ∧
        (∀ p ∈ Q.paths,
          Disjoint p.support
            (GroundingEqualActiveSelection.collisionCarrier
              (L.splitPopularAuxiliaryInput hL.legal) q)) := by
  let I := L.splitPopularAuxiliaryInput hL.legal
  let U := L.splitPopularAuxiliaryIndexed hL
  let R := U.equalSubwarp P
  obtain ⟨a, haInitial, haGround⟩ := hstat.nonempty
  obtain ⟨q, hqR, hqa⟩ := haInitial
  have hRstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf U R.paths R.starts_in_source) :=
    hstat.mono (fun _ ha ↦ ha.1)
  obtain ⟨Q, hQR, hQstat, hQdisjoint, hQavoid⟩ :=
    GroundingEqualActiveSelection.exists_stationary_decodedCarrierDisjoint_subwarp_avoiding
      I (L.splitPopularAuxiliary_proxyPathsFaithful hL)
      U (L.splitPopularAuxiliaryIndexed_sourceIndexed hL)
      R hRstat q
  refine ⟨q, hqR, ?_, Q, hQR, ?_, ?_, hQdisjoint, hQavoid⟩
  · have hindex :
        U.f ⟨q.start, R.starts_in_source hqR⟩ = a := hqa
    exact hindex ▸ haGround
  · intro p hpQ
    apply hpure p
    exact U.equalPaths_subset P (hQR hpQ)
  · exact
      GroundingEqualActiveSelection.equalSubwarp_initialIndices_isStationary_of_subset
        U P Q hQR hQstat


end KappaLadder
end DWeb
end Erdos599
