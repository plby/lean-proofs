/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingDescentBridge
import ErdosProblems.Erdos599.GroundingIndexDichotomy
import ErdosProblems.Erdos599.LadderFreshSameStage

/-!
# Reducing the equal-index grounding branch

The weak chronology of the successor-normalized ladder leaves a genuine
same-index alternative.  This file records the exact set-theoretic reduction
of that alternative.  First, every initial index of an equal subwarp is an
obstruction stage.  Split provenance removes only the nonstationary
strictly-earlier hanging branch.  What remains is either grounded, or the
genuinely fresh same-stage hanging branch.  The grounded alternative then
splits into prior-inessential and successor-new parts.

No claim that the last part is empty is made: that assertion is false from
local ladder data alone and has to be resolved by the global grounding
switch.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder

/-- Every source represented by the grounding auxiliary was selected at a
grounded obstruction stage.  Hence the initial index of every equal-subwarp
path is grounded, not merely an arbitrary obstruction index. -/
theorem equalSubwarp_initialIndices_subset_phiGround
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target) :
    Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source ⊆
      L.phiGround := by
  let I := L.popularAuxiliaryInput hL.legal
  let U := L.popularAuxiliaryIndexed hL
  rintro a ⟨p, hp, hpa⟩
  rcases L.equalSubwarp_path_sameStage hL P hp with
      ⟨x, y, hstart, _hfinish, _hstage⟩ |
      ⟨i, y, hstart, _hfinish, _hstage⟩
  · have hindex :
        U.f ⟨p.start, (U.equalSubwarp P).starts_in_source hp⟩ =
          L.finiteTerminalIndex x := by
      have hs :
          U.f ⟨p.start, (U.equalSubwarp P).starts_in_source hp⟩ =
            U.f ⟨.old x.1, (I.mem_lambda_source_old x.1).2 x.2⟩ := by
        apply congrArg U.f
        exact Subtype.ext hstart
      exact hs
    have ha : a = L.finiteTerminalIndex x := hpa.symm.trans hindex
    rw [ha]
    exact L.finiteTerminalStage_mem_phiGround hL.legal x
  · have hindex :
        U.f ⟨p.start, (U.equalSubwarp P).starts_in_source hp⟩ =
          L.groundedInfiniteStage i := by
      have hs :
          U.f ⟨p.start, (U.equalSubwarp P).starts_in_source hp⟩ =
            U.f ⟨.proxy i, I.mem_lambda_source_proxy i⟩ := by
        apply congrArg U.f
        exact Subtype.ext hstart
      exact hs
    have ha : a = L.groundedInfiniteStage i := hpa.symm.trans hindex
    rw [ha]
    exact (L.groundedInfiniteStage_spec i).1.1

/-- The initial indices used by an equal-index subwarp are genuine
obstruction stages of the ladder. -/
theorem equalSubwarp_initialIndices_subset_phi
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target) :
    Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source ⊆
      L.phi := by
  intro a ha
  obtain ⟨p, hchosen, _hpSource⟩ :=
    L.equalSubwarp_initialIndices_subset_phiGround hL P ha
  exact (L.bookkeeping.mem_phi_iff_exists_chosen
    hL.legal.validBookkeeping).2 ⟨p, hchosen⟩

/-- Intersecting a stationary equal-subwarp index set with grounded stages
does not remove any member: groundedness is built into both kinds of source
of the literal Section 8 auxiliary. -/
theorem equalSubwarp_grounded_initialIndices_isStationary
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (hstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source)) :
    Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source ∩
        L.phiGround) := by
  apply hstat.mono
  intro a ha
  exact ⟨ha, L.equalSubwarp_initialIndices_subset_phiGround hL P ha⟩

/-- A stationary equal-index subwarp retains either stationary many grounded
indices or stationary many genuinely fresh same-stage hanging indices.

This is the sound replacement for removing all of `phiHanging`: only the
strictly-earlier provenance branch is nonstationary. -/
theorem equalSubwarp_grounded_or_freshSameStage_isStationary
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (hSplit : L.SplitLegalityInvariant)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (hstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source)) :
    Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
            ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
            ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source ∩
          L.phiGround) ∨
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
            ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
            ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source ∩
          L.freshSameStageHangingStages) := by
  let E : Set (Ladder.Stage kappa) :=
    Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
      ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
      ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source
  have hEphi : E ⊆ L.phi := L.equalSubwarp_initialIndices_subset_phi hL P
  exact L.stationary_ground_or_freshSameStageHanging
    hSplit E hstat hEphi

/-- Exact stationary old/new split of the equal-index alternative.  The
second branch is the irreducible successor-new case that must be handled by
the global grounding construction. -/
theorem equalSubwarp_prior_or_fresh_or_sameStage_isStationary
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (hSplit : L.SplitLegalityInvariant)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (hstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source)) :
    Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
            ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
            ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source ∩
          L.priorInessentialGroundStages) ∨
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
            ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
            ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source ∩
          L.freshInessentialGroundStages) ∨
        Stationary.IsStationaryBelow kappa
          (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
              ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
              ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source ∩
            L.freshSameStageHangingStages) := by
  let E : Set (Ladder.Stage kappa) :=
    Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
      ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
      ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source
  rcases L.equalSubwarp_grounded_or_freshSameStage_isStationary
      hL hSplit P hstat with hground | hsame
  · have hsplit : E ∩ L.phiGround =
        (E ∩ L.priorInessentialGroundStages) ∪
          (E ∩ L.freshInessentialGroundStages) := by
      rw [L.phiGround_eq_priorInessential_union_freshInessential
        hL.legal.validBookkeeping, Set.inter_union_distrib_left]
    rw [hsplit] at hground
    have hcof : Order.cof (Ladder.Stage kappa) ≠ ℵ₀ := by
      rw [Stationary.cof_below_eq_lift hSplit.regular]
      rw [← Cardinal.lift_aleph0.{u + 1, u}]
      exact (Cardinal.lift_lt.mpr hSplit.uncountable).ne'
    rcases (isStationary_union_iff hcof).mp hground with hprior | hfresh
    · exact Or.inl hprior
    · exact Or.inr (Or.inl hfresh)
  · exact Or.inr (Or.inr hsame)

/-- The weakly chronological auxiliary web has four possible outputs: a
stationary old-record branch, a stationary genuinely successor-new grounded
branch, a stationary fresh same-stage hanging branch, or the popular
separator required by the grounding construction.  The apparently
additional strict-index branch is nonstationary by pressing down and
therefore does not occur here. -/
theorem popularAuxiliary_prior_or_fresh_or_separator
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (hSplit : L.SplitLegalityInvariant)
    (hmono : L.AuxiliaryNonincreasing hL) :
    (∃ P : Popular.XSWarp
        (L.popularAuxiliaryInput hL.legal).lambda
        (L.popularAuxiliaryInput hL.legal).lambda.target,
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
            ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
            ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source ∩
          L.priorInessentialGroundStages)) ∨
      (∃ P : Popular.XSWarp
          (L.popularAuxiliaryInput hL.legal).lambda
          (L.popularAuxiliaryInput hL.legal).lambda.target,
        Stationary.IsStationaryBelow kappa
          (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
              ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
            ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source ∩
            L.freshInessentialGroundStages)) ∨
        (exists P : Popular.XSWarp
            (L.popularAuxiliaryInput hL.legal).lambda
            (L.popularAuxiliaryInput hL.legal).lambda.target,
          Stationary.IsStationaryBelow kappa
            (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
                ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
                ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source ∩
              L.freshSameStageHangingStages)) ∨
          Nonempty (Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)) := by
  let U := L.popularAuxiliaryIndexed hL
  have hsource : U.SourceBounded :=
    U.sourceBounded_of_sourceIndexed
      (L.popularAuxiliaryIndexed_sourceIndexed hL)
  rcases Popular.stronglyPopular_target_or_popularSeparator U hsource with
      hstrong | hseparator
  · obtain ⟨P, hP⟩ := U.stronglyPopular_target_equal hmono hstrong
    rcases L.equalSubwarp_prior_or_fresh_or_sameStage_isStationary
        hL hSplit P hP with hprior | hfresh | hsame
    · exact Or.inl ⟨P, hprior⟩
    · exact Or.inr (Or.inl ⟨P, hfresh⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨P, hsame⟩))
  · exact Or.inr (Or.inr (Or.inr hseparator))

end KappaLadder
end DWeb
end Erdos599
