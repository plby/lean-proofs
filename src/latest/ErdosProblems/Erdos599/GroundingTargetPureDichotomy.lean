/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingTargetPureChronology
import ErdosProblems.Erdos599.GroundingIndexDichotomy

/-!
# First-target normalization of the grounding popularity dichotomy

A strongly popular target warp need not consist of target-pure paths.
Cutting every member at its first target hit preserves all source indices,
keeps the paths disjoint, and makes the successor-roof chronology applicable.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Popular

open DirectedPath Stationary

universe u

variable {V : Type u}

namespace XSWarp

/-- The first-target prefix of one member of a target warp. -/
def firstTargetPath {Gamma : DWeb V}
    (P : XSWarp Gamma Gamma.target) (p : P.paths) :
    FinitePath Gamma.graph :=
  p.1.firstHit Gamma.target
    ⟨p.1.finish, p.1.finish_mem_support, P.ends_in_target p.2⟩

/-- Normalize a target warp by stopping every member at its first target. -/
def firstTargetWarp {Gamma : DWeb V}
    (P : XSWarp Gamma Gamma.target) : XSWarp Gamma Gamma.target where
  paths := Set.range P.firstTargetPath
  disjoint := by
    rintro q ⟨p, rfl⟩ r ⟨p', rfl⟩ hqr
    have hpp' : p.1 ≠ p'.1 := by
      intro hpp'
      apply hqr
      exact congrArg P.firstTargetPath (Subtype.ext hpp')
    exact (P.disjoint p.2 p'.2 hpp').mono
      (p.1.firstHit_support_subset Gamma.target
        ⟨p.1.finish, p.1.finish_mem_support, P.ends_in_target p.2⟩)
      (p'.1.firstHit_support_subset Gamma.target
        ⟨p'.1.finish, p'.1.finish_mem_support, P.ends_in_target p'.2⟩)
  starts_in_source := by
    rintro q ⟨p, rfl⟩
    change p.1.start ∈ Gamma.source
    exact P.starts_in_source p.2
  ends_in_target := by
    rintro q ⟨p, rfl⟩
    exact p.1.firstHit_finish_mem Gamma.target
      ⟨p.1.finish, p.1.finish_mem_support, P.ends_in_target p.2⟩

/-- First-target normalization preserves every initial ordinal index. -/
theorem initialIndices_subset_firstTargetWarp
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (D : KappaIndexed Gamma kappa) (P : XSWarp Gamma Gamma.target) :
    initialIndicesOf D P.paths P.starts_in_source ⊆
      initialIndicesOf D P.firstTargetWarp.paths
        P.firstTargetWarp.starts_in_source := by
  rintro a ⟨p, hp, hpa⟩
  let ps : P.paths := ⟨p, hp⟩
  let q := P.firstTargetPath ps
  have hq : q ∈ P.firstTargetWarp.paths := ⟨ps, rfl⟩
  refine ⟨q, hq, ?_⟩
  have hsource :
      (⟨q.start, P.firstTargetWarp.starts_in_source hq⟩ : Gamma.source) =
        ⟨p.start, P.starts_in_source hp⟩ := Subtype.ext rfl
  exact (congrArg D.f hsource).trans hpa

end XSWarp

namespace KappaIndexed

/-- A stationary target warp with pointwise weak chronology has a
stationary equality subwarp.  No chronology is assumed outside this warp. -/
theorem stationary_equalSubwarp_of_pathwise_nonincreasing
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (D : KappaIndexed Gamma kappa) (P : XSWarp Gamma Gamma.target)
    (hstat : IsStationaryBelow kappa
      (initialIndicesOf D P.paths P.starts_in_source))
    (hmono : ∀ p (hp : p ∈ P.paths),
      D.g ⟨p.finish, P.ends_in_target hp⟩ ≤
        D.f ⟨p.start, P.starts_in_source hp⟩) :
    IsStationaryBelow kappa
      (initialIndicesOf D (D.equalSubwarp P).paths
        (D.equalSubwarp P).starts_in_source) := by
  let Istrict := initialIndicesOf D (D.strictSubwarp P).paths
    (D.strictSubwarp P).starts_in_source
  let Iequal := initialIndicesOf D (D.equalSubwarp P).paths
    (D.equalSubwarp P).starts_in_source
  have hcover : initialIndicesOf D P.paths P.starts_in_source ⊆
      Istrict ∪ Iequal := by
    rintro a ⟨p, hp, hpa⟩
    rcases (hmono p hp).lt_or_eq with hlt | heq
    · apply Or.inl
      refine ⟨p, ⟨hp, hlt⟩, ?_⟩
      simpa [strictSubwarp, subwarp] using hpa
    · apply Or.inr
      refine ⟨p, ⟨hp, heq⟩, ?_⟩
      simpa [equalSubwarp, subwarp] using hpa
  have hunion : IsStationaryBelow kappa (Istrict ∪ Iequal) :=
    hstat.mono hcover
  have hcof : Order.cof (Below kappa) ≠ ℵ₀ := by
    rw [Stationary.cof_below_eq_lift D.regular]
    rw [← Cardinal.lift_aleph0.{u + 1, u}]
    exact (Cardinal.lift_lt.mpr D.uncountable).ne'
  rcases (isStationary_union_iff hcof).mp hunion with hstrict | hequal
  · exact (D.strictSubwarp_initialIndices_nonstationary P hstrict).elim
  · exact hequal

end KappaIndexed
end Popular

namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath Ladder Stationary

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- The unconditional, successor-corrected grounding dichotomy.  In the
strong-target branch, first-target normalization supplies pointwise weak
chronology, so the only stationary part is the same-index subwarp. -/
theorem popularAuxiliary_equal_or_separator_targetPure
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance) :
    (∃ P : Popular.XSWarp
        (L.popularAuxiliaryInput hL.legal).lambda
        (L.popularAuxiliaryInput hL.legal).lambda.target,
      IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source)) ∨
    Nonempty (Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)) := by
  let U := L.popularAuxiliaryIndexed hL
  have hsource : U.SourceBounded :=
    U.sourceBounded_of_sourceIndexed
      (L.popularAuxiliaryIndexed_sourceIndexed hL)
  rcases Popular.stronglyPopular_target_or_popularSeparator U hsource with
      ⟨P, hP⟩ | hseparator
  · let Q := P.firstTargetWarp
    have hQstat : IsStationaryBelow kappa
        (Popular.initialIndicesOf U Q.paths Q.starts_in_source) :=
      hP.mono (P.initialIndices_subset_firstTargetWarp U)
    have hmono : ∀ p (hp : p ∈ Q.paths),
        U.g ⟨p.finish, Q.ends_in_target hp⟩ ≤
          U.f ⟨p.start, Q.starts_in_source hp⟩ := by
      intro p hp
      rcases hp with ⟨q, rfl⟩
      exact L.targetPure_auxiliaryNonincreasing hL (P.firstTargetPath q)
        (Q.starts_in_source ⟨q, rfl⟩)
        (Q.ends_in_target ⟨q, rfl⟩)
        ((L.popularAuxiliaryInput hL.legal).firstHit_target_isTargetPure
          q.1 ⟨q.1.finish, q.1.finish_mem_support,
            P.ends_in_target q.2⟩)
    exact Or.inl ⟨Q,
      U.stationary_equalSubwarp_of_pathwise_nonincreasing Q hQstat hmono⟩
  · exact Or.inr hseparator

/-- Witness-preserving form of the successor-corrected dichotomy.  The
equal-subwarp witness is not an arbitrary target warp: it is the first-target
normalization constructed above, so every one of its paths is target-pure.
Keeping this fact in the conclusion is essential for the simultaneous
strong-target switch, whose chronology is only valid on target-pure routes. -/
theorem popularAuxiliary_targetPure_equal_or_separator
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance) :
    (∃ P : Popular.XSWarp
        (L.popularAuxiliaryInput hL.legal).lambda
        (L.popularAuxiliaryInput hL.legal).lambda.target,
      (∀ p (_hp : p ∈ P.paths),
        (L.popularAuxiliaryInput hL.legal).IsTargetPure p) ∧
      IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source)) ∨
    Nonempty (Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)) := by
  let U := L.popularAuxiliaryIndexed hL
  have hsource : U.SourceBounded :=
    U.sourceBounded_of_sourceIndexed
      (L.popularAuxiliaryIndexed_sourceIndexed hL)
  rcases Popular.stronglyPopular_target_or_popularSeparator U hsource with
      ⟨P, hP⟩ | hseparator
  · let Q := P.firstTargetWarp
    have hQstat : IsStationaryBelow kappa
        (Popular.initialIndicesOf U Q.paths Q.starts_in_source) :=
      hP.mono (P.initialIndices_subset_firstTargetWarp U)
    have hQpure : ∀ p (hp : p ∈ Q.paths),
        (L.popularAuxiliaryInput hL.legal).IsTargetPure p := by
      intro p hp
      rcases hp with ⟨q, rfl⟩
      exact (L.popularAuxiliaryInput hL.legal).firstHit_target_isTargetPure
        q.1 ⟨q.1.finish, q.1.finish_mem_support,
          P.ends_in_target q.2⟩
    have hmono : ∀ p (hp : p ∈ Q.paths),
        U.g ⟨p.finish, Q.ends_in_target hp⟩ ≤
          U.f ⟨p.start, Q.starts_in_source hp⟩ := by
      intro p hp
      exact L.targetPure_auxiliaryNonincreasing hL p
        (Q.starts_in_source hp) (Q.ends_in_target hp) (hQpure p hp)
    exact Or.inl ⟨Q, hQpure,
      U.stationary_equalSubwarp_of_pathwise_nonincreasing Q hQstat hmono⟩
  · exact Or.inr hseparator

end KappaLadder
end DWeb
end Erdos599
