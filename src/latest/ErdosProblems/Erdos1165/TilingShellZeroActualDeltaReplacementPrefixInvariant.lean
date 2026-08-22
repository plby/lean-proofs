/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroSourcePrefixInvariant
import ErdosProblems.Erdos1165.TilingShellZeroActualDeltaPartition

/-!
# Prefix invariance of an honest actual-delta replacement atom

Every field of a fixed-increment replacement atom is read at its common
rank-`k + delta` creation prefix.  This file packages the corresponding
transport theorem.  In particular, the enlarged `Dtilde_eta` condition, the
oriented external-window screen, both exact coordinate counts, the retained
external code, and the static support all move together.
-/

namespace Erdos1165.TilingShellZeroActualDeltaReplacementPrefixInvariant

open Set
open HLOZPathEvents HLOZTypedStoppedCandidateObservability
open HLOZThetaSourceBalance HLOZShellZeroReplacementWindows
open LazyDecomposition TilingDistinguishedTraceInvariant
open TilingLazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedShellZeroSourcePartition
open TilingShellZeroActualDeltaPartition
open TilingShellZeroSourcePartition TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The enlarged replacement classification is determined by the physical
path prefix at the time where it is evaluated. -/
theorem tilingDtildeEtaAt_iff_of_pathPrefix_eq
    (t : DominoTiling) (m k w low : ℕ)
    {s s' : WalkPath} {n : ℕ}
    (hp : pathPrefix s n = pathPrefix s' n) :
    tilingDtildeEtaAt t m k w low s n ↔
      tilingDtildeEtaAt t m k w low s' n := by
  classical
  have hend : s n = s' n := congrFun hp ⟨n, Nat.lt_succ_self n⟩
  have hVOneBases := tilingVOneBases_eq_of_pathPrefix_eq t m hp
  have hsource := fun b ↦ tilingVTwoAt_iff_of_pathPrefix_eq t
    (shellZeroSourceTotalWindow m w) hp b
  have hreplacement := fun b ↦ tilingVTwoAt_iff_of_pathPrefix_eq t
    (shellZeroReplacementTotalWindow m w) hp b
  have hVOne := fun b ↦ tilingVOneAt_iff_of_pathPrefix_eq t m hp b
  have hVThree := fun b ↦ tilingVThreeAt_iff_of_pathPrefix_eq t m low hp b
  have hlocal := fun b ↦ localTime_eq_of_pathPrefix_eq hp b
  constructor
  · rintro ⟨hcard, hclass, hterminal, hterminalVOne⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [hVOneBases] using hcard
    · intro b hb
      rcases hclass b hb with hb1 | hb2 | hb0 | hb3
      · exact Or.inl ((hVOne b).mp hb1)
      · exact Or.inr (Or.inl ((hsource b).mp hb2))
      · exact Or.inr (Or.inr (Or.inl ((hreplacement b).mp hb0)))
      · exact Or.inr (Or.inr (Or.inr ((hVThree b).mp hb3)))
    · rw [← hend, ← hlocal (s n)]
      exact hterminal
    · rw [← hend]
      exact (hVOne (tilingBase t (s n))).mp hterminalVOne
  · rintro ⟨hcard, hclass, hterminal, hterminalVOne⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [hVOneBases] using hcard
    · intro b hb
      rcases hclass b hb with hb1 | hb2 | hb0 | hb3
      · exact Or.inl ((hVOne b).mpr hb1)
      · exact Or.inr (Or.inl ((hsource b).mpr hb2))
      · exact Or.inr (Or.inr (Or.inl ((hreplacement b).mpr hb0)))
      · exact Or.inr (Or.inr (Or.inr ((hVThree b).mpr hb3)))
    · rw [hend, hlocal (s' n)]
      exact hterminal
    · have hterminalVOne' :
          tilingVOneAt t m s' n (tilingBase t (s n)) := by
        rw [hend]
        exact hterminalVOne
      exact (hVOne (tilingBase t (s n))).mpr hterminalVOne'

/-- Membership in one honest fixed-increment replacement atom is determined
by its physical path prefix at the actual replacement creation time. -/
theorem actualDeltaReplacementStaticSupportAtom_of_pathPrefix_eq
    {t : DominoTiling} {o : Orientation}
    {m k w low externalLow externalHigh total central : ℕ}
    (delta : ReplacementEndpointIncrement total central)
    {z : OrientedTilingTypedExternalWordCode t} {S : Finset Point}
    {s s' : WalkPath}
    (hs : s ∈ orientedValidShellZeroActualDeltaReplacementStaticSupportAtom
      t o m k w low externalLow externalHigh total central delta z S)
    (hvalid' : s' ∈ validStepWalk)
    (hp : pathPrefix s (creationTimeNat m (k + (delta : ℕ)) s) =
      pathPrefix s' (creationTimeNat m (k + (delta : ℕ)) s)) :
    s' ∈ orientedValidShellZeroActualDeltaReplacementStaticSupportAtom
      t o m k w low externalLow externalHigh total central delta z S := by
  classical
  let n := creationTimeNat m (k + (delta : ℕ)) s
  rcases hs with ⟨⟨⟨hevent, hcode⟩, _hvalid⟩, hsupport⟩
  change fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m (k + (delta : ℕ)) s) s = z at hcode
  change actualDeltaReplacementStaticSupport t o m k w total central delta s = S
    at hsupport
  rcases hevent with ⟨hreach, hDtilde, htheta, hsourceCard,
    hreplacementCard⟩
  have hreach' : ReachesThreshold s m (k + (delta : ℕ)) := by
    simpa only [actualReplacementCreationRank] using hreach
  have hcreation : ThresholdCreation s m (k + (delta : ℕ)) n := by
    simpa only [n, creationTimeNat, hreach', dif_pos] using
      thresholdCreation_natFind hreach'
  have hcreation' : ThresholdCreation s' m (k + (delta : ℕ)) n :=
    (thresholdCreation_iff_of_pathPrefix_eq hp le_rfl).mp hcreation
  have htime' : creationTimeNat m (k + (delta : ℕ)) s' = n :=
    creationTimeNat_eq_of_creation hcreation'
  have hDtilde' : tilingDtildeEtaAt t m k w low s' n :=
    (tilingDtildeEtaAt_iff_of_pathPrefix_eq t m k w low hp).mp hDtilde
  have hthetaEq : orientedTilingThetaBases t o m w externalLow externalHigh
      s n = orientedTilingThetaBases t o m w externalLow externalHigh s' n := by
    rw [← prefixOrientedTilingThetaBases_pathPrefix
      t o m w externalLow externalHigh n s,
      ← prefixOrientedTilingThetaBases_pathPrefix
        t o m w externalLow externalHigh n s', hp]
  have hsourceEq : orientedTilingVTwoBases t o
      (shellZeroSourceTotalWindow m w) s n =
      orientedTilingVTwoBases t o
        (shellZeroSourceTotalWindow m w) s' n := by
    rw [← prefixOrientedTilingVTwoBases_pathPrefix t o
      (shellZeroSourceTotalWindow m w) n s,
      ← prefixOrientedTilingVTwoBases_pathPrefix t o
        (shellZeroSourceTotalWindow m w) n s', hp]
  have hreplacementEq : orientedTilingVTwoBases t o
      (shellZeroReplacementTotalWindow m w) s n =
      orientedTilingVTwoBases t o
        (shellZeroReplacementTotalWindow m w) s' n := by
    rw [← prefixOrientedTilingVTwoBases_pathPrefix t o
      (shellZeroReplacementTotalWindow m w) n s,
      ← prefixOrientedTilingVTwoBases_pathPrefix t o
        (shellZeroReplacementTotalWindow m w) n s', hp]
  have hcode' : fixedOrientedTypedExternalWordCode t o n s' = z :=
    (fixedOrientedTypedExternalWordCode_eq_of_pathPrefix_eq t o hp).symm.trans
      hcode
  have hsupport' : actualDeltaReplacementStaticSupport
      t o m k w total central delta s' = S := by
    change orientedTilingVTwoBases t o (shellZeroSourceTotalWindow m w)
        s' (creationTimeNat m (k + (delta : ℕ)) s') ∪
      orientedTilingVTwoBases t o (shellZeroReplacementTotalWindow m w)
        s' (creationTimeNat m (k + (delta : ℕ)) s') = S
    rw [htime', ← hsourceEq, ← hreplacementEq]
    change orientedTilingVTwoBases t o (shellZeroSourceTotalWindow m w)
        s (creationTimeNat m (k + (delta : ℕ)) s) ∪
      orientedTilingVTwoBases t o (shellZeroReplacementTotalWindow m w)
        s (creationTimeNat m (k + (delta : ℕ)) s) = S at hsupport
    exact hsupport
  refine ⟨⟨⟨?_, ?_⟩, hvalid'⟩, hsupport'⟩
  · refine ⟨⟨n, hcreation'.1⟩, ?_⟩
    change let n' := creationTimeNat m (k + (delta : ℕ)) s'
      tilingDtildeEtaAt t m k w low s' n' ∧
        orientedTilingThetaBases t o m w externalLow externalHigh s' n' = ∅ ∧
        (orientedTilingVTwoBases t o
          (shellZeroSourceTotalWindow m w) s' n').card = central ∧
        (orientedTilingVTwoBases t o
          (shellZeroReplacementTotalWindow m w) s' n').card = total - central
    rw [htime']
    exact ⟨hDtilde', hthetaEq ▸ htheta,
      by rw [← hsourceEq]; exact hsourceCard,
      by rw [← hreplacementEq]; exact hreplacementCard⟩
  · change fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m (k + (delta : ℕ)) s') s' = z
    rw [htime']
    exact hcode'

end

end Erdos1165.TilingShellZeroActualDeltaReplacementPrefixInvariant
