/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZTypedStoppedCandidateObservability
import ErdosProblems.Erdos1165.TilingShellZeroDeltaScreenMassBound

/-!
# Prefix invariance of the exact oriented static-support source atom

Every condition in the exact source atom is read at its rank-`k` creation
prefix.  This module packages the resulting transport theorem, including the
endpoint-oriented external local-time Theta predicate and the physical
external word/static support fields.
-/

namespace Erdos1165.TilingShellZeroSourcePrefixInvariant

open Set
open HLOZPathEvents HLOZTypedStoppedCandidateObservability
open HLOZThetaSourceBalance
open HLOZShellZeroReplacementWindows LazyDecomposition
open TilingDistinguishedTraceInvariant
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedShellZeroSourcePartition
open TilingShellZeroExternalStaticSupportPartition
open TilingShellZeroSourcePartition VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Exact source membership is determined by the physical path prefix at
the source creation time. -/
theorem exactSourceStaticSupportAtom_of_pathPrefix_eq
    {t : DominoTiling} {o : Orientation}
    {m k w low externalLow externalHigh total : ℕ}
    {z : OrientedTilingTypedExternalWordCode t} {S : Finset Point}
    {s s' : WalkPath}
    (hs : s ∈ orientedValidShellZeroExactSourceStaticSupportAtom
      t o m k w low externalLow externalHigh total z S)
    (hvalid' : s' ∈ validStepWalk)
    (hp : pathPrefix s (creationTimeNat m k s) =
      pathPrefix s' (creationTimeNat m k s)) :
    s' ∈ orientedValidShellZeroExactSourceStaticSupportAtom
      t o m k w low externalLow externalHigh total z S := by
  classical
  let n := creationTimeNat m k s
  rcases hs with ⟨⟨⟨hevent, hcode⟩, _hvalid⟩, hsupport⟩
  change fixedOrientedTypedExternalWordCode t o (creationTimeNat m k s) s = z
    at hcode
  change sourceStaticSupport t o m k w s = S at hsupport
  rcases hevent with ⟨hreach, hD, htheta, hcard⟩
  have hcreation : ThresholdCreation s m k n := by
    simpa only [n, creationTimeNat, hreach, dif_pos] using
      thresholdCreation_natFind hreach
  have hcreation' : ThresholdCreation s' m k n :=
    (thresholdCreation_iff_of_pathPrefix_eq hp le_rfl).mp hcreation
  have htime' : creationTimeNat m k s' = n :=
    creationTimeNat_eq_of_creation hcreation'
  have hD' : tilingDEtaAt t m k w low s' n :=
    (tilingDEtaAt_iff_of_pathPrefix_eq t m k w low hp).mp hD
  have hthetaEq : orientedTilingThetaBases t o m w externalLow externalHigh
      s n = orientedTilingThetaBases t o m w externalLow externalHigh s' n := by
    rw [← prefixOrientedTilingThetaBases_pathPrefix
      t o m w externalLow externalHigh n s,
      ← prefixOrientedTilingThetaBases_pathPrefix
        t o m w externalLow externalHigh n s', hp]
  have hVTwoEq : orientedTilingVTwoBases t o
      (shellZeroSourceTotalWindow m w) s n =
      orientedTilingVTwoBases t o
        (shellZeroSourceTotalWindow m w) s' n := by
    rw [← prefixOrientedTilingVTwoBases_pathPrefix t o
      (shellZeroSourceTotalWindow m w) n s,
      ← prefixOrientedTilingVTwoBases_pathPrefix t o
        (shellZeroSourceTotalWindow m w) n s', hp]
  have hcode' : fixedOrientedTypedExternalWordCode t o n s' = z := by
    exact (fixedOrientedTypedExternalWordCode_eq_of_pathPrefix_eq
      t o hp).symm.trans hcode
  have hsupport' : sourceStaticSupport t o m k w s' = S := by
    change orientedTilingVTwoBases t o (shellZeroSourceTotalWindow m w)
      s' (creationTimeNat m k s') = S
    rw [htime', ← hVTwoEq]
    change orientedTilingVTwoBases t o (shellZeroSourceTotalWindow m w)
      s (creationTimeNat m k s) = S at hsupport
    exact hsupport
  refine ⟨⟨⟨?_, ?_⟩, hvalid'⟩, hsupport'⟩
  · refine ⟨⟨n, hcreation'.1⟩, ?_⟩
    change let n' := creationTimeNat m k s'
      tilingDEtaAt t m k w low s' n' ∧
        orientedTilingThetaBases t o m w externalLow externalHigh s' n' = ∅ ∧
        (orientedTilingVTwoBases t o
          (shellZeroSourceTotalWindow m w) s' n').card = total
    rw [htime']
    exact ⟨hD', hthetaEq ▸ htheta, by rw [← hVTwoEq]; exact hcard⟩
  · change fixedOrientedTypedExternalWordCode t o (creationTimeNat m k s') s' = z
    rw [htime']
    exact hcode'

end

end Erdos1165.TilingShellZeroSourcePrefixInvariant
