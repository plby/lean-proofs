/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZCheckerOriginSafeProp49Family
import ErdosProblems.Erdos1165.HLOZPrefixedCanonicalSourceProp49PathCoverage

/-!
# Physical coverage of the exposed-origin checker screen

On a checker row the deleted physical origin must remain below level `m`.
When its represented domino is one of the source coordinates, the
origin-safe Proposition 4.9 screen imposes exactly this additional
one-coordinate inequality.  This file proves the converse pathwise
coverage: a literal safe path in an exact source atom belongs to that
screen.
-/

open Set

namespace Erdos1165.HLOZCheckerOriginSafeProp49PathCoverage

open HLOZCheckerOriginSafeProp49Family HLOZPathEvents
open HLOZTypedStoppedCandidateObservability
open HLOZPrefixedAllCreationCanonicalDominantWindows
open HLOZPrefixedCanonicalSourceAtomRecovery
open HLOZPrefixedCanonicalSourceLowRecovery
open HLOZPrefixedCanonicalSourceProp49Data
open HLOZPrefixedCanonicalSourceProp49Data.SourceThetaGoodRepresentative
open HLOZPrefixedCanonicalSourceProp49PathCoverage
open HLOZPrefixedCanonicalSourceProp49Refinement
open HLOZPrefixedProp49CandidateWindowRatio HLOZProposition48Candidates
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZTilingConditionalCandidateWindows HLOZThetaSourceBalance
open LazyDecomposition PreStoppingFiber PreStoppingSpatialLaw
open SpatialInsertionFiber StoppedInsertion TilingCappedMarginalization
open TilingDistinguishedTraceInvariant TilingInsertedLocalTime
open TilingLazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedFavoriteTraceSupport
open TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- A path already covered by the ordinary source screen is covered by the
origin-safe screen when the exposed origin is a source coordinate and the
physical origin inequality holds on that same path. -/
theorem mem_sourceOriginSafeCandidateNear_of_exactAtom
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) (a : GapScale)
    (candidate : Point) (hcandidate : candidate ∈ eta.1.2) (low : ℕ)
    (e : Direction) (horigin : targetOriginBase t e ∈ eta.1.2)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    {s : WalkPath}
    (hs : s ∈ orientedAllCreationSupportTraceAtom t o m k
      (SourceSupportAt t o m) eta.1.1 eta.1.2)
    (htheta : orientedTilingThetaBases t o m (shellWidth48 m)
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m) s
      (creationTimeNat m k s) = ∅)
    (hnarrow : localTime s (creationTimeNat m k s) candidate ∈
      prop49NarrowTotalWindow m a)
    (hsafe : s ∈ targetOriginSafe m k e) :
    s ∈ sourceOriginSafeCandidateNear eta a low e candidate := by
  classical
  have hordinary : s ∈ sourceProp49CandidateNear eta a low candidate :=
    mem_sourceProp49CandidateNear_of_exactAtom eta a candidate hcandidate low
      hm hk hwindow harithmetic hexternalArithmetic hs htheta hnarrow
  simp only [sourceProp49CandidateNear, hcandidate, dite_true] at hordinary
  rcases Set.mem_iUnion.mp hordinary with ⟨cap, hcap⟩
  rcases hcap with ⟨hvalid, hevent⟩
  rcases Set.mem_iUnion.mp hevent with ⟨q, hqword⟩
  rcases q.2.1 with ⟨hatom, ell, hell, htotal⟩
  let v := prefixedTilingInsertionPrefixList
    ((SourceFiber eta).initial cap) t ((SourceFiber eta).start cap)
    ((SourceFiber eta).retained cap) (fun j ↦ (q.1 j : ℕ))
    ((SourceFiber eta).tail cap)
  let sq := trajectory (extendPrefix (directionVectorOfList v))
  have hp' := pathPrefix_eq_canonical_of_mem_prefixedTilingStoppedInsertionAtom
    ((SourceFiber eta).initial cap) ((SourceFiber eta).start cap)
    ((SourceFiber eta).retained cap) (fun j ↦ (q.1 j : ℕ))
    ((SourceFiber eta).tail cap) (stepsOfWalk s) hqword
  have hp : pathPrefix s v.length = pathPrefix sq v.length := by
    change trajectory (stepsOfWalk s) = s at hvalid
    rw [hvalid] at hp'
    simpa only [v, sq] using hp'
  have hlt : v.length < orientedAllCreationCoordinateCutoff eta.1.1
      ((SourceFiber eta).coordinateCap cap) := by
    simpa only [v,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.initial,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.start,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.retained,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.tail] using
      (prefixedInsertion_lt_orientedAllCreationCoordinateCutoff eta.1.1
        ((SourceFiber eta).coordinateCap cap) q.1)
  have hcreationQ : ThresholdCreation sq m k v.length := by
    have hstop := q.2.2
    change truncatedLevelTime m k
        (orientedAllCreationCoordinateCutoff eta.1.1
          ((SourceFiber eta).coordinateCap cap))
        (extendPrefix (directionVectorOfList v)) = v.length at hstop
    exact (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k (orientedAllCreationCoordinateCutoff eta.1.1
        ((SourceFiber eta).coordinateCap cap)) v.length _ hlt).mp hstop
  have hcreationS : ThresholdCreation s m k v.length :=
    (thresholdCreation_iff_of_pathPrefix_eq hp le_rfl).mpr hcreationQ
  have htime : creationTimeNat m k s = v.length :=
    creationTimeNat_eq_of_creation hcreationS
  have hpath : finitePathList (pathPrefix sq v.length) =
      prefixedTilingPrefixPointPath ((SourceFiber eta).initial cap)
        ((SourceFiber eta).start cap)
        (tilingInsertGapVector t ((SourceFiber eta).start cap)
          ((SourceFiber eta).retained cap) (fun j ↦ (q.1 j : ℕ)))
        (sourceTerminal eta) := by
    rw [← sourceTerminal_eq_coordinates eta q.1]
    exact finitePathList_prefixedTilingInsertionPrefix
      eta.1.1.external.initial t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (q.1 j : ℕ))
      eta.1.1.external.tail rfl
  let origin := sourceOriginChosen cap eta e horigin
  have hlocalQ : localTime sq v.length (0 - directionVector e) =
      sourceOriginFixedLocalTime eta e +
        tilingDominoTotal t ((SourceFiber eta).start cap)
          ((SourceFiber eta).retained cap) (fun j ↦ (q.1 j : ℕ))
          origin.1 := by
    rw [localTime_eq_listLocalTime, hpath,
      prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        ((SourceFiber eta).initial cap) t ((SourceFiber eta).start cap)
        ((SourceFiber eta).retained cap) (fun j ↦ (q.1 j : ℕ))
        (sourceTerminal eta) origin.1 (0 - directionVector e)]
    · rfl
    · exact sourceOriginChosen_base eta e horigin |>.symm
  have htotalOrigin : tilingDominoTotal t ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) (fun j ↦ (q.1 j : ℕ)) origin.1 =
      ell origin := by
    rw [← tilingAwayTotal_split_eq_dominoTotal t
      ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
      ((SourceFiber eta).distinguished cap) q.1 origin]
    exact htotal origin
  have hsafeCoordinates : sourceOriginFixedLocalTime eta e +
      (ell origin : ℕ) + 1 < m := by
    change localTime s (creationTimeNat m k s)
        (0 - directionVector e) + 1 < m at hsafe
    rw [htime, localTime_eq_of_pathPrefix_eq hp, hlocalQ,
      htotalOrigin] at hsafe
    exact hsafe
  have hordinaryScreened :
      (sourceProp49Spec eta a candidate hcandidate low cap).acceptedScreenedProp
        ell := by
    change decide
      ((sourceProp49Spec eta a candidate hcandidate low cap).acceptedScreenedProp
        ell) = true at hell
    simpa only [decide_eq_true_eq] using hell
  have horiginScreened : originSafeScreenedAccepts m
      (sourceOriginFixedLocalTime eta e)
      (sourceProp49Spec eta a candidate hcandidate low cap) origin ell = true := by
    simpa only [originSafeScreenedAccepts, decide_eq_true_eq] using
      And.intro hordinaryScreened hsafeCoordinates
  have hscreen : sourceOriginSafeScreenedPredicate eta a candidate hcandidate
      low e horigin cap q.1 :=
    ⟨hatom, ell, horiginScreened, htotal⟩
  let qscreen : PrefixedTilingAcceptedCappedCoordinates
      ((SourceFiber eta).stoppingTime cap) ((SourceFiber eta).initial cap) t
      ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
      ((SourceFiber eta).coordinateCap cap) ((SourceFiber eta).tail cap)
      (sourceOriginSafeScreenedPredicate eta a candidate hcandidate low e
        horigin cap) :=
    ⟨q.1, ⟨hscreen, q.2.2⟩⟩
  simp only [sourceOriginSafeCandidateNear, horigin, hcandidate, dite_true]
  exact Set.mem_iUnion.mpr ⟨cap,
    ⟨hvalid, Set.mem_iUnion.mpr ⟨qscreen, hqword⟩⟩⟩

/-- A safe target path whose shifted-origin domino is exposed belongs to the
fixed-direction target candidate family. -/
theorem mem_originSafeTargetFamily_of_path
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    {s : WalkPath} (hvalid : s ∈ validStepWalk)
    (hreach : s ∈ thresholdReachStage m k)
    (hsafe : s ∈ targetOriginSafe m k e)
    (hcard : (SourceSupportAt t o m s (creationTimeNat m k s)).card ≤
      initialBudget48 m)
    (htheta : orientedTilingThetaBases t o m (shellWidth48 m)
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m) s
      (creationTimeNat m k s) = ∅)
    (horigin : targetOriginBase t e ∈
      SourceSupportAt t o m s (creationTimeNat m k s))
    (candidate : Point)
    (hcandidate : candidate ∈
      SourceSupportAt t o m s (creationTimeNat m k s))
    (hnarrow : localTime s (creationTimeNat m k s) candidate ∈
      prop49NarrowTotalWindow m a) :
    s ∈ (originSafeTargetFamily (t := t) (o := o) a low e hm hk hwindow
      harithmetic hwidth hexternalArithmetic).someCandidate := by
  let z := fixedOrientedAllCreationTraceCode t o
    (creationTimeNat m k s) s
  let S := SourceSupportAt t o m s (creationTimeNat m k s)
  have hsAtom : s ∈ orientedAllCreationSupportTraceAtom t o m k
      (SourceSupportAt t o m) z S :=
    ⟨⟨hvalid, hreach, rfl⟩, rfl⟩
  let eta : SourceSupportedIndex t o m k :=
    ⟨(z, S), ⟨s, hsAtom⟩⟩
  have hsourceEligible : SourceProp49EligibleHistory eta :=
    ⟨hcard, ⟨s, hsAtom, htheta⟩⟩
  have horiginEta : targetOriginBase t e ∈ eta.1.2 := horigin
  have hcandidateEta : candidate ∈ eta.1.2 := hcandidate
  have hnear : s ∈ sourceOriginSafeCandidateNear eta a low e candidate :=
    mem_sourceOriginSafeCandidateNear_of_exactAtom eta a candidate
      hcandidateEta low e horiginEta hm hk hwindow harithmetic
      hexternalArithmetic hsAtom htheta hnarrow hsafe
  apply originSafeTargetNext_subset_someCandidate a low e {s} hm hk hwindow
    harithmetic hwidth hexternalArithmetic
  · intro u hu
    have hus : u = s := by simpa only [Set.mem_singleton_iff] using hu
    subst u
    exact ⟨eta, candidate, ⟨⟨hsafe, hreach⟩, hsAtom⟩,
      ⟨hsourceEligible, horiginEta⟩, hcandidateEta, hnear⟩
  · simp

end

end Erdos1165.HLOZCheckerOriginSafeProp49PathCoverage
