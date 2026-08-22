/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZPrefixedCanonicalSourceProp49Refinement
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaWindowSplit

/-!
# Physical-path coverage of the canonical Proposition 4.9 screen

The conditional product construction supplies the narrow stopped fibres and
their probability ratio.  This file proves the converse deterministic fact
needed by the raw low transition: a path in an exact source-good stopped atom
whose selected dominant endpoint is in the narrow window belongs to one of
those fibres.
-/

open Set

namespace Erdos1165.HLOZPrefixedCanonicalSourceProp49PathCoverage

open FiniteDominoProductLaw HLOZPathEvents
open HLOZTypedStoppedCandidateObservability
open HLOZPrefixedAllCreationCanonicalDominantWindows
open HLOZPrefixedCanonicalSourceAtomRecovery
open HLOZPrefixedCanonicalSourceLowRecovery
open HLOZPrefixedCanonicalSourceProp49Data
open HLOZPrefixedCanonicalSourceProp49Data.SourceThetaGoodRepresentative
open HLOZPrefixedCanonicalSourceProp49Refinement
open HLOZPrefixedProp49CandidateWindowRatio HLOZProposition48Candidates
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZSourceOrientedThetaWindowSplit
open HLOZTilingConditionalCandidateWindows
open HLOZThetaSourceBalance LazyDecomposition PreStoppingFiber
open PreStoppingSpatialLaw SpatialInsertionFiber StoppedInsertion
open TilingCappedMarginalization TilingLazyDecomposition
open TilingInsertedLocalTime
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingDistinguishedTraceInvariant TilingPrefixedInsertedLocalTime
open TilingPrefixedFavoriteTraceSupport
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Exact stopped source histories with a narrow selected endpoint are covered
by the prefix-correct Proposition 4.9 candidate event. -/
theorem mem_sourceProp49CandidateNear_of_exactAtom
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) (a : GapScale)
    (candidate : Point) (hcandidate : candidate ∈ eta.1.2) (low : ℕ)
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
      prop49NarrowTotalWindow m a) :
    s ∈ sourceProp49CandidateNear eta a low candidate := by
  classical
  simp only [sourceProp49CandidateNear, hcandidate, dite_true]
  apply Set.mem_iUnion.mpr
  have hcomplete := (SourceFiber eta).atom_complete hs
  rcases Set.mem_iUnion.mp hcomplete with ⟨cap, hcap⟩
  refine ⟨cap, ?_⟩
  rcases hcap with ⟨hvalid, hevent⟩
  rcases Set.mem_iUnion.mp hevent with ⟨q, hqword⟩
  let D := supportComplementDistinguished t eta.1.1.external.start
    eta.1.1.external.retained eta.1.2
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
  have hcanonical := canonical_mem_supportAtom_of_predicate_accepted
    ((SourceFiber eta).coordinateCap cap) q.1 q.2.1 q.2.2
  have hbelow := sourceCanonical_strictAway eta q.1 hcanonical q.2.2
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
  let away := (splitTilingCoordinatesEquiv t eta.1.1.external.start
    eta.1.1.external.retained D q.1).2
  let spec := sourceProp49Spec eta a candidate hcandidate low cap
  let ell : TruncatedTotals spec.upper := fun b ↦
    ⟨tilingAwayTotal t eta.1.1.external.start
        eta.1.1.external.retained D away b,
      by
        have hb := hbelow b.1 b.2
        have htotal : tilingAwayTotal t eta.1.1.external.start
            eta.1.1.external.retained D away b =
            tilingDominoTotal t eta.1.1.external.start
              eta.1.1.external.retained (fun j ↦ (q.1 j : ℕ)) b.1 := by
          dsimp only [away]
          exact tilingAwayTotal_split_eq_dominoTotal _ _ _ _ _ _
        have htotalLt : tilingAwayTotal t eta.1.1.external.start
            eta.1.1.external.retained D away b < m := by
          rw [htotal]
          omega
        have hmUpper : m < (SourceFiber eta).upper cap b :=
          (m_le_sourceFiber_totalCap eta).trans_lt
            ((SourceFiber eta).totalCap_lt_upper cap b)
        exact htotalLt.trans hmUpper⟩
  have good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m) :=
    { path := s, mem_atom := hs, theta_good := htheta }
  have hratio := good.acceptedRatioData a candidate hcandidate low hm hk
    hwindow harithmetic hexternalArithmetic cap
  have hscreened : spec.acceptedScreenedProp ell := by
    rw [spec.acceptedScreenedProp_iff_windows ell hratio.coverage]
    intro b
    have hlocalQ : localTime sq v.length b.1.1 =
        prefixedTilingFixedBoundaryLocalTime ((SourceFiber eta).initial cap)
            ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
            (sourceTerminal eta) b.1.1 +
          tilingDominoTotal t ((SourceFiber eta).start cap)
            ((SourceFiber eta).retained cap) (fun j ↦ (q.1 j : ℕ)) b.1 := by
      rw [localTime_eq_listLocalTime, hpath,
        prefixedTilingInsertedPrefix_localTime_at_dominoPoint
          ((SourceFiber eta).initial cap) t ((SourceFiber eta).start cap)
          ((SourceFiber eta).retained cap) (fun j ↦ (q.1 j : ℕ))
          (sourceTerminal eta) b.1 b.1.1]
      exact tilingExternalDomino_isBase t ((SourceFiber eta).start cap)
        ((SourceFiber eta).retained cap) b.1
    have htotal : (ell b : ℕ) =
        tilingDominoTotal t ((SourceFiber eta).start cap)
          ((SourceFiber eta).retained cap) (fun j ↦ (q.1 j : ℕ)) b.1 := by
      change tilingAwayTotal t eta.1.1.external.start
        eta.1.1.external.retained D away b = _
      exact tilingAwayTotal_split_eq_dominoTotal _ _ _ _ _ _
    have hlocalS : localTime s (creationTimeNat m k s) b.1.1 =
        prefixedTilingFixedBoundaryLocalTime ((SourceFiber eta).initial cap)
            ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
            (sourceTerminal eta) b.1.1 + (ell b : ℕ) := by
      rw [htime, localTime_eq_of_pathPrefix_eq hp, hlocalQ, htotal]
    by_cases hb : b = spec.chosen
    · subst b
      have hnarrowSubset : prop49NarrowTotalWindow m a ⊆
          shellZeroSourceTotalWindow m (shellWidth48 m) :=
        prop49NarrowTotalWindow_subset_source
          ((show 1 ≤ 2 by norm_num).trans harithmetic.1)
          harithmetic.2.1 hwindow.cut_le_width_pred
      have hchosenBase : spec.chosen.1.1 = candidate := by
        dsimp only [spec, sourceProp49Spec]
        exact sourceChosen_base cap eta candidate hcandidate
      rw [spec.acceptedScreenedWindow_chosen
          (sourceChosen_fixedBoundary_partner_le_base (cap := cap) eta
            candidate hcandidate)
          (by rw [hchosenBase]; exact hcandidate)
          (good.away_fixedBoundary_external_window (cap := cap) hm hk
            spec.chosen)
          rfl hnarrowSubset]
      rw [shiftedEndpointWindow, Finset.mem_filter]
      refine ⟨Finset.mem_range.mpr (ell spec.chosen).isLt, ?_⟩
      change prefixedTilingFixedBoundaryLocalTime
          ((SourceFiber eta).initial cap) ((SourceFiber eta).start cap)
          ((SourceFiber eta).retained cap) (sourceTerminal eta)
          spec.chosen.1.1 + (ell spec.chosen : ℕ) ∈
        prop49NarrowTotalWindow m a
      rw [← hlocalS, hchosenBase]
      exact hnarrow
    · rw [spec.acceptedScreenedWindow_eq_base b hb]
      have hbaseEq := good.acceptedBaseWindow_eq_shifted (cap := cap)
        candidate hcandidate low
        (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m) rfl rfl hm hk
        (prop49NarrowTotalWindow m a) b
      change spec.acceptedBaseWindow b = _ at hbaseEq
      rw [hbaseEq]
      change (ell b : ℕ) ∈ (Finset.range (spec.upper b)).filter (fun v ↦
        prefixedTilingFixedBoundaryLocalTime spec.initial spec.x spec.r
          spec.terminal b.1.1 + v ∈
            shellZeroSourceTotalWindow m (shellWidth48 m))
      refine Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (ell b).isLt, ?_⟩
      change prefixedTilingFixedBoundaryLocalTime
          ((SourceFiber eta).initial cap) ((SourceFiber eta).start cap)
          ((SourceFiber eta).retained cap) (sourceTerminal eta) b.1.1 +
          (ell b : ℕ) ∈ shellZeroSourceTotalWindow m (shellWidth48 m)
      rw [← hlocalS]
      have hbS : b.1.1 ∈ eta.1.2 :=
        away_mem_sourceSupport (cap := cap) eta b
      have hbSource : b.1.1 ∈ orientedTilingVTwoBases t o
          (shellZeroSourceTotalWindow m (shellWidth48 m)) s
          (creationTimeNat m k s) := by
        change b.1.1 ∈ SourceSupportAt t o m s (creationTimeNat m k s)
        rw [hs.2]
        exact hbS
      exact (Finset.mem_filter.mp
        ((mem_orientedTilingVTwoBases_iff t o
          (shellZeroSourceTotalWindow m (shellWidth48 m)) s
          (creationTimeNat m k s) b.1.1).mp hbSource).1).2.2
  have hscreen : sourceProp49ScreenedPredicate eta a candidate hcandidate
      low cap q.1 := by
    refine ⟨q.2.1, ell, ?_, ?_⟩
    · dsimp only [spec, sourceProp49Spec] at hscreened ⊢
      simpa only [PrefixedCanonicalDominantCandidateWindowSpec.acceptedScreenedAccepts,
        decide_eq_true_eq] using hscreened
    · intro b
      rfl
  let qscreen : PrefixedTilingAcceptedCappedCoordinates
      ((SourceFiber eta).stoppingTime cap) ((SourceFiber eta).initial cap) t
      ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
      ((SourceFiber eta).coordinateCap cap) ((SourceFiber eta).tail cap)
      (sourceProp49ScreenedPredicate eta a candidate hcandidate low cap) :=
    ⟨q.1, ⟨hscreen, q.2.2⟩⟩
  refine ⟨hvalid, Set.mem_iUnion.mpr ⟨qscreen, ?_⟩⟩
  exact hqword

/-- With no level-`m+1` site at the old creation clock, the replacement
part of oriented Theta is empty.  Hence excluding the source-window
restriction excludes the complete Theta family required by Proposition 4.9. -/
theorem orientedTilingThetaAtCreation_eq_empty_of_restrictedSource_empty
    {t : DominoTiling} {o : Orientation} {m k w externalLow externalHigh : ℕ}
    {s : WalkPath}
    (hnext : thresholdCount s (creationTimeNat m k s) (m + 1) = 0)
    (hsource : orientedRestrictedThetaSourceAtCreation t o m k w externalLow
      externalHigh s = ∅) :
    orientedTilingThetaAtCreation t o m k w externalLow externalHigh s = ∅ := by
  rw [orientedTilingThetaAtCreation_eq_source_union_replacement]
  apply Finset.union_eq_empty.mpr
  refine ⟨hsource, ?_⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  rw [orientedRestrictedThetaReplacementAtCreation,
    Finset.mem_filter] at hb
  have hlt := (thresholdCount_eq_zero_iff_forall_lt
    s (creationTimeNat m k s) (m + 1) (by omega)).mp hnext b
  rw [mem_shellZeroReplacementTotalWindow] at hb
  omega

/-- A physical canonical path with a small exact source support, no
restricted-Theta coordinate, and one narrow candidate belongs to the
unrestricted Proposition 4.9 candidate family.  The stopped history index is
constructed from the path itself; no atom-containment or transition premise
is required. -/
theorem mem_sourceProp49StoppedHistoryCandidateFamily_univ_of_path
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    {s : WalkPath} (hvalid : s ∈ validStepWalk)
    (hreach : s ∈ thresholdReachStage m k)
    (hcard : (SourceSupportAt t o m s (creationTimeNat m k s)).card ≤
      initialBudget48 m)
    (htheta : orientedTilingThetaBases t o m (shellWidth48 m)
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m) s
      (creationTimeNat m k s) = ∅)
    (candidate : Point)
    (hcandidate : candidate ∈
      SourceSupportAt t o m s (creationTimeNat m k s))
    (hnarrow : localTime s (creationTimeNat m k s) candidate ∈
      prop49NarrowTotalWindow m a) :
    s ∈ (sourceProp49StoppedHistoryCandidateFamily
      (t := t) (o := o) a low Set.univ MeasurableSet.univ
      (fun _ _ ↦ subset_univ _) hm hk hwindow harithmetic
        hexternalArithmetic).someCandidate := by
  let z := fixedOrientedAllCreationTraceCode t o
    (creationTimeNat m k s) s
  let S := SourceSupportAt t o m s (creationTimeNat m k s)
  have hsAtom : s ∈ orientedAllCreationSupportTraceAtom t o m k
      (SourceSupportAt t o m) z S := by
    exact ⟨⟨hvalid, hreach, rfl⟩, rfl⟩
  let eta : SourceSupportedIndex t o m k :=
    ⟨(z, S), ⟨s, hsAtom⟩⟩
  have heligible : SourceProp49EligibleHistory eta := by
    refine ⟨?_, ⟨s, hsAtom, ?_⟩⟩
    · exact hcard
    · exact htheta
  have hcandidateEta : candidate ∈ eta.1.2 := hcandidate
  have hnear : s ∈ sourceProp49CandidateNear eta a low candidate :=
    mem_sourceProp49CandidateNear_of_exactAtom eta a candidate
      hcandidateEta low hm hk hwindow harithmetic hexternalArithmetic
      hsAtom htheta hnarrow
  have hsubset := sourceProp49Next_subset_someCandidate a low Set.univ {s}
    MeasurableSet.univ (fun _ _ ↦ subset_univ _) hm hk hwindow harithmetic
      hexternalArithmetic (by
        intro u hu
        have hus : u = s := by
          simpa only [Set.mem_singleton_iff] using hu
        subst u
        exact ⟨eta, candidate, ⟨Set.mem_univ s, hsAtom⟩, heligible,
          hcandidateEta, hnear⟩)
  exact hsubset (by simp)

end

end Erdos1165.HLOZPrefixedCanonicalSourceProp49PathCoverage
