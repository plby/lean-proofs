/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZRawProp49CanonicalAmbientCover
import ErdosProblems.Erdos1165.HLOZRawProp49NarrowCandidateGeometry
import ErdosProblems.Erdos1165.HLOZRawProp49OppositeCheckerExposedOriginCover
import ErdosProblems.Erdos1165.HLOZRawProp49OppositeColumnAmbientCover
import ErdosProblems.Erdos1165.HLOZTilingEndpointSourceRowProp49

/-!
# Ambient six-row coverage for unpaid raw transitions

Every raw low transition outside the literal source/Theta payment has one
dominant narrow endpoint.  Its spatial endpoint class and temporal parity
select one of the finite physical Proposition 4.9 rows.  For checker-opposite
endpoints the first physical direction selects the fixed-prefix row, whose
complete target family handles both exposed and distinguished shifted
origins.

This theorem deliberately stops at the ambient source rows.  Passing to a
rank-two or rank-three spatial past additionally requires the exact stopped
atom carrying the witness to be absorbed by that past.
-/

open Set
open scoped ENNReal

namespace Erdos1165.HLOZRawProp49TilingEndpointAmbientCover

open HLOZCheckerOriginSafeDistinguishedProp49Family
open HLOZNoLazyFilteredTransitions
open HLOZPathEvents HLOZPrefixedProp49CandidateWindowRatio
open HLOZProposition48Candidates
open HLOZRawFullGapProductPromotion
open HLOZRawOrientedSourceThetaPayment
open HLOZRawProp49CanonicalAmbientCover
open HLOZRawProp49NarrowCandidateGeometry
open HLOZRawProp49OppositeCheckerExposedOriginCover
open HLOZRawProp49OppositeColumnAmbientCover
open HLOZRawProp49SourceCardinality HLOZRawProp49UnpaidProfile
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZSourceCorrectFullGapClosure
open HLOZSourceEndpointTransportTable
open HLOZSourceTransportStoppedCandidateFamily
open HLOZStoppedCandidatePreviousRebase
open HLOZStoppedCandidatePreviousRestriction
open HLOZStoppedHistoryCandidateFuture
open HLOZThetaSourceBalance
open HLOZThetaOneSourceShift
open HLOZTilingEndpointBandExtraction
open HLOZTilingEndpointSourceRows
open HLOZTransportedCanonicalProp49Row
open LazyDecomposition ScreeningInstantiation SpatialInsertionFiber
open TilingLazyDecomposition
open TilingOrientedShellZeroSourcePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The literal ambient candidate union associated with a physical endpoint
row, before restricting its stopped atoms to a spatial rank past. -/
noncomputable def rowAmbientCandidateEvent
    (t : DominoTiling) (m k : ℕ) (a : GapScale) (low : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    TilingEndpointSourceRow t → Set WalkPath := by
  cases t with
  | checker d =>
      intro row
      cases row with
      | inl o =>
          exact (transportedAmbientFamily (.checker d) o .canonical m k a low
            hm hk hwindow harithmetic hexternalArithmetic).someCandidate
      | inr e =>
          exact (checkerCompleteOriginSafeFamily
            (t := shiftedCheckerTarget d) (o := .even) a low e hm hk hwindow
              harithmetic hwidth hexternalArithmetic).someCandidate
  | evenColumns =>
      exact fun row ↦
        (transportedAmbientFamily .evenColumns row.1 row.2 m k a low hm hk
          hwindow harithmetic hexternalArithmetic).someCandidate
  | oddColumns =>
      exact fun row ↦
        (transportedAmbientFamily .oddColumns row.1 row.2 m k a low hm hk
          hwindow harithmetic hexternalArithmetic).someCandidate

private theorem mem_transportedAmbientFamily_canonical_of_unpaid
    {data : FullBetaSourceCorrectAllTilingProductData}
    {t : DominoTiling} {o : Orientation} {rank m : ℕ}
    (a : GapScale) (low : ℕ)
    (hrank : 0 < rank)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    {s : WalkPath}
    (hprofile : RawProp49UnpaidProfile data t rank m s)
    (hcard : RawProp49SourceCardinalityProfile t m rank s)
    (candidate : Point)
    (hclass : dominantEndpointClass t candidate = .canonical)
    (horientation : OrientationCompatible o candidate)
    (hdominance : localTime s (creationTimeNat m rank s)
        (tilingPartner t candidate) ≤
      localTime s (creationTimeNat m rank s) candidate)
    (hnarrow : localTime s (creationTimeNat m rank s) candidate ∈
      prop49NarrowTotalWindow m a) :
    s ∈ (transportedAmbientFamily t o .canonical m rank a low
      (by have := hprofile.level_two; omega) hrank hwindow harithmetic
        hexternalArithmetic).someCandidate := by
  have htarget := mem_targetAmbientFamily_canonical_of_unpaid a low hrank
    hwindow harithmetic hexternalArithmetic hprofile hcard candidate hclass
      horientation hdominance hnarrow
  change s ∈ (stoppedHistoryCandidateFamilySourceTransport t .canonical
    (targetAmbientFamily t o .canonical m rank a low
      (by have := hprofile.level_two; omega) hrank hwindow harithmetic
        hexternalArithmetic)
    (targetAmbientNear_measurable t o .canonical m rank a low
      (by have := hprofile.level_two; omega) hrank hwindow harithmetic
        hexternalArithmetic)).someCandidate
  rw [StoppedHistoryCandidateFamily.someCandidate_sourceTransport]
  simpa only [HLOZSourceTransportCoordinateMass.sourceTransportPreimage,
    sourceTransportPath, Set.mem_preimage, id_eq] using htarget

/-- The six ambient physical rows cover every unpaid narrow transition. -/
theorem mem_iUnion_rowAmbientCandidateEvent_of_unpaid
    {data : FullBetaSourceCorrectAllTilingProductData}
    {t : DominoTiling} {rank m : ℕ}
    (a : GapScale) (low : ℕ)
    (hm : 1 < m) (hrank : 0 < rank) (hrank_le : rank ≤ 3)
    (ha : a ∈ lowGapMesh)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    {s : WalkPath}
    (hprofile : RawProp49UnpaidProfile data t rank m s)
    (hnarrowProfile : RawProp49NarrowCandidateProfile t m rank a s) :
    s ∈ ⋃ row : TilingEndpointSourceRow t,
      rowAmbientCandidateEvent t m rank a low hm hrank hwindow harithmetic
        hwidth hexternalArithmetic row := by
  rcases hnarrowProfile.exists_times with
    ⟨nOld, nNew, hcreationOld, _hcreationNew, _hscale, hnarrowOld⟩
  have hclock : creationTimeNat m rank s = nOld :=
    creationTimeNat_eq_of_creation hcreationOld
  let candidate := tilingDominantEndpointAt t s nOld (s nNew)
  have hnarrow : localTime s (creationTimeNat m rank s) candidate ∈
      prop49NarrowTotalWindow m a := by
    rw [hclock]
    exact hnarrowOld
  have hdominance : localTime s (creationTimeNat m rank s)
        (tilingPartner t candidate) ≤
      localTime s (creationTimeNat m rank s) candidate := by
    rw [hclock]
    exact tilingDominantEndpointAt_partner_le t s nOld (s nNew)
  have hcard :=
    HLOZRawProp49SourceCardinality.RawProp49UnpaidProfile.sourceCardinalityProfile
      hprofile hrank hrank_le ha
  let o := compatibleOrientation candidate
  have horientation : OrientationCompatible o candidate :=
    compatibleOrientation_compatible candidate
  cases t with
  | checker d =>
      cases hclass : dominantEndpointClass (.checker d) candidate with
      | canonical =>
          apply Set.mem_iUnion_of_mem (Sum.inl o)
          exact mem_transportedAmbientFamily_canonical_of_unpaid a low hrank
            hwindow harithmetic hexternalArithmetic hprofile hcard candidate
              hclass horientation hdominance hnarrow
      | opposite =>
          let e : Direction := stepsOfWalk s 0
          have hfirst : s 1 = directionVector e := by
            rw [← hprofile.valid]
            simp [e, trajectory_succ]
          apply Set.mem_iUnion_of_mem (Sum.inr e)
          exact mem_checkerCompleteOriginSafeFamily_of_unpaid a low e hm hrank
            hrank_le ha hwindow harithmetic hwidth hexternalArithmetic hprofile
              candidate hclass hdominance hnarrow hfirst
  | evenColumns =>
      cases hclass : dominantEndpointClass .evenColumns candidate with
      | canonical =>
          apply Set.mem_iUnion_of_mem (o, .canonical)
          exact mem_transportedAmbientFamily_canonical_of_unpaid a low hrank
            hwindow harithmetic hexternalArithmetic hprofile hcard candidate
              hclass horientation hdominance hnarrow
      | opposite =>
          apply Set.mem_iUnion_of_mem (o, .opposite)
          exact mem_transportedAmbientFamily_opposite_column_of_unpaid
            (by simp [IsColumnTiling]) a low hm hrank hrank_le ha hwindow harithmetic
              hexternalArithmetic hprofile candidate hclass horientation
                hdominance hnarrow
  | oddColumns =>
      cases hclass : dominantEndpointClass .oddColumns candidate with
      | canonical =>
          apply Set.mem_iUnion_of_mem (o, .canonical)
          exact mem_transportedAmbientFamily_canonical_of_unpaid a low hrank
            hwindow harithmetic hexternalArithmetic hprofile hcard candidate
              hclass horientation hdominance hnarrow
      | opposite =>
          apply Set.mem_iUnion_of_mem (o, .opposite)
          exact mem_transportedAmbientFamily_opposite_column_of_unpaid
            (by simp [IsColumnTiling]) a low hm hrank hrank_le ha hwindow harithmetic
              hexternalArithmetic hprofile candidate hclass horientation
                hdominance hnarrow

private theorem someCandidate_subset_restrictToPrevious_univ
    {History Candidate : Type*} [Countable History]
    {budget : ℕ} {ratio : ℝ≥0∞}
    (ambient : StoppedHistoryCandidateFamily History Candidate Set.univ
      budget ratio) :
    ambient.someCandidate ⊆
      (restrictToPrevious ambient Set.univ MeasurableSet.univ).someCandidate := by
  intro s hs
  unfold StoppedHistoryCandidateFamily.someCandidate at hs
  rcases Set.mem_iUnion.mp hs with ⟨h, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨candidate, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨hcandidate, hpiece, hnear⟩
  exact StoppedHistoryCandidateFamily.mem_someCandidate_restrictToPrevious
    ambient Set.univ MeasurableSet.univ h candidate (subset_univ _)
      hpiece hcandidate hnear

/-- On the rank-one past `univ`, the ambient and spatially rebased rows have
the same candidate coverage. -/
theorem rowAmbientCandidateEvent_subset_rowCandidateEvent_univ
    (t : DominoTiling) (m k : ℕ) (a : GapScale) (low : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (row : TilingEndpointSourceRow t) :
    rowAmbientCandidateEvent t m k a low hm hk hwindow harithmetic hwidth
        hexternalArithmetic row ⊆
      HLOZTilingEndpointSourceRowProp49.rowCandidateEvent t m k a low Set.univ
        MeasurableSet.univ hm hk hwindow harithmetic hwidth
          hexternalArithmetic row := by
  cases t with
  | checker d =>
      cases row with
      | inl o =>
          exact someCandidate_subset_restrictToPrevious_univ
            (transportedAmbientFamily (.checker d) o .canonical m k a low hm
              hk hwindow harithmetic hexternalArithmetic)
      | inr e =>
          exact
            StoppedHistoryCandidateFamily.someCandidate_subset_rebaseToPrevious_of_subset
              (checkerCompleteOriginSafeFamily
                (t := shiftedCheckerTarget d) (o := .even) a low e hm hk
                  hwindow harithmetic hwidth hexternalArithmetic)
              Set.univ MeasurableSet.univ (subset_univ _)
  | evenColumns =>
      exact someCandidate_subset_restrictToPrevious_univ
        (transportedAmbientFamily .evenColumns row.1 row.2 m k a low hm hk
          hwindow harithmetic hexternalArithmetic)
  | oddColumns =>
      exact someCandidate_subset_restrictToPrevious_univ
        (transportedAmbientFamily .oddColumns row.1 row.2 m k a low hm hk
          hwindow harithmetic hexternalArithmetic)

/-- Rank-one specialization of the unpaid six-row cover. -/
theorem mem_iUnion_rowCandidateEvent_univ_of_unpaid
    {data : FullBetaSourceCorrectAllTilingProductData}
    {t : DominoTiling} {rank m : ℕ}
    (a : GapScale) (low : ℕ)
    (hm : 1 < m) (hrank : 0 < rank) (hrank_le : rank ≤ 3)
    (ha : a ∈ lowGapMesh)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    {s : WalkPath}
    (hprofile : RawProp49UnpaidProfile data t rank m s)
    (hnarrowProfile : RawProp49NarrowCandidateProfile t m rank a s) :
    s ∈ ⋃ row : TilingEndpointSourceRow t,
      HLOZTilingEndpointSourceRowProp49.rowCandidateEvent t m rank a low
        Set.univ MeasurableSet.univ hm hrank hwindow harithmetic hwidth
          hexternalArithmetic row := by
  rcases Set.mem_iUnion.mp
      (mem_iUnion_rowAmbientCandidateEvent_of_unpaid a low hm hrank hrank_le
        ha hwindow harithmetic hwidth hexternalArithmetic hprofile
          hnarrowProfile) with ⟨row, hrow⟩
  exact Set.mem_iUnion_of_mem row
    (rowAmbientCandidateEvent_subset_rowCandidateEvent_univ t m rank a low hm
      hrank hwindow harithmetic hwidth hexternalArithmetic row hrow)

/-- The exact rank-one raw transition is covered by its source/Theta payment
or one of the six physical Proposition 4.9 rows. -/
theorem filteredFirstTransitionEvent_subset_payment_union_rows
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ)
    (gaps : HLOZRawFullGapProductPromotion.GapTriple) (low : ℕ)
    (hm : 1 < m)
    (hlow : gaps.1.1 ∈ lowGapMesh)
    (hwindow : Prop49WindowArithmeticAt m gaps.1.1)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    HLOZNoLazyFilteredTransitions.filteredFirstTransitionEvent
        (firstRawStagedCandidate data) t m gaps ⊆
      rawOrientedSourceThetaTotalPaymentAtRank data t 1 m ∪
        ⋃ row : TilingEndpointSourceRow t,
          HLOZTilingEndpointSourceRowProp49.rowCandidateEvent t m 1 gaps.1.1
            low Set.univ MeasurableSet.univ hm (by omega) hwindow harithmetic hwidth
                hexternalArithmetic row := by
  intro s hs
  by_cases hpaid : s ∈ rawOrientedSourceThetaTotalPaymentAtRank data t 1 m
  · exact Or.inl hpaid
  · apply Or.inr
    have hpreliminary : s ∈ firstRawCandidatePreliminary t m gaps := by
      exact ⟨hs.1, fun hfailure ↦ hs.2 (Or.inl hfailure)⟩
    have hunpaid : s ∈ firstRawCandidatePreliminary t m gaps \
        rawOrientedSourceThetaTotalPaymentAtRank data t 1 m :=
      ⟨hpreliminary, hpaid⟩
    have hprofile := firstRawCandidatePreliminary_unpaid_profile data t m gaps
      s hunpaid
    have hnarrow := firstRawCandidatePreliminary_narrowCandidateProfile t m
      gaps s hm hlow hpreliminary
    exact mem_iUnion_rowCandidateEvent_univ_of_unpaid gaps.1.1 low
      hm (by omega) (by omega) hlow
        hwindow harithmetic hwidth hexternalArithmetic hprofile hnarrow

end

end Erdos1165.HLOZRawProp49TilingEndpointAmbientCover
