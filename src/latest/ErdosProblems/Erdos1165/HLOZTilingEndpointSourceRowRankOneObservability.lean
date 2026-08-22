/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZCheckerCompleteOriginSafeObservability
import ErdosProblems.Erdos1165.HLOZPaymentFilteredTilingEndpointSourceRowData
import ErdosProblems.Erdos1165.HLOZRawNoLazyMeshCreation
import ErdosProblems.Erdos1165.HLOZRawProp49TilingEndpointAmbientCover
import ErdosProblems.Erdos1165.HLOZTransportedCanonicalProp49Observability

/-!
# Rank-one observability for every physical endpoint-source row

The raw rank-one creation piece is observable after intersection with each
of the finite source rows.  Canonical and column rows use the existing
transport observability.  The checker-opposite rows use the complete
fixed-direction origin-safe theorem.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZTilingEndpointSourceRowRankOneObservability

open HLOZCheckerCompleteOriginSafeObservability
open HLOZCheckerOriginSafeDistinguishedProp49Family
open HLOZMeshCandidatePolynomialNumerics
open HLOZMeshCandidateFutureFactor
open HLOZNoLazyMeshCandidateCreation
open HLOZNoLazyFilteredTransitions
open HLOZNoLazyFiniteSourceRowUpperAssembly
open HLOZPaymentFilteredTilingEndpointSourceRowData
open HLOZPathEvents HLOZPrefixedProp49CandidateWindowRatio
open HLOZProposition48Candidates
open HLOZRawNoLazyMeshCreation
open HLOZRawOrientedSourceThetaPayment
open HLOZRawFullGapProductPromotion
open HLOZRawProp49TilingEndpointAmbientCover
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZSourceEndpointTransportTable
open HLOZSourceCorrectFullGapClosure
open HLOZStoppedCandidatePreviousRebase
open HLOZStoppedHistoryCandidateFuture
open HLOZTilingEndpointSourceRowProp49
open HLOZTilingEndpointSourceRows
open HLOZTransportedCanonicalProp49Observability
open HLOZTransportedCanonicalProp49Row
open HLOZThetaOneSourceShift
open LazyDecomposition ScreeningInstantiation

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Rebasing a stopped family to the universal past changes no candidate
event. -/
private theorem someCandidate_rebaseToPrevious_univ_eq
    {History Candidate : Type*} [Countable History]
    {oldPrevious : Set WalkPath} {budget : ℕ} {ratio : ℝ≥0∞}
    (family : StoppedHistoryCandidateFamily History Candidate oldPrevious
      budget ratio) :
    (rebaseToPrevious family Set.univ MeasurableSet.univ).someCandidate =
      family.someCandidate := by
  apply Set.Subset.antisymm
  · intro s hs
    unfold StoppedHistoryCandidateFamily.someCandidate at hs ⊢
    rcases Set.mem_iUnion.mp hs with ⟨history, hs⟩
    rcases Set.mem_iUnion.mp hs with ⟨candidate, hs⟩
    rcases Set.mem_iUnion.mp hs with ⟨hcandidate, hpiece, hnear⟩
    cases history with
    | none =>
        change candidate ∈ (∅ : Finset Candidate) at hcandidate
        simp at hcandidate
    | some history =>
        have hcandidates := (mem_rebasedCandidates_some_iff family Set.univ
          history candidate).mp hcandidate
        exact Set.mem_iUnion_of_mem history <| Set.mem_iUnion_of_mem candidate <|
          Set.mem_iUnion_of_mem hcandidates.2 ⟨hpiece.2, hnear⟩
  · exact StoppedHistoryCandidateFamily.someCandidate_subset_rebaseToPrevious_of_subset
      family Set.univ MeasurableSet.univ (subset_univ _)

/-- On the universal rank-one past, a rebased checker-opposite row is
literally the complete fixed-direction checker row. -/
theorem checkerOriginSafeRebasedFamily_univ_someCandidate
    (d : Tilings.CheckerDirection) (e : Direction)
    (m k : ℕ) (a : GapScale) (low : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    (checkerOriginSafeRebasedFamily d e m k a low Set.univ
      MeasurableSet.univ hm hk hwindow harithmetic hwidth
        hexternalArithmetic).someCandidate =
      (checkerCompleteOriginSafeFamily
        (t := shiftedCheckerTarget d) (o := .even) a low e hm hk hwindow
          harithmetic hwidth hexternalArithmetic).someCandidate :=
  someCandidate_rebaseToPrevious_univ_eq _

/-- Every physical endpoint row is observable on a fixed rank-one creation
atom. -/
theorem rowCandidateEvent_univ_firstCandidatePastAtom_observable
    (t : DominoTiling) (m n : ℕ) (a : GapScale) (low : ℕ)
    (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (row : TilingEndpointSourceRow t) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ n)
      (trajectory ⁻¹' firstCandidatePastAtom
        (rowCandidateEvent t m 1 a low Set.univ MeasurableSet.univ hm
          (by omega) hwindow harithmetic hwidth hexternalArithmetic row) m n) := by
  cases t with
  | checker d =>
      cases row with
      | inl o =>
          exact candidateFamily_univ_firstCandidatePastAtom_observable_canonical
            (.checker d) o m n a low hm hwindow harithmetic
              hexternalArithmetic
      | inr e =>
          change IsMeasurableAtStopping (fun _ : StepPath ↦ n)
            (trajectory ⁻¹' firstCandidatePastAtom
              (checkerOriginSafeRebasedFamily d e m 1 a low Set.univ
                MeasurableSet.univ hm (by omega) hwindow harithmetic hwidth
                  hexternalArithmetic).someCandidate m n)
          rw [checkerOriginSafeRebasedFamily_univ_someCandidate]
          exact checkerCompleteOriginSafeFamily_firstCandidatePastAtom_observable
            (t := shiftedCheckerTarget d) (o := .even) a low e hm hwindow
              harithmetic hwidth hexternalArithmetic
  | evenColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              exact candidateFamily_univ_firstCandidatePastAtom_observable_canonical
                .evenColumns o m n a low hm hwindow harithmetic
                  hexternalArithmetic
          | opposite =>
              exact candidateFamily_univ_firstCandidatePastAtom_observable_column
                .evenColumns (Or.inl rfl) o m n a low hm hwindow harithmetic
                  hexternalArithmetic
  | oddColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              exact candidateFamily_univ_firstCandidatePastAtom_observable_canonical
                .oddColumns o m n a low hm hwindow harithmetic
                  hexternalArithmetic
          | opposite =>
              exact candidateFamily_univ_firstCandidatePastAtom_observable_column
                .oddColumns (Or.inr rfl) o m n a low hm hwindow harithmetic
                  hexternalArithmetic

/-- The raw rank-one decomposition's past piece remains observable after
intersection with any one of the six physical source rows. -/
theorem firstRaw_rowCandidate_past_observable
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ)
    (gaps : HLOZRawFullGapProductPromotion.GapTriple) (low : ℕ)
    (hproper : gaps.1.1 ∈ properGapMesh)
    (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m gaps.1.1)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (row : TilingEndpointSourceRow t) (n : ℕ) :
    IsMeasurableAtStopping (fun _ : StepPath ↦
      (firstRawCountableMeshCreationData (firstRawStagedCandidate data) t m
        gaps hproper
          (measurableSet_firstRawStagedCandidate data t m gaps)).oldCreation n)
      (trajectory ⁻¹'
        ((firstRawCountableMeshCreationData (firstRawStagedCandidate data) t m
          gaps hproper
            (measurableSet_firstRawStagedCandidate data t m gaps)).pastPiece n ∩
          rowCandidateEvent t m 1 gaps.1.1 low Set.univ MeasurableSet.univ hm
            (by omega) hwindow harithmetic hwidth hexternalArithmetic row)) := by
  simpa only [firstRawCountableMeshCreationData,
    HLOZNoLazyMeshCandidateCreation.firstCountableMeshCreationData,
    CountableMeshCreationData.oldCreation,
    CountableMeshCreationData.pastPiece, id_eq, firstCandidatePastAtom,
    inter_univ, inter_assoc] using
    rowCandidateEvent_univ_firstCandidatePastAtom_observable t m n gaps.1.1
      low hm hwindow harithmetic hwidth hexternalArithmetic row

/-- Concrete hidden six-row rank-one low data after removing the exact
source/Theta payment. -/
noncomputable def firstPaymentFilteredFiniteRowMeshLowCoordinateData
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ)
    (gaps : HLOZRawFullGapProductPromotion.GapTriple) (low : ℕ)
    (hproper : gaps.1.1 ∈ properGapMesh)
    (hlow : gaps.1.1 ∈ lowGapMesh)
    (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m gaps.1.1)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    HeterogeneousFiniteSourceRowMeshLowCoordinateData
      (6 * prop49WindowRatioConstant) m 1 gaps.1.1 Set.univ
      (filteredFirstTransitionEvent (firstRawStagedCandidate data) t m gaps \
        rawOrientedSourceThetaTotalPaymentAtRank data t 1 m) :=
  heterogeneousFiniteRowMeshLowCoordinateDataOutside
    (rawOrientedSourceThetaTotalPaymentAtRank data t 1 m) t m 1 gaps.1.1 low
      Set.univ MeasurableSet.univ hm (by omega) hwindow harithmetic hwidth
        hexternalArithmetic
      (firstRawCountableMeshCreationData (firstRawStagedCandidate data) t m
        gaps hproper (measurableSet_firstRawStagedCandidate data t m gaps))
      (firstRaw_rowCandidate_past_observable data t m gaps low hproper hm
        hwindow harithmetic hwidth hexternalArithmetic)
      (filteredFirstTransitionEvent_subset_payment_union_rows data t m gaps low
        hm hlow hwindow harithmetic hwidth hexternalArithmetic)

end

end Erdos1165.HLOZTilingEndpointSourceRowRankOneObservability
