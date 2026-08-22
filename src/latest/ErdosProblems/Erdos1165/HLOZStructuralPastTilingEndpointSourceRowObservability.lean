/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCheckerCompleteOriginSafeObservability
import ErdosProblems.Erdos1165.HLOZCountableMeshCreationRestriction
import ErdosProblems.Erdos1165.HLOZRawNoLazyMeshCreation
import ErdosProblems.Erdos1165.HLOZStructuralPastTilingEndpointSourceRows
import ErdosProblems.Erdos1165.HLOZTransportedCanonicalProp49Observability
import ErdosProblems.Erdos1165.HLOZVariablePastFiniteSourceRowMeshLowTransition

/-!
# Stopped observability for structural endpoint-source rows

The raw rank-two and rank-three creation atoms already lie in the physical
structural past.  On those atoms the structural candidate row agrees with
its ambient observable row, including the origin-safe checker transport.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZStructuralPastTilingEndpointSourceRowObservability

open HLOZCheckerCompleteOriginSafeObservability
open HLOZCheckerOriginSafeDistinguishedProp49Family
open HLOZCheckerStructuralPastProp49Row
open HLOZCountableMeshCreationRestriction
open HLOZGapPointReturn
open HLOZMeshCandidateFutureFactor
open HLOZMeshCandidatePolynomialNumerics
open HLOZNoLazyFilteredPastObservability
open HLOZNoLazyFilteredTransitions
open HLOZNoLazyHighSpatialTransitionFactor
open HLOZNoLazyInitialBudgetMixedTransitionFactors
open HLOZNoLazyMeshCandidateCreation
open HLOZPathEvents HLOZPrefixedProp49CandidateWindowRatio
open HLOZProposition48Candidates
open HLOZRawFullGapProductPromotion
open HLOZRawNoLazyMeshCreation
open HLOZRawOrientedSourceThetaPayment
open HLOZRawProp49TilingEndpointAmbientCover
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZSpatialAdapter
open HLOZSourceCorrectFullGapClosure
open HLOZSourceEndpointTransportTable
open HLOZSourceStructuralPastInvariant
open HLOZStoppedHistoryCandidateFuture
open HLOZStructuralPastTilingEndpointSourceRows
open HLOZTilingEndpointSourceRows
open HLOZTransportedCanonicalProp49Observability
open HLOZTransportedCanonicalProp49Row
open HLOZTransportedStructuralPastProp49Row
open HLOZVariablePastFiniteSourceRowMeshLowTransition
open LazyDecomposition ScreeningInstantiation
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := HLOZFilteredTransitionAssembly.GapTriple

/-- Each ambient endpoint row is observable on a fixed rank creation atom. -/
theorem rowAmbientCandidate_fixedCreation_observable
    (t : DominoTiling) (m rank n : ℕ) (a : GapScale) (low : ℕ)
    (hm : 1 < m) (hrank : 0 < rank)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (row : TilingEndpointSourceRow t) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ n)
      {omega | ThresholdCreation (trajectory omega) m rank n ∧
        trajectory omega ∈ rowAmbientCandidateEvent t m rank a low hm hrank
          hwindow harithmetic hwidth hexternalArithmetic row} := by
  cases t with
  | checker d =>
      cases row with
      | inl o =>
          exact transportedAmbientCandidate_fixedCreation_observable_canonical
            (.checker d) o m rank n a low hm hrank hwindow harithmetic
              hexternalArithmetic
      | inr e =>
          exact checkerCompleteOriginSafeFamily_fixedCreation_observable a low e
            hm hrank hwindow harithmetic hwidth hexternalArithmetic
  | evenColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              exact transportedAmbientCandidate_fixedCreation_observable_canonical
                .evenColumns o m rank n a low hm hrank hwindow harithmetic
                  hexternalArithmetic
          | opposite =>
              exact transportedAmbientCandidate_fixedCreation_observable_column
                .evenColumns (Or.inl rfl) o m rank n a low hm hrank hwindow
                  harithmetic hexternalArithmetic
  | oddColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              exact transportedAmbientCandidate_fixedCreation_observable_canonical
                .oddColumns o m rank n a low hm hrank hwindow harithmetic
                  hexternalArithmetic
          | opposite =>
              exact transportedAmbientCandidate_fixedCreation_observable_column
                .oddColumns (Or.inr rfl) o m rank n a low hm hrank hwindow
                  harithmetic hexternalArithmetic

/-- A raw rank-two past atom remains observable after restriction to any
structural endpoint row. -/
theorem firstStructuralRow_secondCandidatePastAtom_observable
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (low : ℕ)
    (hm : 1 < m) (hwindow : Prop49WindowArithmeticAt m gaps.1.2)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (row : TilingEndpointSourceRow t) (z : PairCreationIndex) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (noLazyFilteredFirstPairCreationAtom
        (firstRawStagedCandidate data) t m gaps z ∩
          firstStructuralRowCandidateEvent t m gaps low hm hwindow harithmetic
            hwidth hexternalArithmetic row)) := by
  have hraw := pairCreationAtom_inter_filteredFirstTransitionEvent_observable
    (firstRawStagedCandidate data) t m gaps z
      (pairCreationAtom_inter_firstRawStagedCandidate_observable data t m gaps z)
  have hamb := rowAmbientCandidate_fixedCreation_observable t m 2 z.2 gaps.1.2
    low hm (by omega) hwindow harithmetic hwidth hexternalArithmetic row
  have hinter := isMeasurableAtStopping_inter hraw hamb
  have heq :
      trajectory ⁻¹' (noLazyFilteredFirstPairCreationAtom
          (firstRawStagedCandidate data) t m gaps z ∩
        firstStructuralRowCandidateEvent t m gaps low hm hwindow harithmetic
          hwidth hexternalArithmetic row) =
        (trajectory ⁻¹' noLazyFilteredFirstPairCreationAtom
          (firstRawStagedCandidate data) t m gaps z) ∩
        {omega | ThresholdCreation (trajectory omega) m 2 z.2 ∧
          trajectory omega ∈ rowAmbientCandidateEvent t m 2 gaps.1.2 low hm
            (by omega) hwindow harithmetic hwidth hexternalArithmetic row} := by
    ext omega
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hrawAtom, hcandidate⟩
      exact ⟨hrawAtom, hrawAtom.1.2.1,
        firstStructuralRowCandidateEvent_subset_ambient t m gaps low hm
          hwindow harithmetic hwidth hexternalArithmetic row hcandidate⟩
    · rintro ⟨hrawAtom, _hcreation, hambient⟩
      have hstruct : trajectory omega ∈ firstStructuralPast t m gaps :=
        ⟨hrawAtom.2.1, fun hlow ↦ hrawAtom.2.2 (Or.inl hlow)⟩
      exact ⟨hrawAtom,
        ambient_inter_firstStructural_inter_valid_subset_rowCandidate t m gaps
          low hm hwindow harithmetic hwidth hexternalArithmetic row
            ⟨⟨hambient, hstruct⟩, trajectory_mem_validStepWalk omega⟩⟩
  rw [heq]
  exact hinter

/-- Rank-three analogue of the preceding stopped-observability theorem. -/
theorem secondStructuralRow_thirdCandidatePastAtom_observable
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (low : ℕ)
    (hm : 1 < m) (hwindow : Prop49WindowArithmeticAt m gaps.2)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (row : TilingEndpointSourceRow t) (z : TripleCreationIndex) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' (noLazyFilteredSecondTripleCreationAtom
        (firstRawStagedCandidate data) (secondRawStagedCandidate data)
          t m gaps z ∩
        secondStructuralRowCandidateEvent t m gaps low hm hwindow harithmetic
          hwidth hexternalArithmetic row)) := by
  have hraw := tripleCreationAtom_inter_filteredSecondTransitionEvent_observable
    (firstRawStagedCandidate data) (secondRawStagedCandidate data) t m gaps z
      (tripleCreationAtom_inter_firstRawStagedCandidate_observable data t m
        gaps z)
      (tripleCreationAtom_inter_secondRawStagedCandidate_observable data t m
        gaps z)
  have hamb := rowAmbientCandidate_fixedCreation_observable t m 3 z.2 gaps.2
    low hm (by omega) hwindow harithmetic hwidth hexternalArithmetic row
  have hinter := isMeasurableAtStopping_inter hraw hamb
  have heq :
      trajectory ⁻¹' (noLazyFilteredSecondTripleCreationAtom
          (firstRawStagedCandidate data) (secondRawStagedCandidate data)
            t m gaps z ∩
        secondStructuralRowCandidateEvent t m gaps low hm hwindow harithmetic
          hwidth hexternalArithmetic row) =
        (trajectory ⁻¹' noLazyFilteredSecondTripleCreationAtom
          (firstRawStagedCandidate data) (secondRawStagedCandidate data)
            t m gaps z) ∩
        {omega | ThresholdCreation (trajectory omega) m 3 z.2 ∧
          trajectory omega ∈ rowAmbientCandidateEvent t m 3 gaps.2 low hm
            (by omega) hwindow harithmetic hwidth hexternalArithmetic row} := by
    ext omega
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hrawAtom, hcandidate⟩
      exact ⟨hrawAtom, hrawAtom.1.2.2.1,
        secondStructuralRowCandidateEvent_subset_ambient t m gaps low hm
          hwindow harithmetic hwidth hexternalArithmetic row hcandidate⟩
    · rintro ⟨hrawAtom, _hcreation, hambient⟩
      have hstruct : trajectory omega ∈ secondStructuralPast t m gaps :=
        ⟨hrawAtom.2.1, fun hbad ↦ hrawAtom.2.2 <|
          hbad.elim (fun h ↦ Or.inl (Or.inl h))
            (fun h ↦ Or.inr (Or.inl h))⟩
      exact ⟨hrawAtom,
        ambient_inter_secondStructural_inter_valid_subset_rowCandidate t m gaps
          low hm hwindow harithmetic hwidth hexternalArithmetic row
            ⟨⟨hambient, hstruct⟩, trajectory_mem_validStepWalk omega⟩⟩
  rw [heq]
  exact hinter

/-- The raw rank-two decomposition's literal past piece has the rowwise
stopped observability just established. -/
theorem secondRaw_firstStructuralRow_past_observable
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (low : ℕ)
    (hproper : gaps.1.2 ∈ properGapMesh)
    (hm : 1 < m) (hwindow : Prop49WindowArithmeticAt m gaps.1.2)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (row : TilingEndpointSourceRow t) (z : PairCreationIndex) :
    IsMeasurableAtStopping (fun _ : StepPath ↦
      (secondRawCountableMeshCreationData (firstRawStagedCandidate data)
        (secondRawStagedCandidate data) t m gaps hproper
          (measurableSet_firstRawStagedCandidate data t m gaps)
          (measurableSet_secondRawStagedCandidate data t m gaps)
          (pairCreationAtom_inter_firstRawStagedCandidate_observable data t m
            gaps)).oldCreation z)
      (trajectory ⁻¹'
        ((secondRawCountableMeshCreationData (firstRawStagedCandidate data)
          (secondRawStagedCandidate data) t m gaps hproper
            (measurableSet_firstRawStagedCandidate data t m gaps)
            (measurableSet_secondRawStagedCandidate data t m gaps)
            (pairCreationAtom_inter_firstRawStagedCandidate_observable data t m
              gaps)).pastPiece z ∩
          firstStructuralRowCandidateEvent t m gaps low hm hwindow harithmetic
            hwidth hexternalArithmetic row)) := by
  simpa only [secondRawCountableMeshCreationData,
    HLOZNoLazyMeshCandidateCreation.secondCountableMeshCreationData,
    CountableMeshCreationData.oldCreation, CountableMeshCreationData.pastPiece,
    secondCandidatePastAtom, inter_univ] using
      firstStructuralRow_secondCandidatePastAtom_observable data t m gaps low
        hm hwindow harithmetic hwidth hexternalArithmetic row z

/-- Rank-three raw decomposition analogue. -/
theorem thirdRaw_secondStructuralRow_past_observable
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (low : ℕ)
    (hproper : gaps.2 ∈ properGapMesh)
    (hm : 1 < m) (hwindow : Prop49WindowArithmeticAt m gaps.2)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (row : TilingEndpointSourceRow t) (z : TripleCreationIndex) :
    IsMeasurableAtStopping (fun _ : StepPath ↦
      (thirdRawCountableMeshCreationData (firstRawStagedCandidate data)
        (secondRawStagedCandidate data) (thirdRawStagedCandidate data)
          t m gaps hproper
          (measurableSet_firstRawStagedCandidate data t m gaps)
          (measurableSet_secondRawStagedCandidate data t m gaps)
          (measurableSet_thirdRawStagedCandidate data t m gaps)
          (tripleCreationAtom_inter_firstRawStagedCandidate_observable data t m
            gaps)
          (tripleCreationAtom_inter_secondRawStagedCandidate_observable data t m
            gaps)).oldCreation z)
      (trajectory ⁻¹'
        ((thirdRawCountableMeshCreationData (firstRawStagedCandidate data)
          (secondRawStagedCandidate data) (thirdRawStagedCandidate data)
            t m gaps hproper
            (measurableSet_firstRawStagedCandidate data t m gaps)
            (measurableSet_secondRawStagedCandidate data t m gaps)
            (measurableSet_thirdRawStagedCandidate data t m gaps)
            (tripleCreationAtom_inter_firstRawStagedCandidate_observable data t m
              gaps)
            (tripleCreationAtom_inter_secondRawStagedCandidate_observable data t
              m gaps)).pastPiece z ∩
          secondStructuralRowCandidateEvent t m gaps low hm hwindow harithmetic
            hwidth hexternalArithmetic row)) := by
  simpa only [thirdRawCountableMeshCreationData,
    HLOZNoLazyMeshCandidateCreation.thirdCountableMeshCreationData,
    CountableMeshCreationData.oldCreation, CountableMeshCreationData.pastPiece,
    thirdCandidatePastAtom, inter_univ] using
      secondStructuralRow_thirdCandidatePastAtom_observable data t m gaps low
        hm hwindow harithmetic hwidth hexternalArithmetic row z

/-- Restrict a raw creation decomposition to an arbitrary candidate family
whose ratio is exactly the Proposition 4.9 envelope. -/
private noncomputable def meshLowCoordinateDataOfRaw
    {History Candidate Index : Type 0} [Countable History] [Countable Index]
    {m rank : ℕ} {a : GapScale} {previous rawNext : Set WalkPath}
    (candidate : StoppedHistoryCandidateFamily History Candidate previous
      (initialBudget48 m)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a))
    (hcandidate : MeasurableSet candidate.someCandidate)
    (raw : CountableMeshCreationData Index Set.univ rawNext m rank a)
    (hpast : ∀ i, IsMeasurableAtStopping
      (fun _ : StepPath ↦ raw.oldCreation i)
      (trajectory ⁻¹' (raw.pastPiece i ∩ candidate.someCandidate))) :
    FirstStripMeshLowCoordinateData prop49WindowRatioConstant m rank a previous
      (rawNext ∩ candidate.someCandidate) where
  History := History
  Candidate := Candidate
  Index := Index
  candidateRatio := prop49CandidateRatioEnvelope
    prop49WindowRatioConstant m a
  candidate := candidate
  creation := CountableMeshCreationData.inter raw hcandidate hpast
  ratio_le := le_rfl

/-- One literal rank-two structural endpoint row, including its own stopped
past and restricted raw creation decomposition. -/
noncomputable def firstStructuralRowMeshLowCoordinateData
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (low : ℕ)
    (hproper : gaps.1.2 ∈ properGapMesh)
    (hm : 1 < m) (hwindow : Prop49WindowArithmeticAt m gaps.1.2)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (row : TilingEndpointSourceRow t) :
    FirstStripMeshLowCoordinateData prop49WindowRatioConstant m 2 gaps.1.2
      (firstStructuralRowPrevious t m gaps row)
      (filteredSecondTransitionEvent (firstRawStagedCandidate data)
        (secondRawStagedCandidate data) t m gaps ∩
        firstStructuralRowCandidateEvent t m gaps low hm hwindow harithmetic
          hwidth hexternalArithmetic row) := by
  let raw := secondRawCountableMeshCreationData (firstRawStagedCandidate data)
    (secondRawStagedCandidate data) t m gaps hproper
      (measurableSet_firstRawStagedCandidate data t m gaps)
      (measurableSet_secondRawStagedCandidate data t m gaps)
      (pairCreationAtom_inter_firstRawStagedCandidate_observable data t m gaps)
  have hpast (row : TilingEndpointSourceRow t) : ∀ z,
      IsMeasurableAtStopping (fun _ : StepPath ↦ raw.oldCreation z)
        (trajectory ⁻¹' (raw.pastPiece z ∩
          firstStructuralRowCandidateEvent t m gaps low hm hwindow harithmetic
            hwidth hexternalArithmetic row)) :=
    secondRaw_firstStructuralRow_past_observable data t m gaps low hproper hm
      hwindow harithmetic hwidth hexternalArithmetic row
  cases t with
  | checker d =>
      cases row with
      | inl o =>
          exact meshLowCoordinateDataOfRaw
            (firstCanonicalStructuralFamily (.checker d) o m gaps gaps.1.2 low
              hm hwindow harithmetic hexternalArithmetic)
            (measurableSet_firstStructuralRowCandidateEvent (.checker d) m
              gaps low hm hwindow harithmetic hwidth hexternalArithmetic
                (Sum.inl o)) raw (hpast (Sum.inl o))
      | inr e =>
          exact meshLowCoordinateDataOfRaw
            (firstCheckerStructuralFamily d m gaps gaps.1.2 low e hm hwindow
              harithmetic hwidth hexternalArithmetic)
            (measurableSet_firstStructuralRowCandidateEvent (.checker d) m
              gaps low hm hwindow harithmetic hwidth hexternalArithmetic
                (Sum.inr e)) raw (hpast (Sum.inr e))
  | evenColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              exact meshLowCoordinateDataOfRaw
                (firstCanonicalStructuralFamily .evenColumns o m gaps gaps.1.2
                  low hm hwindow harithmetic hexternalArithmetic)
                (measurableSet_firstStructuralRowCandidateEvent .evenColumns m
                  gaps low hm hwindow harithmetic hwidth hexternalArithmetic
                    ⟨o, .canonical⟩) raw (hpast ⟨o, .canonical⟩)
          | opposite =>
              exact meshLowCoordinateDataOfRaw
                (firstStructuralTransportedFamily .evenColumns o .opposite m
                  gaps gaps.1.2 low hm hwindow harithmetic hexternalArithmetic)
                (measurableSet_firstStructuralRowCandidateEvent .evenColumns m
                  gaps low hm hwindow harithmetic hwidth hexternalArithmetic
                    ⟨o, .opposite⟩) raw (hpast ⟨o, .opposite⟩)
  | oddColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              exact meshLowCoordinateDataOfRaw
                (firstCanonicalStructuralFamily .oddColumns o m gaps gaps.1.2
                  low hm hwindow harithmetic hexternalArithmetic)
                (measurableSet_firstStructuralRowCandidateEvent .oddColumns m
                  gaps low hm hwindow harithmetic hwidth hexternalArithmetic
                    ⟨o, .canonical⟩) raw (hpast ⟨o, .canonical⟩)
          | opposite =>
              exact meshLowCoordinateDataOfRaw
                (firstStructuralTransportedFamily .oddColumns o .opposite m
                  gaps gaps.1.2 low hm hwindow harithmetic hexternalArithmetic)
                (measurableSet_firstStructuralRowCandidateEvent .oddColumns m
                  gaps low hm hwindow harithmetic hwidth hexternalArithmetic
                    ⟨o, .opposite⟩) raw (hpast ⟨o, .opposite⟩)

@[simp] theorem firstStructuralRowMeshLowCoordinateData_candidateRatio
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (low : ℕ)
    (hproper : gaps.1.2 ∈ properGapMesh)
    (hm : 1 < m) (hwindow : Prop49WindowArithmeticAt m gaps.1.2)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (row : TilingEndpointSourceRow t) :
    (firstStructuralRowMeshLowCoordinateData data t m gaps low hproper hm
      hwindow harithmetic hwidth hexternalArithmetic row).candidateRatio =
        prop49CandidateRatioEnvelope prop49WindowRatioConstant m gaps.1.2 := by
  cases t with
  | checker _ => cases row <;> rfl
  | evenColumns => cases row with | mk _ cls => cases cls <;> rfl
  | oddColumns => cases row with | mk _ cls => cases cls <;> rfl

/-- One literal rank-three structural endpoint row. -/
noncomputable def secondStructuralRowMeshLowCoordinateData
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (low : ℕ)
    (hproper : gaps.2 ∈ properGapMesh)
    (hm : 1 < m) (hwindow : Prop49WindowArithmeticAt m gaps.2)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (row : TilingEndpointSourceRow t) :
    FirstStripMeshLowCoordinateData prop49WindowRatioConstant m 3 gaps.2
      (secondStructuralRowPrevious t m gaps row)
      (filteredThirdTransitionEvent (firstRawStagedCandidate data)
        (secondRawStagedCandidate data) (thirdRawStagedCandidate data)
          t m gaps ∩
        secondStructuralRowCandidateEvent t m gaps low hm hwindow harithmetic
          hwidth hexternalArithmetic row) := by
  let raw := thirdRawCountableMeshCreationData (firstRawStagedCandidate data)
    (secondRawStagedCandidate data) (thirdRawStagedCandidate data)
      t m gaps hproper
      (measurableSet_firstRawStagedCandidate data t m gaps)
      (measurableSet_secondRawStagedCandidate data t m gaps)
      (measurableSet_thirdRawStagedCandidate data t m gaps)
      (tripleCreationAtom_inter_firstRawStagedCandidate_observable data t m gaps)
      (tripleCreationAtom_inter_secondRawStagedCandidate_observable data t m
        gaps)
  have hpast (row : TilingEndpointSourceRow t) : ∀ z,
      IsMeasurableAtStopping (fun _ : StepPath ↦ raw.oldCreation z)
        (trajectory ⁻¹' (raw.pastPiece z ∩
          secondStructuralRowCandidateEvent t m gaps low hm hwindow harithmetic
            hwidth hexternalArithmetic row)) :=
    thirdRaw_secondStructuralRow_past_observable data t m gaps low hproper hm
      hwindow harithmetic hwidth hexternalArithmetic row
  cases t with
  | checker d =>
      cases row with
      | inl o =>
          exact meshLowCoordinateDataOfRaw
            (secondCanonicalStructuralFamily (.checker d) o m gaps gaps.2 low
              hm hwindow harithmetic hexternalArithmetic)
            (measurableSet_secondStructuralRowCandidateEvent (.checker d) m
              gaps low hm hwindow harithmetic hwidth hexternalArithmetic
                (Sum.inl o)) raw (hpast (Sum.inl o))
      | inr e =>
          exact meshLowCoordinateDataOfRaw
            (secondCheckerStructuralFamily d m gaps gaps.2 low e hm hwindow
              harithmetic hwidth hexternalArithmetic)
            (measurableSet_secondStructuralRowCandidateEvent (.checker d) m
              gaps low hm hwindow harithmetic hwidth hexternalArithmetic
                (Sum.inr e)) raw (hpast (Sum.inr e))
  | evenColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              exact meshLowCoordinateDataOfRaw
                (secondCanonicalStructuralFamily .evenColumns o m gaps gaps.2
                  low hm hwindow harithmetic hexternalArithmetic)
                (measurableSet_secondStructuralRowCandidateEvent .evenColumns m
                  gaps low hm hwindow harithmetic hwidth hexternalArithmetic
                    ⟨o, .canonical⟩) raw (hpast ⟨o, .canonical⟩)
          | opposite =>
              exact meshLowCoordinateDataOfRaw
                (secondStructuralTransportedFamily .evenColumns o .opposite m
                  gaps gaps.2 low hm hwindow harithmetic hexternalArithmetic)
                (measurableSet_secondStructuralRowCandidateEvent .evenColumns m
                  gaps low hm hwindow harithmetic hwidth hexternalArithmetic
                    ⟨o, .opposite⟩) raw (hpast ⟨o, .opposite⟩)
  | oddColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              exact meshLowCoordinateDataOfRaw
                (secondCanonicalStructuralFamily .oddColumns o m gaps gaps.2
                  low hm hwindow harithmetic hexternalArithmetic)
                (measurableSet_secondStructuralRowCandidateEvent .oddColumns m
                  gaps low hm hwindow harithmetic hwidth hexternalArithmetic
                    ⟨o, .canonical⟩) raw (hpast ⟨o, .canonical⟩)
          | opposite =>
              exact meshLowCoordinateDataOfRaw
                (secondStructuralTransportedFamily .oddColumns o .opposite m
                  gaps gaps.2 low hm hwindow harithmetic hexternalArithmetic)
                (measurableSet_secondStructuralRowCandidateEvent .oddColumns m
                  gaps low hm hwindow harithmetic hwidth hexternalArithmetic
                    ⟨o, .opposite⟩) raw (hpast ⟨o, .opposite⟩)

@[simp] theorem secondStructuralRowMeshLowCoordinateData_candidateRatio
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (low : ℕ)
    (hproper : gaps.2 ∈ properGapMesh)
    (hm : 1 < m) (hwindow : Prop49WindowArithmeticAt m gaps.2)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (row : TilingEndpointSourceRow t) :
    (secondStructuralRowMeshLowCoordinateData data t m gaps low hproper hm
      hwindow harithmetic hwidth hexternalArithmetic row).candidateRatio =
        prop49CandidateRatioEnvelope prop49WindowRatioConstant m gaps.2 := by
  cases t with
  | checker _ => cases row <;> rfl
  | evenColumns => cases row with | mk _ cls => cases cls <;> rfl
  | oddColumns => cases row with | mk _ cls => cases cls <;> rfl

/-- The six variable-past rank-two rows after removing the exact additive
source/Theta payment and restricting to valid trajectories. -/
noncomputable def firstPaymentFilteredVariablePastRowData
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (low : ℕ)
    (hproper : gaps.1.2 ∈ properGapMesh) (hlow : gaps.1.2 ∈ lowGapMesh)
    (hm : 1 < m) (hwindow : Prop49WindowArithmeticAt m gaps.1.2)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    VariablePastFiniteSourceRowMeshLowCoordinateData
      (TilingEndpointSourceRow t) (6 * prop49WindowRatioConstant) m 2 gaps.1.2
      (firstStructuralPast t m gaps)
      (filteredSecondTransitionEvent (firstRawStagedCandidate data)
          (secondRawStagedCandidate data) t m gaps \
        rawOrientedSourceThetaTotalPaymentAtRank data t 2 m) where
  rowPrevious := firstStructuralRowPrevious t m gaps
  rowPrevious_measurable := measurableSet_firstStructuralRowPrevious t m gaps
  rowPrevious_measure_le := firstStructuralRowPrevious_measure_le t m gaps hm
  rowNext := fun row ↦
    filteredSecondTransitionEvent (firstRawStagedCandidate data)
      (secondRawStagedCandidate data) t m gaps ∩
        firstStructuralRowCandidateEvent t m gaps low hm hwindow harithmetic
          hwidth hexternalArithmetic row
  rowNext_measurable := fun row ↦ by
    let raw := secondRawCountableMeshCreationData
      (firstRawStagedCandidate data) (secondRawStagedCandidate data) t m gaps
        hproper (measurableSet_firstRawStagedCandidate data t m gaps)
        (measurableSet_secondRawStagedCandidate data t m gaps)
        (pairCreationAtom_inter_firstRawStagedCandidate_observable data t m
          gaps)
    have hraw : MeasurableSet
        (filteredSecondTransitionEvent (firstRawStagedCandidate data)
          (secondRawStagedCandidate data) t m gaps) := by
      rw [← raw.next_union]
      exact MeasurableSet.iUnion raw.next_measurable
    exact hraw.inter (measurableSet_firstStructuralRowCandidateEvent t m gaps
      low hm hwindow harithmetic hwidth hexternalArithmetic row)
  next_subset := by
    intro s hs
    have hvalid : s ∈ validStepWalk := by
      by_contra hnotValid
      exact hs.2 (Or.inr (Or.inl hnotValid))
    have hrows := filteredSecond_inter_payment_compl_inter_valid_subset_rows
      data t m gaps low hlow hm hwindow harithmetic hwidth hexternalArithmetic
        ⟨hs, hvalid⟩
    rcases Set.mem_iUnion.mp hrows with ⟨row, hrow⟩
    exact Set.mem_iUnion_of_mem row ⟨hs.1, hrow⟩
  rowConstant := fun _ ↦ prop49WindowRatioConstant
  row := firstStructuralRowMeshLowCoordinateData data t m gaps low hproper hm
    hwindow harithmetic hwidth hexternalArithmetic
  ratio_sum_le := by
    simpa only [firstStructuralRowMeshLowCoordinateData_candidateRatio] using
      sum_candidateRatio_le_six t m gaps.1.2

/-- Terminal rank-three variable-past row data. -/
noncomputable def secondPaymentFilteredVariablePastRowData
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (low : ℕ)
    (hproper : gaps.2 ∈ properGapMesh) (hlow : gaps.2 ∈ lowGapMesh)
    (hm : 1 < m) (hwindow : Prop49WindowArithmeticAt m gaps.2)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    VariablePastFiniteSourceRowMeshLowCoordinateData
      (TilingEndpointSourceRow t) (6 * prop49WindowRatioConstant) m 3 gaps.2
      (secondStructuralPast t m gaps)
      (filteredThirdTransitionEvent (firstRawStagedCandidate data)
          (secondRawStagedCandidate data) (thirdRawStagedCandidate data)
            t m gaps \
        rawOrientedSourceThetaTotalPaymentAtRank data t 3 m) where
  rowPrevious := secondStructuralRowPrevious t m gaps
  rowPrevious_measurable := measurableSet_secondStructuralRowPrevious t m gaps
  rowPrevious_measure_le := secondStructuralRowPrevious_measure_le t m gaps hm
  rowNext := fun row ↦
    filteredThirdTransitionEvent (firstRawStagedCandidate data)
      (secondRawStagedCandidate data) (thirdRawStagedCandidate data)
        t m gaps ∩
        secondStructuralRowCandidateEvent t m gaps low hm hwindow harithmetic
          hwidth hexternalArithmetic row
  rowNext_measurable := fun row ↦ by
    let raw := thirdRawCountableMeshCreationData
      (firstRawStagedCandidate data) (secondRawStagedCandidate data)
        (thirdRawStagedCandidate data) t m gaps hproper
        (measurableSet_firstRawStagedCandidate data t m gaps)
        (measurableSet_secondRawStagedCandidate data t m gaps)
        (measurableSet_thirdRawStagedCandidate data t m gaps)
        (tripleCreationAtom_inter_firstRawStagedCandidate_observable data t m
          gaps)
        (tripleCreationAtom_inter_secondRawStagedCandidate_observable data t m
          gaps)
    have hraw : MeasurableSet
        (filteredThirdTransitionEvent (firstRawStagedCandidate data)
          (secondRawStagedCandidate data) (thirdRawStagedCandidate data)
            t m gaps) := by
      rw [← raw.next_union]
      exact MeasurableSet.iUnion raw.next_measurable
    exact hraw.inter (measurableSet_secondStructuralRowCandidateEvent t m gaps
      low hm hwindow harithmetic hwidth hexternalArithmetic row)
  next_subset := by
    intro s hs
    have hvalid : s ∈ validStepWalk := by
      by_contra hnotValid
      exact hs.2 (Or.inr (Or.inl hnotValid))
    have hrows := filteredThird_inter_payment_compl_inter_valid_subset_rows
      data t m gaps low hlow hm hwindow harithmetic hwidth hexternalArithmetic
        ⟨hs, hvalid⟩
    rcases Set.mem_iUnion.mp hrows with ⟨row, hrow⟩
    exact Set.mem_iUnion_of_mem row ⟨hs.1, hrow⟩
  rowConstant := fun _ ↦ prop49WindowRatioConstant
  row := secondStructuralRowMeshLowCoordinateData data t m gaps low hproper hm
    hwindow harithmetic hwidth hexternalArithmetic
  ratio_sum_le := by
    simpa only [secondStructuralRowMeshLowCoordinateData_candidateRatio] using
      sum_candidateRatio_le_six t m gaps.2

theorem measure_filteredSecond_diff_payment_le_transition_mul_structuralPast
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (low : ℕ)
    (hproper : gaps.1.2 ∈ properGapMesh) (hlow : gaps.1.2 ∈ lowGapMesh)
    (hm : 1 < m) (hwindow : Prop49WindowArithmeticAt m gaps.1.2)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (hnumeric : (initialBudget48 m : ℝ≥0∞) *
      prop49CandidateRatioEnvelope (6 * prop49WindowRatioConstant) m gaps.1.2 *
        meshEscapeCost m gaps.1.2 ≤ UpperCanonical.hlozTransitionCost 1 m) :
    simpleRandomWalk
        (filteredSecondTransitionEvent (firstRawStagedCandidate data)
            (secondRawStagedCandidate data) t m gaps \
          rawOrientedSourceThetaTotalPaymentAtRank data t 2 m) ≤
      UpperCanonical.hlozTransitionCost 1 m *
        simpleRandomWalk (firstStructuralPast t m gaps) :=
  VariablePastFiniteSourceRowMeshLowCoordinateData.measure_next_le
    (firstPaymentFilteredVariablePastRowData data t m gaps low hproper hlow hm
      hwindow harithmetic hwidth hexternalArithmetic) (by omega) hnumeric

theorem measure_filteredThird_diff_payment_le_transition_mul_structuralPast
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (low : ℕ)
    (hproper : gaps.2 ∈ properGapMesh) (hlow : gaps.2 ∈ lowGapMesh)
    (hm : 1 < m) (hwindow : Prop49WindowArithmeticAt m gaps.2)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (hnumeric : (initialBudget48 m : ℝ≥0∞) *
      prop49CandidateRatioEnvelope (6 * prop49WindowRatioConstant) m gaps.2 *
        meshEscapeCost m gaps.2 ≤ UpperCanonical.hlozTransitionCost 1 m) :
    simpleRandomWalk
        (filteredThirdTransitionEvent (firstRawStagedCandidate data)
            (secondRawStagedCandidate data) (thirdRawStagedCandidate data)
              t m gaps \
          rawOrientedSourceThetaTotalPaymentAtRank data t 3 m) ≤
      UpperCanonical.hlozTransitionCost 1 m *
        simpleRandomWalk (secondStructuralPast t m gaps) :=
  VariablePastFiniteSourceRowMeshLowCoordinateData.measure_next_le
    (secondPaymentFilteredVariablePastRowData data t m gaps low hproper hlow hm
      hwindow harithmetic hwidth hexternalArithmetic) (by omega) hnumeric

end

end Erdos1165.HLOZStructuralPastTilingEndpointSourceRowObservability
