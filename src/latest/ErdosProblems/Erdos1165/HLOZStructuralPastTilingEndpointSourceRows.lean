/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCheckerStructuralPastProp49Row
import ErdosProblems.Erdos1165.HLOZRawProp49TilingEndpointAmbientCover
import ErdosProblems.Erdos1165.HLOZTransportedStructuralPastProp49Row

/-!
# Physical endpoint rows on the structural rank pasts

This module selects the rank-two and rank-three Proposition 4.9 families for
all six physical endpoint rows.  Canonical and column rows have the literal
physical structural past.  A checker-opposite row retains its origin-safe
recentered past, whose mass is bounded by the physical past.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZStructuralPastTilingEndpointSourceRows

open HLOZCheckerOriginSafeEventProp49Family
open HLOZCheckerOriginSafeProp49Family
open HLOZCheckerPrefixedCylinderTransport
open HLOZCheckerStructuralPastProp49Row
open HLOZNoLazyFilteredTransitions
open HLOZPathEvents HLOZPrefixedProp49CandidateWindowRatio
open HLOZProposition48Candidates
open HLOZRawFullGapProductPromotion HLOZRawOrientedSourceThetaPayment
open HLOZRawProp49NarrowCandidateGeometry
open HLOZRawProp49TilingEndpointAmbientCover
open HLOZRawProp49UnpaidProfile
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZSourceCorrectFullGapClosure
open HLOZSourceEndpointTransportTable
open HLOZSourceStructuralPastInvariant
open HLOZSourceTransportCoordinateMass
open HLOZStoppedHistoryCandidateFuture
open HLOZTilingEndpointSourceRows
open HLOZTransportedCanonicalProp49Row
open HLOZTransportedStructuralPastProp49Row
open HLOZThetaOneSourceShift
open LazyDecomposition ScreeningInstantiation
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := HLOZFilteredTransitionAssembly.GapTriple

private theorem measurableSet_someCandidate_of_near
    {History Candidate : Type*} [Countable History] [Countable Candidate]
    {previous : Set WalkPath} {budget : ℕ} {ratio : ℝ≥0∞}
    (family : StoppedHistoryCandidateFamily History Candidate previous budget
      ratio)
    (hnear : ∀ h x, MeasurableSet (family.near h x)) :
    MeasurableSet family.someCandidate := by
  unfold StoppedHistoryCandidateFamily.someCandidate
  apply MeasurableSet.iUnion
  intro h
  apply MeasurableSet.iUnion
  intro x
  apply MeasurableSet.iUnion
  intro _hx
  exact (family.piece_measurable h).inter (hnear h x)

/-- The literal past used by a physical rank-two source row. -/
noncomputable def firstStructuralRowPrevious
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) :
    TilingEndpointSourceRow t → Set WalkPath := by
  cases t with
  | checker d =>
      intro row
      cases row with
      | inl _ => exact firstStructuralPast (.checker d) m gaps
      | inr e =>
          exact checkerPrefixedPreimage e
            (((targetOriginSafe m 2 e ∩ thresholdReachStage m 2) ∩
              firstStructuralPast (shiftedCheckerTarget d) m gaps))
  | evenColumns =>
      intro row
      exact match row.2 with
        | .canonical => firstStructuralPast .evenColumns m gaps
        | .opposite => sourceTransportPreimage .evenColumns .opposite
            (firstStructuralPast
              (TargetTiling .evenColumns .opposite) m gaps)
  | oddColumns =>
      intro row
      exact match row.2 with
        | .canonical => firstStructuralPast .oddColumns m gaps
        | .opposite => sourceTransportPreimage .oddColumns .opposite
            (firstStructuralPast
              (TargetTiling .oddColumns .opposite) m gaps)

/-- The literal past used by a physical rank-three source row. -/
noncomputable def secondStructuralRowPrevious
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) :
    TilingEndpointSourceRow t → Set WalkPath := by
  cases t with
  | checker d =>
      intro row
      cases row with
      | inl _ => exact secondStructuralPast (.checker d) m gaps
      | inr e =>
          exact checkerPrefixedPreimage e
            (((targetOriginSafe m 3 e ∩ thresholdReachStage m 3) ∩
              secondStructuralPast (shiftedCheckerTarget d) m gaps))
  | evenColumns =>
      intro row
      exact match row.2 with
        | .canonical => secondStructuralPast .evenColumns m gaps
        | .opposite => sourceTransportPreimage .evenColumns .opposite
            (secondStructuralPast
              (TargetTiling .evenColumns .opposite) m gaps)
  | oddColumns =>
      intro row
      exact match row.2 with
        | .canonical => secondStructuralPast .oddColumns m gaps
        | .opposite => sourceTransportPreimage .oddColumns .opposite
            (secondStructuralPast
              (TargetTiling .oddColumns .opposite) m gaps)

/-- Candidate union in one rank-two structural row. -/
noncomputable def firstStructuralRowCandidateEvent
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (low : ℕ)
    (hm : 1 < m) (hwindow : Prop49WindowArithmeticAt m gaps.1.2)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    TilingEndpointSourceRow t → Set WalkPath := by
  cases t with
  | checker d =>
      intro row
      cases row with
      | inl o => exact (firstCanonicalStructuralFamily (.checker d) o m gaps
          gaps.1.2 low hm hwindow harithmetic hexternalArithmetic).someCandidate
      | inr e => exact (firstCheckerStructuralFamily d m gaps gaps.1.2 low e hm
          hwindow harithmetic hwidth hexternalArithmetic).someCandidate
  | evenColumns =>
      intro row
      cases row with
      | mk o cls =>
          cases cls with
          | canonical => exact (firstCanonicalStructuralFamily .evenColumns o
              m gaps gaps.1.2 low hm hwindow harithmetic
                hexternalArithmetic).someCandidate
          | opposite => exact (firstStructuralTransportedFamily .evenColumns o
              .opposite m gaps gaps.1.2 low hm hwindow harithmetic
                hexternalArithmetic).someCandidate
  | oddColumns =>
      intro row
      cases row with
      | mk o cls =>
          cases cls with
          | canonical => exact (firstCanonicalStructuralFamily .oddColumns o
              m gaps gaps.1.2 low hm hwindow harithmetic
                hexternalArithmetic).someCandidate
          | opposite => exact (firstStructuralTransportedFamily .oddColumns o
              .opposite m gaps gaps.1.2 low hm hwindow harithmetic
                hexternalArithmetic).someCandidate

/-- Candidate union in one rank-three structural row. -/
noncomputable def secondStructuralRowCandidateEvent
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (low : ℕ)
    (hm : 1 < m) (hwindow : Prop49WindowArithmeticAt m gaps.2)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    TilingEndpointSourceRow t → Set WalkPath := by
  cases t with
  | checker d =>
      intro row
      cases row with
      | inl o => exact (secondCanonicalStructuralFamily (.checker d) o m gaps
          gaps.2 low hm hwindow harithmetic hexternalArithmetic).someCandidate
      | inr e => exact (secondCheckerStructuralFamily d m gaps gaps.2 low e hm
          hwindow harithmetic hwidth hexternalArithmetic).someCandidate
  | evenColumns =>
      intro row
      cases row with
      | mk o cls =>
          cases cls with
          | canonical => exact (secondCanonicalStructuralFamily .evenColumns o
              m gaps gaps.2 low hm hwindow harithmetic
                hexternalArithmetic).someCandidate
          | opposite => exact (secondStructuralTransportedFamily .evenColumns o
              .opposite m gaps gaps.2 low hm hwindow harithmetic
                hexternalArithmetic).someCandidate
  | oddColumns =>
      intro row
      cases row with
      | mk o cls =>
          cases cls with
          | canonical => exact (secondCanonicalStructuralFamily .oddColumns o
              m gaps gaps.2 low hm hwindow harithmetic
                hexternalArithmetic).someCandidate
          | opposite => exact (secondStructuralTransportedFamily .oddColumns o
              .opposite m gaps gaps.2 low hm hwindow harithmetic
                hexternalArithmetic).someCandidate

theorem measurableSet_firstStructuralRowPrevious
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple)
    (row : TilingEndpointSourceRow t) :
    MeasurableSet (firstStructuralRowPrevious t m gaps row) := by
  cases t with
  | checker d =>
      cases row with
      | inl _ =>
          simpa [firstStructuralRowPrevious] using
            measurableSet_firstStructuralPast (.checker d) m gaps
      | inr e =>
          simpa [firstStructuralRowPrevious] using
            measurableSet_checkerPrefixedPreimage
            (((measurableSet_targetOriginSafe m 2 e).inter
              (measurableSet_thresholdReachStage m 2)).inter
              (measurableSet_firstStructuralPast (shiftedCheckerTarget d) m
                gaps)) e
  | evenColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              simpa [firstStructuralRowPrevious] using
                measurableSet_firstStructuralPast .evenColumns m gaps
          | opposite =>
              change MeasurableSet (sourceTransportPreimage .evenColumns
                .opposite (firstStructuralPast
                  (TargetTiling .evenColumns .opposite) m gaps))
              exact (measurableSet_firstStructuralPast
                (TargetTiling .evenColumns .opposite) m gaps).preimage
                  (measurable_sourceTransportPath .evenColumns .opposite)
  | oddColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              simpa [firstStructuralRowPrevious] using
                measurableSet_firstStructuralPast .oddColumns m gaps
          | opposite =>
              change MeasurableSet (sourceTransportPreimage .oddColumns
                .opposite (firstStructuralPast
                  (TargetTiling .oddColumns .opposite) m gaps))
              exact (measurableSet_firstStructuralPast
                (TargetTiling .oddColumns .opposite) m gaps).preimage
                  (measurable_sourceTransportPath .oddColumns .opposite)

theorem measurableSet_secondStructuralRowPrevious
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple)
    (row : TilingEndpointSourceRow t) :
    MeasurableSet (secondStructuralRowPrevious t m gaps row) := by
  cases t with
  | checker d =>
      cases row with
      | inl _ =>
          simpa [secondStructuralRowPrevious] using
            measurableSet_secondStructuralPast (.checker d) m gaps
      | inr e =>
          simpa [secondStructuralRowPrevious] using
            measurableSet_checkerPrefixedPreimage
            (((measurableSet_targetOriginSafe m 3 e).inter
              (measurableSet_thresholdReachStage m 3)).inter
              (measurableSet_secondStructuralPast (shiftedCheckerTarget d) m
                gaps)) e
  | evenColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              simpa [secondStructuralRowPrevious] using
                measurableSet_secondStructuralPast .evenColumns m gaps
          | opposite =>
              change MeasurableSet (sourceTransportPreimage .evenColumns
                .opposite (secondStructuralPast
                  (TargetTiling .evenColumns .opposite) m gaps))
              exact (measurableSet_secondStructuralPast
                (TargetTiling .evenColumns .opposite) m gaps).preimage
                  (measurable_sourceTransportPath .evenColumns .opposite)
  | oddColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              simpa [secondStructuralRowPrevious] using
                measurableSet_secondStructuralPast .oddColumns m gaps
          | opposite =>
              change MeasurableSet (sourceTransportPreimage .oddColumns
                .opposite (secondStructuralPast
                  (TargetTiling .oddColumns .opposite) m gaps))
              exact (measurableSet_secondStructuralPast
                (TargetTiling .oddColumns .opposite) m gaps).preimage
                  (measurable_sourceTransportPath .oddColumns .opposite)

theorem firstStructuralRowPrevious_measure_le
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (hm : 1 < m)
    (row : TilingEndpointSourceRow t) :
    simpleRandomWalk (firstStructuralRowPrevious t m gaps row) ≤
      simpleRandomWalk (firstStructuralPast t m gaps) := by
  cases t with
  | checker d =>
      cases row with
      | inl _ => simpa [firstStructuralRowPrevious]
      | inr e =>
          simpa [firstStructuralRowPrevious] using
            firstCheckerStructuralPrevious_measure_le d m gaps e hm
  | evenColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical => simpa [firstStructuralRowPrevious]
          | opposite =>
              change simpleRandomWalk (sourceTransportPreimage .evenColumns
                .opposite (firstStructuralPast
                  (TargetTiling .evenColumns .opposite) m gaps)) ≤ _
              rw [firstStructuralPreimage_opposite_column .evenColumns
                (by simp [IsColumnTiling]) m (by omega) gaps]
  | oddColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical => simpa [firstStructuralRowPrevious]
          | opposite =>
              change simpleRandomWalk (sourceTransportPreimage .oddColumns
                .opposite (firstStructuralPast
                  (TargetTiling .oddColumns .opposite) m gaps)) ≤ _
              rw [firstStructuralPreimage_opposite_column .oddColumns
                (by simp [IsColumnTiling]) m (by omega) gaps]

theorem secondStructuralRowPrevious_measure_le
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (hm : 1 < m)
    (row : TilingEndpointSourceRow t) :
    simpleRandomWalk (secondStructuralRowPrevious t m gaps row) ≤
      simpleRandomWalk (secondStructuralPast t m gaps) := by
  cases t with
  | checker d =>
      cases row with
      | inl _ => simpa [secondStructuralRowPrevious]
      | inr e =>
          simpa [secondStructuralRowPrevious] using
            secondCheckerStructuralPrevious_measure_le d m gaps e hm
  | evenColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical => simpa [secondStructuralRowPrevious]
          | opposite =>
              change simpleRandomWalk (sourceTransportPreimage .evenColumns
                .opposite (secondStructuralPast
                  (TargetTiling .evenColumns .opposite) m gaps)) ≤ _
              rw [secondStructuralPreimage_opposite_column .evenColumns
                (by simp [IsColumnTiling]) m (by omega) gaps]
  | oddColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical => simpa [secondStructuralRowPrevious]
          | opposite =>
              change simpleRandomWalk (sourceTransportPreimage .oddColumns
                .opposite (secondStructuralPast
                  (TargetTiling .oddColumns .opposite) m gaps)) ≤ _
              rw [secondStructuralPreimage_opposite_column .oddColumns
                (by simp [IsColumnTiling]) m (by omega) gaps]

theorem measurableSet_firstStructuralRowCandidateEvent
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (low : ℕ)
    (hm : 1 < m) (hwindow : Prop49WindowArithmeticAt m gaps.1.2)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (row : TilingEndpointSourceRow t) :
    MeasurableSet (firstStructuralRowCandidateEvent t m gaps low hm hwindow
      harithmetic hwidth hexternalArithmetic row) := by
  cases t with
  | checker d =>
      cases row with
      | inl o =>
          apply measurableSet_someCandidate_of_near
          intro h candidate
          change MeasurableSet
            ((firstStructuralTransportedFamily (.checker d) o .canonical m
              gaps gaps.1.2 low hm hwindow harithmetic
                hexternalArithmetic).near h candidate)
          exact firstStructuralTransportedFamily_near_measurable (.checker d) o
            .canonical m gaps gaps.1.2 low hm hwindow harithmetic
              hexternalArithmetic h candidate
      | inr e =>
          apply measurableSet_someCandidate_of_near
          intro h candidate
          change MeasurableSet (checkerPrefixedPreimage e
            ((firstCheckerStructuralTargetFamily d m gaps gaps.1.2 low e hm
              hwindow harithmetic hwidth hexternalArithmetic).near h candidate))
          exact measurableSet_checkerPrefixedPreimage
            (firstCheckerStructuralTargetFamily_near_measurable d m gaps
              gaps.1.2 low e hm hwindow harithmetic hwidth hexternalArithmetic h
                candidate) e
  | evenColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              apply measurableSet_someCandidate_of_near
              intro h candidate
              change MeasurableSet
                ((firstStructuralTransportedFamily .evenColumns o .canonical m
                  gaps gaps.1.2 low hm hwindow harithmetic
                    hexternalArithmetic).near h candidate)
              exact firstStructuralTransportedFamily_near_measurable
                .evenColumns o .canonical m gaps gaps.1.2 low hm hwindow
                  harithmetic hexternalArithmetic h candidate
          | opposite =>
              apply measurableSet_someCandidate_of_near
              intro h candidate
              change MeasurableSet
                ((firstStructuralTransportedFamily .evenColumns o .opposite m
                  gaps gaps.1.2 low hm hwindow harithmetic
                    hexternalArithmetic).near h candidate)
              exact firstStructuralTransportedFamily_near_measurable
                .evenColumns o .opposite m gaps gaps.1.2 low hm hwindow
                  harithmetic hexternalArithmetic h candidate
  | oddColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              apply measurableSet_someCandidate_of_near
              intro h candidate
              change MeasurableSet
                ((firstStructuralTransportedFamily .oddColumns o .canonical m
                  gaps gaps.1.2 low hm hwindow harithmetic
                    hexternalArithmetic).near h candidate)
              exact firstStructuralTransportedFamily_near_measurable
                .oddColumns o .canonical m gaps gaps.1.2 low hm hwindow
                  harithmetic hexternalArithmetic h candidate
          | opposite =>
              apply measurableSet_someCandidate_of_near
              intro h candidate
              change MeasurableSet
                ((firstStructuralTransportedFamily .oddColumns o .opposite m
                  gaps gaps.1.2 low hm hwindow harithmetic
                    hexternalArithmetic).near h candidate)
              exact firstStructuralTransportedFamily_near_measurable
                .oddColumns o .opposite m gaps gaps.1.2 low hm hwindow
                  harithmetic hexternalArithmetic h candidate

theorem measurableSet_secondStructuralRowCandidateEvent
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (low : ℕ)
    (hm : 1 < m) (hwindow : Prop49WindowArithmeticAt m gaps.2)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (row : TilingEndpointSourceRow t) :
    MeasurableSet (secondStructuralRowCandidateEvent t m gaps low hm hwindow
      harithmetic hwidth hexternalArithmetic row) := by
  cases t with
  | checker d =>
      cases row with
      | inl o =>
          apply measurableSet_someCandidate_of_near
          intro h candidate
          change MeasurableSet
            ((secondStructuralTransportedFamily (.checker d) o .canonical m
              gaps gaps.2 low hm hwindow harithmetic
                hexternalArithmetic).near h candidate)
          exact secondStructuralTransportedFamily_near_measurable (.checker d) o
            .canonical m gaps gaps.2 low hm hwindow harithmetic
              hexternalArithmetic h candidate
      | inr e =>
          apply measurableSet_someCandidate_of_near
          intro h candidate
          change MeasurableSet (checkerPrefixedPreimage e
            ((secondCheckerStructuralTargetFamily d m gaps gaps.2 low e hm
              hwindow harithmetic hwidth hexternalArithmetic).near h candidate))
          exact measurableSet_checkerPrefixedPreimage
            (secondCheckerStructuralTargetFamily_near_measurable d m gaps
              gaps.2 low e hm hwindow harithmetic hwidth hexternalArithmetic h
                candidate) e
  | evenColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              apply measurableSet_someCandidate_of_near
              intro h candidate
              change MeasurableSet
                ((secondStructuralTransportedFamily .evenColumns o .canonical m
                  gaps gaps.2 low hm hwindow harithmetic
                    hexternalArithmetic).near h candidate)
              exact secondStructuralTransportedFamily_near_measurable
                .evenColumns o .canonical m gaps gaps.2 low hm hwindow
                  harithmetic hexternalArithmetic h candidate
          | opposite =>
              apply measurableSet_someCandidate_of_near
              intro h candidate
              change MeasurableSet
                ((secondStructuralTransportedFamily .evenColumns o .opposite m
                  gaps gaps.2 low hm hwindow harithmetic
                    hexternalArithmetic).near h candidate)
              exact secondStructuralTransportedFamily_near_measurable
                .evenColumns o .opposite m gaps gaps.2 low hm hwindow
                  harithmetic hexternalArithmetic h candidate
  | oddColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              apply measurableSet_someCandidate_of_near
              intro h candidate
              change MeasurableSet
                ((secondStructuralTransportedFamily .oddColumns o .canonical m
                  gaps gaps.2 low hm hwindow harithmetic
                    hexternalArithmetic).near h candidate)
              exact secondStructuralTransportedFamily_near_measurable
                .oddColumns o .canonical m gaps gaps.2 low hm hwindow
                  harithmetic hexternalArithmetic h candidate
          | opposite =>
              apply measurableSet_someCandidate_of_near
              intro h candidate
              change MeasurableSet
                ((secondStructuralTransportedFamily .oddColumns o .opposite m
                  gaps gaps.2 low hm hwindow harithmetic
                    hexternalArithmetic).near h candidate)
              exact secondStructuralTransportedFamily_near_measurable
                .oddColumns o .opposite m gaps gaps.2 low hm hwindow
                  harithmetic hexternalArithmetic h candidate

theorem firstStructuralRowCandidateEvent_subset_ambient
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (low : ℕ)
    (hm : 1 < m) (hwindow : Prop49WindowArithmeticAt m gaps.1.2)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (row : TilingEndpointSourceRow t) :
    firstStructuralRowCandidateEvent t m gaps low hm hwindow harithmetic
        hwidth hexternalArithmetic row ⊆
      rowAmbientCandidateEvent t m 2 gaps.1.2 low hm (by omega) hwindow
        harithmetic hwidth hexternalArithmetic row := by
  cases t with
  | checker d =>
      cases row with
      | inl o =>
          exact firstStructuralTransportedFamily_someCandidate_subset_ambient
            (.checker d) o .canonical m gaps gaps.1.2 low hm hwindow
              harithmetic hexternalArithmetic
      | inr e =>
          exact firstCheckerStructuralFamily_someCandidate_subset_complete d m
            gaps gaps.1.2 low e hm hwindow harithmetic hwidth
              hexternalArithmetic
  | evenColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              exact firstStructuralTransportedFamily_someCandidate_subset_ambient
                .evenColumns o .canonical m gaps gaps.1.2 low hm hwindow
                  harithmetic hexternalArithmetic
          | opposite =>
              exact firstStructuralTransportedFamily_someCandidate_subset_ambient
                .evenColumns o .opposite m gaps gaps.1.2 low hm hwindow
                  harithmetic hexternalArithmetic
  | oddColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              exact firstStructuralTransportedFamily_someCandidate_subset_ambient
                .oddColumns o .canonical m gaps gaps.1.2 low hm hwindow
                  harithmetic hexternalArithmetic
          | opposite =>
              exact firstStructuralTransportedFamily_someCandidate_subset_ambient
                .oddColumns o .opposite m gaps gaps.1.2 low hm hwindow
                  harithmetic hexternalArithmetic

theorem secondStructuralRowCandidateEvent_subset_ambient
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (low : ℕ)
    (hm : 1 < m) (hwindow : Prop49WindowArithmeticAt m gaps.2)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (row : TilingEndpointSourceRow t) :
    secondStructuralRowCandidateEvent t m gaps low hm hwindow harithmetic
        hwidth hexternalArithmetic row ⊆
      rowAmbientCandidateEvent t m 3 gaps.2 low hm (by omega) hwindow
        harithmetic hwidth hexternalArithmetic row := by
  cases t with
  | checker d =>
      cases row with
      | inl o =>
          exact secondStructuralTransportedFamily_someCandidate_subset_ambient
            (.checker d) o .canonical m gaps gaps.2 low hm hwindow harithmetic
              hexternalArithmetic
      | inr e =>
          exact secondCheckerStructuralFamily_someCandidate_subset_complete d m
            gaps gaps.2 low e hm hwindow harithmetic hwidth hexternalArithmetic
  | evenColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              exact secondStructuralTransportedFamily_someCandidate_subset_ambient
                .evenColumns o .canonical m gaps gaps.2 low hm hwindow
                  harithmetic hexternalArithmetic
          | opposite =>
              exact secondStructuralTransportedFamily_someCandidate_subset_ambient
                .evenColumns o .opposite m gaps gaps.2 low hm hwindow
                  harithmetic hexternalArithmetic
  | oddColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              exact secondStructuralTransportedFamily_someCandidate_subset_ambient
                .oddColumns o .canonical m gaps gaps.2 low hm hwindow
                  harithmetic hexternalArithmetic
          | opposite =>
              exact secondStructuralTransportedFamily_someCandidate_subset_ambient
                .oddColumns o .opposite m gaps gaps.2 low hm hwindow
                  harithmetic hexternalArithmetic

theorem ambient_inter_firstStructural_inter_valid_subset_rowCandidate
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (low : ℕ)
    (hm : 1 < m) (hwindow : Prop49WindowArithmeticAt m gaps.1.2)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (row : TilingEndpointSourceRow t) :
    (rowAmbientCandidateEvent t m 2 gaps.1.2 low hm (by omega) hwindow
        harithmetic hwidth hexternalArithmetic row ∩
      firstStructuralPast t m gaps) ∩ validStepWalk ⊆
      firstStructuralRowCandidateEvent t m gaps low hm hwindow harithmetic
        hwidth hexternalArithmetic row := by
  intro s hs
  cases t with
  | checker d =>
      cases row with
      | inl o =>
          exact transportedSourceFamily_inter_firstStructuralPreimage_subset
            (.checker d) o .canonical m gaps gaps.1.2 low hm hwindow harithmetic
              hexternalArithmetic hs.1
      | inr e =>
          exact checkerComplete_inter_firstStructural_inter_valid_subset d m
            gaps gaps.1.2 low e hm hwindow harithmetic hwidth
              hexternalArithmetic hs
  | evenColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              exact transportedSourceFamily_inter_firstStructuralPreimage_subset
                .evenColumns o .canonical m gaps gaps.1.2 low hm hwindow
                  harithmetic hexternalArithmetic hs.1
          | opposite =>
              have hpre : s ∈ sourceTransportPreimage .evenColumns .opposite
                  (firstStructuralPast
                    (TargetTiling .evenColumns .opposite) m gaps) := by
                rw [firstStructuralPreimage_opposite_column .evenColumns
                  (by simp [IsColumnTiling]) m (by omega) gaps]
                exact hs.1.2
              exact transportedSourceFamily_inter_firstStructuralPreimage_subset
                .evenColumns o .opposite m gaps gaps.1.2 low hm hwindow
                  harithmetic hexternalArithmetic ⟨hs.1.1, hpre⟩
  | oddColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              exact transportedSourceFamily_inter_firstStructuralPreimage_subset
                .oddColumns o .canonical m gaps gaps.1.2 low hm hwindow
                  harithmetic hexternalArithmetic hs.1
          | opposite =>
              have hpre : s ∈ sourceTransportPreimage .oddColumns .opposite
                  (firstStructuralPast
                    (TargetTiling .oddColumns .opposite) m gaps) := by
                rw [firstStructuralPreimage_opposite_column .oddColumns
                  (by simp [IsColumnTiling]) m (by omega) gaps]
                exact hs.1.2
              exact transportedSourceFamily_inter_firstStructuralPreimage_subset
                .oddColumns o .opposite m gaps gaps.1.2 low hm hwindow
                  harithmetic hexternalArithmetic ⟨hs.1.1, hpre⟩

theorem ambient_inter_secondStructural_inter_valid_subset_rowCandidate
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (low : ℕ)
    (hm : 1 < m) (hwindow : Prop49WindowArithmeticAt m gaps.2)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (row : TilingEndpointSourceRow t) :
    (rowAmbientCandidateEvent t m 3 gaps.2 low hm (by omega) hwindow
        harithmetic hwidth hexternalArithmetic row ∩
      secondStructuralPast t m gaps) ∩ validStepWalk ⊆
      secondStructuralRowCandidateEvent t m gaps low hm hwindow harithmetic
        hwidth hexternalArithmetic row := by
  intro s hs
  cases t with
  | checker d =>
      cases row with
      | inl o =>
          exact transportedSourceFamily_inter_secondStructuralPreimage_subset
            (.checker d) o .canonical m gaps gaps.2 low hm hwindow harithmetic
              hexternalArithmetic hs.1
      | inr e =>
          exact checkerComplete_inter_secondStructural_inter_valid_subset d m
            gaps gaps.2 low e hm hwindow harithmetic hwidth
              hexternalArithmetic hs
  | evenColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              exact transportedSourceFamily_inter_secondStructuralPreimage_subset
                .evenColumns o .canonical m gaps gaps.2 low hm hwindow
                  harithmetic hexternalArithmetic hs.1
          | opposite =>
              have hpre : s ∈ sourceTransportPreimage .evenColumns .opposite
                  (secondStructuralPast
                    (TargetTiling .evenColumns .opposite) m gaps) := by
                rw [secondStructuralPreimage_opposite_column .evenColumns
                  (by simp [IsColumnTiling]) m (by omega) gaps]
                exact hs.1.2
              exact transportedSourceFamily_inter_secondStructuralPreimage_subset
                .evenColumns o .opposite m gaps gaps.2 low hm hwindow
                  harithmetic hexternalArithmetic ⟨hs.1.1, hpre⟩
  | oddColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              exact transportedSourceFamily_inter_secondStructuralPreimage_subset
                .oddColumns o .canonical m gaps gaps.2 low hm hwindow
                  harithmetic hexternalArithmetic hs.1
          | opposite =>
              have hpre : s ∈ sourceTransportPreimage .oddColumns .opposite
                  (secondStructuralPast
                    (TargetTiling .oddColumns .opposite) m gaps) := by
                rw [secondStructuralPreimage_opposite_column .oddColumns
                  (by simp [IsColumnTiling]) m (by omega) gaps]
                exact hs.1.2
              exact transportedSourceFamily_inter_secondStructuralPreimage_subset
                .oddColumns o .opposite m gaps gaps.2 low hm hwindow
                  harithmetic hexternalArithmetic ⟨hs.1.1, hpre⟩

theorem filteredSecondTransitionEvent_subset_firstStructuralPast
    (stagedCandidate₁ stagedCandidate₂ : HLOZFilteredTransitionAssembly.BranchEvent)
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) :
    filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂ t m gaps ⊆
      firstStructuralPast t m gaps := by
  intro s hs
  have hfirst := filteredSecondTransitionEvent_subset_filteredFirst
    stagedCandidate₁ stagedCandidate₂ t m gaps hs
  exact ⟨hfirst.1, fun hbad ↦ hfirst.2 (Or.inl hbad)⟩

theorem filteredThirdTransitionEvent_subset_secondStructuralPast
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ :
      HLOZFilteredTransitionAssembly.BranchEvent)
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) :
    filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ t m gaps ⊆ secondStructuralPast t m gaps := by
  intro s hs
  have hsecond := filteredThirdTransitionEvent_subset_filteredSecond
    stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ t m gaps hs
  exact ⟨hsecond.1, fun hbad ↦ hsecond.2 <|
    hbad.elim (fun h ↦ Or.inl (Or.inl h)) (fun h ↦ Or.inr (Or.inl h))⟩

/-- Every unpaid valid rank-two path enters one structural source row. -/
theorem filteredSecond_inter_payment_compl_inter_valid_subset_rows
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (low : ℕ)
    (hlow : gaps.1.2 ∈ lowGapMesh) (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m gaps.1.2)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    (filteredSecondTransitionEvent (firstRawStagedCandidate data)
        (secondRawStagedCandidate data) t m gaps \
      rawOrientedSourceThetaTotalPaymentAtRank data t 2 m) ∩ validStepWalk ⊆
      ⋃ row : TilingEndpointSourceRow t,
        firstStructuralRowCandidateEvent t m gaps low hm hwindow harithmetic
          hwidth hexternalArithmetic row := by
  rintro s ⟨⟨hfiltered, hunpaid⟩, hvalid⟩
  have hpreliminary : s ∈ secondRawCandidatePreliminary t m gaps :=
    ⟨hfiltered.1, fun hfailure ↦ hfiltered.2 (Or.inr (Or.inl hfailure))⟩
  have hprofile := secondRawCandidatePreliminary_unpaid_profile data t m gaps s
    ⟨hpreliminary, hunpaid⟩
  have hnarrow := secondRawCandidatePreliminary_narrowCandidateProfile t m gaps
    s hm hlow hpreliminary
  rcases Set.mem_iUnion.mp
      (mem_iUnion_rowAmbientCandidateEvent_of_unpaid gaps.1.2 low hm (by omega)
        (by omega) hlow hwindow harithmetic hwidth hexternalArithmetic hprofile
          hnarrow) with ⟨row, hrow⟩
  apply Set.mem_iUnion_of_mem row
  have hstruct := filteredSecondTransitionEvent_subset_firstStructuralPast
    (firstRawStagedCandidate data) (secondRawStagedCandidate data) t m gaps
      hfiltered
  cases t with
  | checker d =>
      cases row with
      | inl o =>
          exact transportedSourceFamily_inter_firstStructuralPreimage_subset
            (.checker d) o .canonical m gaps gaps.1.2 low hm hwindow harithmetic
              hexternalArithmetic ⟨hrow, hstruct⟩
      | inr e =>
          exact checkerComplete_inter_firstStructural_inter_valid_subset d m
            gaps gaps.1.2 low e hm hwindow harithmetic hwidth hexternalArithmetic
              ⟨⟨hrow, hstruct⟩, hvalid⟩
  | evenColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              exact transportedSourceFamily_inter_firstStructuralPreimage_subset
                .evenColumns o .canonical m gaps gaps.1.2 low hm hwindow
                  harithmetic
                  hexternalArithmetic ⟨hrow, hstruct⟩
          | opposite =>
              have hpre : s ∈ sourceTransportPreimage .evenColumns .opposite
                  (firstStructuralPast
                    (TargetTiling .evenColumns .opposite) m gaps) := by
                rw [firstStructuralPreimage_opposite_column .evenColumns
                  (by simp [IsColumnTiling]) m (by omega) gaps]
                exact hstruct
              exact transportedSourceFamily_inter_firstStructuralPreimage_subset
                .evenColumns o .opposite m gaps gaps.1.2 low hm hwindow
                  harithmetic
                  hexternalArithmetic ⟨hrow, hpre⟩
  | oddColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              exact transportedSourceFamily_inter_firstStructuralPreimage_subset
                .oddColumns o .canonical m gaps gaps.1.2 low hm hwindow
                  harithmetic
                  hexternalArithmetic ⟨hrow, hstruct⟩
          | opposite =>
              have hpre : s ∈ sourceTransportPreimage .oddColumns .opposite
                  (firstStructuralPast
                    (TargetTiling .oddColumns .opposite) m gaps) := by
                rw [firstStructuralPreimage_opposite_column .oddColumns
                  (by simp [IsColumnTiling]) m (by omega) gaps]
                exact hstruct
              exact transportedSourceFamily_inter_firstStructuralPreimage_subset
                .oddColumns o .opposite m gaps gaps.1.2 low hm hwindow
                  harithmetic
                  hexternalArithmetic ⟨hrow, hpre⟩

/-- Every unpaid valid rank-three path enters one structural source row. -/
theorem filteredThird_inter_payment_compl_inter_valid_subset_rows
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (low : ℕ)
    (hlow : gaps.2 ∈ lowGapMesh) (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m gaps.2)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    (filteredThirdTransitionEvent (firstRawStagedCandidate data)
        (secondRawStagedCandidate data) (thirdRawStagedCandidate data)
        t m gaps \
      rawOrientedSourceThetaTotalPaymentAtRank data t 3 m) ∩ validStepWalk ⊆
      ⋃ row : TilingEndpointSourceRow t,
        secondStructuralRowCandidateEvent t m gaps low hm hwindow harithmetic
          hwidth hexternalArithmetic row := by
  rintro s ⟨⟨hfiltered, hunpaid⟩, hvalid⟩
  have hpreliminary : s ∈ thirdRawCandidatePreliminary t m gaps :=
    ⟨hfiltered.1.1, fun hfailure ↦
      hfiltered.2 (Or.inr (Or.inl hfailure))⟩
  have hprofile := thirdRawCandidatePreliminary_unpaid_profile data t m gaps s
    ⟨hpreliminary, hunpaid⟩
  have hnarrow := thirdRawCandidatePreliminary_narrowCandidateProfile t m gaps
    s hm hlow hpreliminary
  rcases Set.mem_iUnion.mp
      (mem_iUnion_rowAmbientCandidateEvent_of_unpaid gaps.2 low hm (by omega)
        (by omega) hlow hwindow harithmetic hwidth hexternalArithmetic hprofile
          hnarrow) with ⟨row, hrow⟩
  apply Set.mem_iUnion_of_mem row
  have hstruct := filteredThirdTransitionEvent_subset_secondStructuralPast
    (firstRawStagedCandidate data) (secondRawStagedCandidate data)
      (thirdRawStagedCandidate data) t m gaps hfiltered
  cases t with
  | checker d =>
      cases row with
      | inl o =>
          exact transportedSourceFamily_inter_secondStructuralPreimage_subset
            (.checker d) o .canonical m gaps gaps.2 low hm hwindow harithmetic
              hexternalArithmetic ⟨hrow, hstruct⟩
      | inr e =>
          exact checkerComplete_inter_secondStructural_inter_valid_subset d m
            gaps gaps.2 low e hm hwindow harithmetic hwidth hexternalArithmetic
              ⟨⟨hrow, hstruct⟩, hvalid⟩
  | evenColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              exact transportedSourceFamily_inter_secondStructuralPreimage_subset
                .evenColumns o .canonical m gaps gaps.2 low hm hwindow
                  harithmetic
                  hexternalArithmetic ⟨hrow, hstruct⟩
          | opposite =>
              have hpre : s ∈ sourceTransportPreimage .evenColumns .opposite
                  (secondStructuralPast
                    (TargetTiling .evenColumns .opposite) m gaps) := by
                rw [secondStructuralPreimage_opposite_column .evenColumns
                  (by simp [IsColumnTiling]) m (by omega) gaps]
                exact hstruct
              exact transportedSourceFamily_inter_secondStructuralPreimage_subset
                .evenColumns o .opposite m gaps gaps.2 low hm hwindow harithmetic
                  hexternalArithmetic ⟨hrow, hpre⟩
  | oddColumns =>
      cases row with
      | mk o cls =>
          cases cls with
          | canonical =>
              exact transportedSourceFamily_inter_secondStructuralPreimage_subset
                .oddColumns o .canonical m gaps gaps.2 low hm hwindow harithmetic
                  hexternalArithmetic ⟨hrow, hstruct⟩
          | opposite =>
              have hpre : s ∈ sourceTransportPreimage .oddColumns .opposite
                  (secondStructuralPast
                    (TargetTiling .oddColumns .opposite) m gaps) := by
                rw [secondStructuralPreimage_opposite_column .oddColumns
                  (by simp [IsColumnTiling]) m (by omega) gaps]
                exact hstruct
              exact transportedSourceFamily_inter_secondStructuralPreimage_subset
                .oddColumns o .opposite m gaps gaps.2 low hm hwindow harithmetic
                  hexternalArithmetic ⟨hrow, hpre⟩

end

end Erdos1165.HLOZStructuralPastTilingEndpointSourceRows
