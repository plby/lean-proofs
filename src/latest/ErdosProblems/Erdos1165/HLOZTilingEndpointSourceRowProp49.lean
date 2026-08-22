/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZCheckerOriginSafeDistinguishedProp49Family
import ErdosProblems.Erdos1165.HLOZFiniteSourceRowMeshLowTransition
import ErdosProblems.Erdos1165.HLOZStoppedCandidatePreviousRebase
import ErdosProblems.Erdos1165.HLOZTilingEndpointSourceRows
import ErdosProblems.Erdos1165.HLOZTransportedCanonicalProp49Row

/-!
# All physical endpoint-source rows for Proposition 4.9

Column tilings use the two orientations and two endpoint classes.  Checker
tilings instead use two canonical orientation rows and four opposite rows,
one for each physical first direction.  The latter are the literal
origin-safe fixed-direction families; they are rebased to the rankwise past
without asserting a conditional ratio on a partially cut source atom.

The final cover remains an explicit deterministic input.  It is discharged
only after the source/Theta eligibility complement has been routed into its
summable exceptional family.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZTilingEndpointSourceRowProp49

open HLOZCheckerOriginSafeProp49Family
open HLOZCheckerOriginSafeDistinguishedProp49Family
open HLOZCheckerPrefixedCylinderTransport
open HLOZCountableMeshCreationRestriction
open HLOZFiniteSourceRowMeshLowTransition
open HLOZMeshCandidateFutureFactor
open HLOZMeshCandidatePolynomialNumerics
open HLOZNoLazyInitialBudgetMixedTransitionFactors
open HLOZOrientedAllCreationStoppedCandidateFamily
open HLOZPathEvents HLOZPrefixedProp49CandidateWindowRatio
open HLOZPrefixedCanonicalSourceLowRecovery
open HLOZProposition48Candidates
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZSourceEndpointTransportTable
open HLOZStoppedCandidatePreviousRebase
open HLOZStoppedHistoryCandidateFuture
open HLOZTilingEndpointSourceRows
open HLOZTransportedCanonicalProp49Row
open HLOZThetaOneSourceShift
open LazyDecomposition ScreeningInstantiation

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The normalized target history carried by one fixed-direction checker
opposite row. -/
abbrev CheckerOriginSafeHistory
    (d : Tilings.CheckerDirection) (m k : ℕ) :=
  History (shiftedCheckerTarget d) .even m k
    (SourceSupportAt (shiftedCheckerTarget d) .even m)

/-- The literal checker-origin-safe family, rebased to a rankwise past.  The
`none` history covers histories outside the source row, while only whole
source atoms absorbed by `previous` retain candidates. -/
noncomputable def checkerOriginSafeRebasedFamily
    (d : Tilings.CheckerDirection) (e : Direction)
    (m k : ℕ) (a : GapScale) (low : ℕ)
    (previous : Set WalkPath) (hprevious : MeasurableSet previous)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    StoppedHistoryCandidateFamily
      (Option (CheckerOriginSafeHistory d m k)) Point previous
      (initialBudget48 m)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) :=
  rebaseToPrevious
    (checkerCompleteOriginSafeFamily
      (t := shiftedCheckerTarget d) (o := .even) a low e hm hk hwindow
        harithmetic hwidth hexternalArithmetic)
    previous hprevious

/-- The complete candidate event in a rebased physical checker row is
measurable. -/
theorem measurableSet_checkerOriginSafeRebasedFamily
    (d : Tilings.CheckerDirection) (e : Direction)
    (m k : ℕ) (a : GapScale) (low : ℕ)
    (previous : Set WalkPath) (hprevious : MeasurableSet previous)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    MeasurableSet
      (checkerOriginSafeRebasedFamily d e m k a low previous hprevious hm hk
        hwindow harithmetic hwidth hexternalArithmetic).someCandidate := by
  exact StoppedHistoryCandidateFamily.measurableSet_someCandidate_rebaseToPrevious
    (checkerCompleteOriginSafeFamily
      (t := shiftedCheckerTarget d) (o := .even) a low e hm hk hwindow
        harithmetic hwidth hexternalArithmetic)
    previous hprevious
    (fun h x ↦ by
      change MeasurableSet (checkerPrefixedPreimage e
        ((completeOriginSafeTargetFamily
          (t := shiftedCheckerTarget d) (o := .even) a low e hm hk hwindow
            harithmetic hwidth hexternalArithmetic).near h x))
      exact measurableSet_checkerPrefixedPreimage
        (completeOriginSafeTargetFamily_near_measurable
          (t := shiftedCheckerTarget d) (o := .even) a low e hm hk hwindow
            harithmetic hwidth hexternalArithmetic h x) e)

/-- Valid candidates in the physical checker row avoid the checker-origin
exception.  This is the deterministic paid-exception routing used by the
final source cover. -/
theorem checkerOriginSafeRebasedCandidate_inter_valid_subset_exception_compl
    (d : Tilings.CheckerDirection) (e : Direction)
    (m k w : ℕ) (a : GapScale) (low : ℕ)
    (previous : Set WalkPath) (hprevious : MeasurableSet previous)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    (checkerOriginSafeRebasedFamily d e m k a low previous hprevious hm hk
        hwindow harithmetic hwidth hexternalArithmetic).someCandidate ∩
        VariableStoppedTracePartition.validStepWalk ⊆
      (checkerOriginShiftExceptionEvent d m k w)ᶜ := by
  apply (inter_subset_inter_left VariableStoppedTracePartition.validStepWalk
    (StoppedHistoryCandidateFamily.someCandidate_rebaseToPrevious_subset_oldPrevious
      (checkerCompleteOriginSafeFamily
        (t := shiftedCheckerTarget d) (o := .even) a low e hm hk hwindow
          harithmetic hwidth hexternalArithmetic)
      previous hprevious)).trans
  exact checkerOriginSafePrevious_inter_valid_subset_exception_compl
    d e hm hk

/-- Intersect a raw fixed-clock mesh decomposition with one rebased physical
checker row. -/
noncomputable def checkerOriginSafeMeshLowCoordinateDataOfRawCreation
    {Index : Type} [Countable Index]
    {rawPast rawNext : Set WalkPath}
    (d : Tilings.CheckerDirection) (e : Direction)
    (m k : ℕ) (a : GapScale) (low : ℕ)
    (previous : Set WalkPath) (hprevious : MeasurableSet previous)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (raw : CountableMeshCreationData Index rawPast rawNext m k a)
    (hpast : ∀ i, IsMeasurableAtStopping
      (fun _ : StepPath ↦ raw.oldCreation i)
      (trajectory ⁻¹' (raw.pastPiece i ∩
        (checkerOriginSafeRebasedFamily d e m k a low previous hprevious
          hm hk hwindow harithmetic hwidth
            hexternalArithmetic).someCandidate))) :
    FirstStripMeshLowCoordinateData prop49WindowRatioConstant m k a previous
      (rawNext ∩
        (checkerOriginSafeRebasedFamily d e m k a low previous hprevious hm hk
          hwindow harithmetic hwidth hexternalArithmetic).someCandidate) where
  History := Option (CheckerOriginSafeHistory d m k)
  Candidate := Point
  Index := Index
  candidateRatio := prop49CandidateRatioEnvelope
    prop49WindowRatioConstant m a
  candidate := checkerOriginSafeRebasedFamily d e m k a low previous
    hprevious hm hk hwindow harithmetic hwidth hexternalArithmetic
  creation := CountableMeshCreationData.inter raw
    (measurableSet_checkerOriginSafeRebasedFamily d e m k a low previous
      hprevious hm hk hwindow harithmetic hwidth hexternalArithmetic) hpast
  ratio_le := le_rfl

/-! ## Tiling-dependent physical rows -/

/-- Candidate union represented by one physical source row. -/
noncomputable def rowCandidateEvent
    (t : DominoTiling) (m k : ℕ) (a : GapScale) (low : ℕ)
    (previous : Set WalkPath) (hprevious : MeasurableSet previous)
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
          exact (candidateFamily (.checker d) o .canonical m k a low previous
            hprevious hm hk hwindow harithmetic
              hexternalArithmetic).someCandidate
      | inr e =>
          exact (checkerOriginSafeRebasedFamily d e m k a low previous
            hprevious hm hk hwindow harithmetic hwidth
              hexternalArithmetic).someCandidate
  | evenColumns =>
      exact fun row ↦
        (candidateFamily .evenColumns row.1 row.2 m k a low previous hprevious
          hm hk hwindow harithmetic hexternalArithmetic).someCandidate
  | oddColumns =>
      exact fun row ↦
        (candidateFamily .oddColumns row.1 row.2 m k a low previous hprevious
          hm hk hwindow harithmetic hexternalArithmetic).someCandidate

/-- Every physical source-row candidate union is measurable. -/
theorem measurableSet_rowCandidateEvent
    (t : DominoTiling) (m k : ℕ) (a : GapScale) (low : ℕ)
    (previous : Set WalkPath) (hprevious : MeasurableSet previous)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (row : TilingEndpointSourceRow t) :
    MeasurableSet (rowCandidateEvent t m k a low previous hprevious hm hk
      hwindow harithmetic hwidth hexternalArithmetic row) := by
  cases t with
  | checker d =>
      cases row with
      | inl o =>
          exact measurableSet_candidateFamily (.checker d) o .canonical
            m k a low previous hprevious hm hk hwindow harithmetic
              hexternalArithmetic
      | inr e =>
          exact measurableSet_checkerOriginSafeRebasedFamily d e m k a low
            previous hprevious hm hk hwindow harithmetic hwidth
              hexternalArithmetic
  | evenColumns =>
      exact measurableSet_candidateFamily .evenColumns row.1 row.2 m k a low
        previous hprevious hm hk hwindow harithmetic hexternalArithmetic
  | oddColumns =>
      exact measurableSet_candidateFamily .oddColumns row.1 row.2 m k a low
        previous hprevious hm hk hwindow harithmetic hexternalArithmetic

/-- One row's first-strip mesh data.  Checker-opposite rows use the
origin-safe fixed-direction family; all other rows use the normalized source
transport table. -/
noncomputable def rowMeshLowCoordinateData
    {Index : Type} [Countable Index]
    {rawPast rawNext : Set WalkPath}
    (t : DominoTiling) (m k : ℕ) (a : GapScale) (low : ℕ)
    (previous : Set WalkPath) (hprevious : MeasurableSet previous)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (raw : CountableMeshCreationData Index rawPast rawNext m k a)
    (row : TilingEndpointSourceRow t)
    (hpast : ∀ i, IsMeasurableAtStopping
      (fun _ : StepPath ↦ raw.oldCreation i)
      (trajectory ⁻¹' (raw.pastPiece i ∩
        rowCandidateEvent t m k a low previous hprevious hm hk hwindow
          harithmetic hwidth hexternalArithmetic row))) :
    FirstStripMeshLowCoordinateData prop49WindowRatioConstant m k a previous
      (rawNext ∩ rowCandidateEvent t m k a low previous hprevious hm hk
        hwindow harithmetic hwidth hexternalArithmetic row) := by
  cases t with
  | checker d =>
      cases row with
      | inl o =>
          exact meshLowCoordinateDataOfRawCreation (.checker d) o .canonical
            m k a low previous hprevious hm hk hwindow harithmetic
              hexternalArithmetic raw hpast
      | inr e =>
          exact checkerOriginSafeMeshLowCoordinateDataOfRawCreation d e m k a
            low previous hprevious hm hk hwindow harithmetic hwidth
              hexternalArithmetic raw hpast
  | evenColumns =>
      exact meshLowCoordinateDataOfRawCreation .evenColumns row.1 row.2 m k a
        low previous hprevious hm hk hwindow harithmetic hexternalArithmetic
          raw hpast
  | oddColumns =>
      exact meshLowCoordinateDataOfRawCreation .oddColumns row.1 row.2 m k a
        low previous hprevious hm hk hwindow harithmetic hexternalArithmetic
          raw hpast

@[simp] theorem rowMeshLowCoordinateData_candidateRatio
    {Index : Type} [Countable Index]
    {rawPast rawNext : Set WalkPath}
    (t : DominoTiling) (m k : ℕ) (a : GapScale) (low : ℕ)
    (previous : Set WalkPath) (hprevious : MeasurableSet previous)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (raw : CountableMeshCreationData Index rawPast rawNext m k a)
    (row : TilingEndpointSourceRow t)
    (hpast : ∀ i, IsMeasurableAtStopping
      (fun _ : StepPath ↦ raw.oldCreation i)
      (trajectory ⁻¹' (raw.pastPiece i ∩
        rowCandidateEvent t m k a low previous hprevious hm hk hwindow
          harithmetic hwidth hexternalArithmetic row))) :
    (rowMeshLowCoordinateData t m k a low previous hprevious hm hk hwindow
      harithmetic hwidth hexternalArithmetic raw row hpast).candidateRatio =
        prop49CandidateRatioEnvelope prop49WindowRatioConstant m a := by
  cases t with
  | checker _ => cases row <;> rfl
  | evenColumns => rfl
  | oddColumns => rfl

/-- Assemble every physical endpoint row around one raw fixed-clock mesh
decomposition.  The rows may overlap.  The final source/Theta module supplies
the deterministic `next_subset`; no transition probability estimate is an
input. -/
noncomputable def finiteRowMeshLowCoordinateData
    {Index : Type} [Countable Index]
    {rawPast rawNext : Set WalkPath}
    (t : DominoTiling) (m k : ℕ) (a : GapScale) (low : ℕ)
    (previous : Set WalkPath) (hprevious : MeasurableSet previous)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (raw : CountableMeshCreationData Index rawPast rawNext m k a)
    (hpast : ∀ row i, IsMeasurableAtStopping
      (fun _ : StepPath ↦ raw.oldCreation i)
      (trajectory ⁻¹' (raw.pastPiece i ∩
        rowCandidateEvent t m k a low previous hprevious hm hk hwindow
          harithmetic hwidth hexternalArithmetic row)))
    (next_subset : rawNext ⊆ ⋃ row : TilingEndpointSourceRow t,
      rowCandidateEvent t m k a low previous hprevious hm hk hwindow
        harithmetic hwidth hexternalArithmetic row) :
    FiniteSourceRowMeshLowCoordinateData (TilingEndpointSourceRow t)
      (6 * prop49WindowRatioConstant) m k a previous rawNext where
  rowNext := fun row ↦ rawNext ∩
    rowCandidateEvent t m k a low previous hprevious hm hk hwindow
      harithmetic hwidth hexternalArithmetic row
  rowNext_measurable := fun row ↦ (by
    have hraw : MeasurableSet rawNext := by
      rw [← raw.next_union]
      exact MeasurableSet.iUnion raw.next_measurable
    exact hraw.inter (measurableSet_rowCandidateEvent t m k a low previous
      hprevious hm hk hwindow harithmetic hwidth hexternalArithmetic row))
  next_subset := by
    intro s hs
    rcases Set.mem_iUnion.mp (next_subset hs) with ⟨row, hrow⟩
    exact Set.mem_iUnion_of_mem row ⟨hs, hrow⟩
  rowConstant := fun _ ↦ prop49WindowRatioConstant
  row := fun row ↦ rowMeshLowCoordinateData t m k a low previous hprevious hm
    hk hwindow harithmetic hwidth hexternalArithmetic raw row (hpast row)
  ratio_sum_le := by
    simpa only [rowMeshLowCoordinateData_candidateRatio] using
      sum_candidateRatio_le_six t m a

end

end Erdos1165.HLOZTilingEndpointSourceRowProp49
