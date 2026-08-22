/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZRawOrientedSourceThetaPayment
import ErdosProblems.Erdos1165.HLOZTilingEndpointSourceRowUpperData

/-!
# Payment-filtered endpoint-source row data

The literal Proposition 4.9 rows cover only the source/Theta-good part of a
raw transition.  The complementary source/Theta event is an additive,
summable payment; it must not be silently inserted into a conditional
candidate family.

This module records the exact deterministic interface.  The raw stopped
creation decomposition and every row factor are unchanged.  Only the final
event is restricted by a paid set, and the pathwise input is the honest
cover

`rawNext ⊆ payment ∪ ⋃ row, rowCandidateEvent row`.

No probability inequality or summability premise occurs here.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZPaymentFilteredTilingEndpointSourceRowData

open HLOZFiniteSourceRowMeshLowTransition
open HLOZMeshCandidateFutureFactor
open HLOZNoLazyFiniteSourceRowUpperAssembly
open HLOZPathEvents HLOZPrefixedProp49CandidateWindowRatio
open HLOZProposition48Candidates
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZTilingEndpointSourceRowProp49
open HLOZTilingEndpointSourceRowUpperData
open HLOZTilingEndpointSourceRows
open LazyDecomposition ScreeningInstantiation

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The six physical source rows give low coordinate data on the complement
of an additive payment.  Row factors retain the larger events
`rawNext ∩ rowCandidateEvent`; only their finite union is restricted to the
unpaid target. -/
noncomputable def finiteRowMeshLowCoordinateDataOutside
    {Index : Type} [Countable Index]
    {rawPast rawNext : Set WalkPath}
    (payment : Set WalkPath)
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
    (next_subset : rawNext ⊆ payment ∪
      ⋃ row : HLOZTilingEndpointSourceRows.TilingEndpointSourceRow t,
        rowCandidateEvent t m k a low previous hprevious hm hk hwindow
          harithmetic hwidth hexternalArithmetic row) :
    FiniteSourceRowMeshLowCoordinateData
      (HLOZTilingEndpointSourceRows.TilingEndpointSourceRow t)
      (6 * prop49WindowRatioConstant) m k a previous (rawNext \ payment) where
  rowNext := fun row ↦ rawNext ∩
    rowCandidateEvent t m k a low previous hprevious hm hk hwindow
      harithmetic hwidth hexternalArithmetic row
  rowNext_measurable := fun row ↦ by
    have hraw : MeasurableSet rawNext := by
      rw [← raw.next_union]
      exact MeasurableSet.iUnion raw.next_measurable
    exact hraw.inter (measurableSet_rowCandidateEvent t m k a low previous
      hprevious hm hk hwindow harithmetic hwidth hexternalArithmetic row)
  next_subset := by
    rintro s ⟨hraw, hunpaid⟩
    rcases next_subset hraw with hpaid | hrow
    · exact (hunpaid hpaid).elim
    · rcases Set.mem_iUnion.mp hrow with ⟨row, hs⟩
      exact Set.mem_iUnion_of_mem row ⟨hraw, hs⟩
  rowConstant := fun _ ↦ prop49WindowRatioConstant
  row := fun row ↦ rowMeshLowCoordinateData t m k a low previous hprevious
    hm hk hwindow harithmetic hwidth hexternalArithmetic raw row (hpast row)
  ratio_sum_le := by
    simpa only [rowMeshLowCoordinateData_candidateRatio] using
      sum_candidateRatio_le_six t m a

/-- Hide the tiling-dependent six-row carrier after removing an additive
payment from the target event. -/
noncomputable def heterogeneousFiniteRowMeshLowCoordinateDataOutside
    {Index : Type} [Countable Index]
    {rawPast rawNext : Set WalkPath}
    (payment : Set WalkPath)
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
    (next_subset : rawNext ⊆ payment ∪
      ⋃ row : HLOZTilingEndpointSourceRows.TilingEndpointSourceRow t,
        rowCandidateEvent t m k a low previous hprevious hm hk hwindow
          harithmetic hwidth hexternalArithmetic row) :
    HeterogeneousFiniteSourceRowMeshLowCoordinateData
      (6 * prop49WindowRatioConstant) m k a previous (rawNext \ payment) where
  Row := HLOZTilingEndpointSourceRows.TilingEndpointSourceRow t
  data := finiteRowMeshLowCoordinateDataOutside payment t m k a low previous
    hprevious hm hk hwindow harithmetic hwidth hexternalArithmetic raw hpast
      next_subset

end

end Erdos1165.HLOZPaymentFilteredTilingEndpointSourceRowData
