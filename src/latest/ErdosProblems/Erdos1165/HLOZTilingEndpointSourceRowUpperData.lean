/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZNoLazyFiniteSourceRowUpperAssembly
import ErdosProblems.Erdos1165.HLOZTilingEndpointSourceRowProp49

/-!
# Hidden physical source-row data for the no-lazy upper assembly

This is the exact adapter from the concrete tiling-dependent endpoint rows to
the existential row carrier consumed by the final upper assembly.  It does
not add a transition estimate or a source-cover assumption.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZTilingEndpointSourceRowUpperData

open HLOZMeshCandidateFutureFactor
open HLOZNoLazyFiniteSourceRowUpperAssembly
open HLOZPathEvents HLOZPrefixedProp49CandidateWindowRatio
open HLOZProposition48Candidates
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZTilingEndpointSourceRowProp49
open LazyDecomposition ScreeningInstantiation

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Hide the physical tiling-dependent row carrier after constructing all
canonical, opposite-column, and fixed-direction checker rows. -/
noncomputable def heterogeneousFiniteRowMeshLowCoordinateData
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
    (hpast : ∀ row, ∀ i, IsMeasurableAtStopping
      (fun _ : StepPath ↦ raw.oldCreation i)
      (trajectory ⁻¹' (raw.pastPiece i ∩
        rowCandidateEvent t m k a low previous hprevious hm hk hwindow
          harithmetic hwidth hexternalArithmetic row)))
    (next_subset : rawNext ⊆ ⋃ row : HLOZTilingEndpointSourceRows.TilingEndpointSourceRow t,
      rowCandidateEvent t m k a low previous hprevious hm hk hwindow
        harithmetic hwidth hexternalArithmetic row) :
    HeterogeneousFiniteSourceRowMeshLowCoordinateData
      (6 * prop49WindowRatioConstant) m k a previous rawNext where
  Row := HLOZTilingEndpointSourceRows.TilingEndpointSourceRow t
  data := finiteRowMeshLowCoordinateData t m k a low previous hprevious hm hk
    hwindow harithmetic hwidth hexternalArithmetic raw hpast next_subset

end

end Erdos1165.HLOZTilingEndpointSourceRowUpperData
