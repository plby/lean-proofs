/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroDeltaIndexedConcreteSpec
import ErdosProblems.Erdos1165.TilingShellZeroDeltaIndexedExactCountScreen

/-!
# Concrete rank-union payment for the exact shell-zero source event

The literal actual-increment stopped-coordinate constructor is instantiated
at every exact source count above `sourceCut`.  This theorem concerns only
the `D_eta`-good, oriented-Theta-empty source event; it makes no coverage
claim for either restricted-Theta failure window.
-/

open MeasureTheory
open scoped ENNReal

namespace Erdos1165.TilingShellZeroConcreteDeltaIndexedSourceBound

open HLOZProposition48Candidates HLOZShellZeroExternalWindow
open HLOZShellZeroRankUnionCentralTail HLOZShellZeroReplacementWindows
open LazyDecomposition TilingOrientedShellZeroSourcePartition
open TilingShellZeroDeltaIndexedConcreteSpec
open TilingShellZeroDeltaIndexedExactCountScreen

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Premise-minimal concrete source-event bound at an arbitrary oriented
cut.  The `m > 1` fact needed by the physical reconstruction is already a
consequence of the shell-window arithmetic package. -/
theorem simpleRandomWalk_orientedShellZeroSourceEvent_le_rankUnionTail
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh sourceCut : ℕ)
    (hk : 0 < k) (hlow : low < m)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternal : ShellZeroExternalWindowArithmeticAt m externalLow externalHigh) :
    simpleRandomWalk
        (orientedShellZeroSourceEvent t o m k (shellWidth48 m) low
          externalLow externalHigh sourceCut) ≤
      centralReplacementRankUnionTailCost shellZeroLocalRatioConstant
        sourceCut := by
  have hm : 1 < m := by
    rcases harithmetic with ⟨hw, hwm, _⟩
    omega
  apply simpleRandomWalk_orientedShellZeroSourceEvent_le_of_deltaIndexedSpecAtCut
  intro n eta
  exact literalShellZeroDeltaIndexedStoppedCoordinateSpec eta hm hk hlow
    (by omega) harithmetic hexternal

end

end Erdos1165.TilingShellZeroConcreteDeltaIndexedSourceBound
