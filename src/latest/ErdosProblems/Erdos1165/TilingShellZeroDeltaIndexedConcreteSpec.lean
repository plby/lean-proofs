/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroDeltaIndexedStoppedCoordinateSpec
import ErdosProblems.Erdos1165.TilingShellZeroDeltaReplacementCapCoverage

/-!
# Concrete literal actual-increment shell coordinate specification

This closes the walk-facing constructor.  Its inputs are only the eventual
deterministic window facts and the positive source parameters; no stopped
screen, factorization, coverage, probability, or limiting statement remains
as a premise.
-/

namespace Erdos1165.TilingShellZeroDeltaIndexedConcreteSpec

open HLOZProposition48Candidates
open HLOZShellZeroCentralCount HLOZShellZeroExternalWindow
open HLOZShellZeroReplacementWindows LazyDecomposition PreStoppingFiber
open StoppedInsertion
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingShellZeroActualDeltaPartition
open TilingShellZeroDeltaGeometricBound
open TilingShellZeroDeltaIndexedStoppedCoordinateSpec
open TilingShellZeroDeltaReplacementCapCoverage
open TilingShellZeroDeltaReplacementFactorization
open TilingShellZeroExternalStaticSupportPartition
open TilingShellZeroSourceCapCoverage TilingShellZeroSourcePartition
open TilingShellZeroSourceScreenForward VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The concrete stopped-coordinate specification on every supported
oriented external-word/static-support source atom. -/
noncomputable def literalShellZeroDeltaIndexedStoppedCoordinateSpec
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total)
    (hm : 1 < m) (hk : 0 < k) (hlow : low < m) (htotal : 0 < total)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternal : ShellZeroExternalWindowArithmeticAt m externalLow externalHigh) :
    LiteralShellZeroDeltaIndexedStoppedCoordinateSpec t o m k low
      externalLow externalHigh total eta.1.1 eta.1.2 where
  coordinateCap := coordinateCap eta.1.1 m
  sourceStoppingTime := sourceStoppingTime eta.1.1 m k
  replacementStoppingTime := fun delta cap ↦
    replacementStoppingTime eta.1.1 m k cap delta
  sourceIsStoppingTime := fun cap ↦ by
    exact isFiniteStoppingTime_truncatedLevelTime m k
      (externalCoordinateCutoff eta.1.1 (coordinateCap eta.1.1 m cap))
  replacementIsStoppingTime := fun delta cap ↦ by
    exact isFiniteStoppingTime_truncatedLevelTime m (k + (delta : ℕ))
      (externalCoordinateCutoff eta.1.1 (coordinateCap eta.1.1 m cap))
  sourcePredicate := fun cap ↦ sourcePredicate t o m k low externalLow
    externalHigh total cap eta.1.1 eta.1.2
  replacementPredicate := fun delta cap ↦ replacementPredicate eta cap
    (centralReplacementUpperCount shellZeroLocalRatioConstant total) delta
  geometric_bound := geometric_bound eta hm hk hlow htotal harithmetic hexternal
  source_sound := source_cap_sound eta
  source_complete := source_complete eta
  replacement_sound := fun delta cap ↦ replacement_cap_sound eta hm hk hlow
    htotal harithmetic hexternal delta cap
  source_monotone := source_monotone eta

end

end Erdos1165.TilingShellZeroDeltaIndexedConcreteSpec
