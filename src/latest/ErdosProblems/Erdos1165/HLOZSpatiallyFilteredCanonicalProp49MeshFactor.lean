/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZCountableMeshCreationRestriction
import ErdosProblems.Erdos1165.HLOZSpatiallyFilteredCanonicalProp49Observability

/-!
# Mesh factors for a spatially filtered canonical source row

One source row contributes the intersection of the raw filtered transition
with its own some-candidate screen.  The raw fixed-clock creation atoms are
intersected with that screen; stopped observability is explicit and no
whole-transition containment is required.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZSpatiallyFilteredCanonicalProp49MeshFactor

open HLOZCountableMeshCreationRestriction
open HLOZMeshCandidateFutureFactor
open HLOZNoLazyInitialBudgetMixedTransitionFactors
open HLOZPathEvents HLOZPrefixedCanonicalSourceLowRecovery
open HLOZPrefixedProp49CandidateWindowRatio
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZSpatiallyFilteredCanonicalSourceProp49
open HLOZStoppedHistoryCandidateFuture
open LazyDecomposition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Intersect a raw mesh-creation decomposition with the source row's
spatially eligible candidate union and package the exact Prop. 4.9 ratio. -/
noncomputable def meshLowCoordinateDataOfRawCreation
    {Index : Type} [Countable Index]
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {rawPast rawNext previous : Set WalkPath}
    (a : GapScale) (low : ℕ)
    (hprevious : MeasurableSet previous)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (raw : CountableMeshCreationData Index rawPast rawNext m k a)
    (hpast : ∀ i, IsMeasurableAtStopping
      (fun _ : StepPath ↦ raw.oldCreation i)
      (trajectory ⁻¹' (raw.pastPiece i ∩
        (spatiallyFilteredCandidateFamily (t := t) (o := o) a low previous
          hprevious hm hk hwindow harithmetic
          hexternalArithmetic).someCandidate))) :
    FirstStripMeshLowCoordinateData prop49WindowRatioConstant m k a previous
      (rawNext ∩
        (spatiallyFilteredCandidateFamily (t := t) (o := o) a low previous
          hprevious hm hk hwindow harithmetic
          hexternalArithmetic).someCandidate) :=
  spatiallyFilteredMeshLowCoordinateData a low previous _ hprevious hm hk
    hwindow harithmetic hexternalArithmetic <|
      HLOZCountableMeshCreationRestriction.CountableMeshCreationData.inter raw
        (measurableSet_spatiallyFilteredCandidateFamily a low previous
          hprevious hm hk hwindow harithmetic hexternalArithmetic)
        hpast

end

end Erdos1165.HLOZSpatiallyFilteredCanonicalProp49MeshFactor
