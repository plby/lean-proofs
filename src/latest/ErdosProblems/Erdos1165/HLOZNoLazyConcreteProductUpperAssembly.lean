/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZConcreteFullBetaProductData
import ErdosProblems.Erdos1165.HLOZNoLazyFiniteSourceRowUpperAssembly

/-!
# Upper assembly with the full-beta product fixed concretely

This removes the corrected full-beta record from the public upper interface.
Only the concrete finite-row low construction and the exact balance/source
series data remain.
-/

open Filter MeasureTheory

namespace Erdos1165.HLOZNoLazyConcreteProductUpperAssembly

open HLOZConcreteFullBetaProductData
open HLOZNoLazyFiniteSourceRowUpperAssembly
open HLOZRawFullGapProductPromotion

noncomputable section

abbrev DominoTiling := Tilings.Tiling

abbrev ConcreteProductSourceThetaSeriesData :=
  CorrectedProductSourceThetaSeriesData concreteFullBetaProductData

/-- The corrected upper theorem after internalizing the now-constructible
full-beta product record. -/
theorem simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_concreteProduct
    (hmax : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (low : ∀ t : DominoTiling,
      PositiveLevelNoLazyFiniteSourceRowMeshCreationData
        (firstRawStagedCandidate concreteFullBetaProductData)
        (secondRawStagedCandidate concreteFullBetaProductData)
        (thirdRawStagedCandidate concreteFullBetaProductData) t)
    (source : ConcreteProductSourceThetaSeriesData) :
    ∀ᵐ s ∂simpleRandomWalk,
      ∀ᶠ n in atTop, favoriteCount s n ≤ 3 :=
  simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_correctedInterfaces
    hmax concreteFullBetaProductData low source

end

end Erdos1165.HLOZNoLazyConcreteProductUpperAssembly
