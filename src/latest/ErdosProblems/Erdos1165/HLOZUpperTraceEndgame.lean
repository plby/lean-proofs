/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/

import ErdosProblems.Erdos1165.HLOZHighGapRouting
import ErdosProblems.Erdos1165.HLOZTraceScreenPackage
import ErdosProblems.Erdos1165.HLOZUpperEstimates

/-!
# Sound trace-screen upper endgame

This downstream module joins the exceptional-event estimates to the
trace/favorite-data product screens.  High spatial scales remain in those
transition screens.  The gap-return input concerns only the low mesh
`α ≤ κ₂`, on the complement of the late-clock event.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace Erdos1165.HLOZUpperTraceEndgame

open HLOZPathEvents HLOZUpperEstimates

/-- All deterministic coverage, finite-mesh arithmetic, recurrence, and
Borel--Cantelli steps are discharged with the sound trace partition. -/
theorem simpleRandomWalk_ae_eventually_favoriteCount_le_three
    (K : ℝ≥0)
    (package : HLOZTraceScreenPackage.AllLevelTraceScreenPackage K)
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    {c : ℝ} (hc : 0 < c) (hgap : HasGapDeficitReturnHarnack c) :
    ∀ᵐ s ∂simpleRandomWalk, ∀ᶠ n in atTop, favoriteCount s n ≤ 3 := by
  exact HLOZTraceScreenPackage.simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_package
      K package (fun t ↦ simpleRandomWalk_hlozExceptional_series_ne_top
        hProp13 hc hgap t)

end Erdos1165.HLOZUpperTraceEndgame
