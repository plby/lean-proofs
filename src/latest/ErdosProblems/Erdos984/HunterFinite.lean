/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterParameters

/-!
# Exact finite interface for Hunter's recurrence argument

All geometric, blue-progression, and label-counting work has already been
proved.  The sole remaining analytic datum is that every long progression
has `hunterY D` distinct center opportunities.  This file records that datum
without adding assumptions to the public theorem, and proves the complete
finite coloring from any constructed value.
-/

namespace Erdos984

noncomputable section

structure HunterRecurrenceData (D : ℕ) where
  center : Fin (hunterM D) → UnitAddTorus (Fin D)
  theta : UnitAddTorus (Fin D)
  selected : BoundedAP (hunterN D) (hunterX D) →
    Finset (Fin (hunterM D))
  target : BoundedAP (hunterN D) (hunterX D) →
    Fin (hunterM D) → Fin (hunterK D + 1)
  card_selected : ∀ P, (selected P).card = hunterY D
  opportunities : RadialOpportunities center (hunterDelta D) theta selected target
  separated : TorusCenterThreeSeparated center (hunterRho D)
  step : ∀ d : ℕ, 0 < d → d < hunterN D →
    radialSquaredWidth (hunterDelta D) (hunterK D) <
      squaredNorm (centeredTorusLift (d • theta))

/-- Once the recurrence datum is available, all remaining estimates produce
the required finite off-diagonal coloring. -/
lemma exists_goodOffDiagonal_of_hunterRecurrenceData
    (D : ℕ) (hD : 4 ≤ D) (R : HunterRecurrenceData D) :
    ∃ color : ℕ → Bool, GoodOffDiagonal color (hunterN D) (hunterX D) := by
  apply exists_goodOffDiagonal_of_radial_opportunities
    (K := hunterK D) (Y := hunterY D)
    (two_le_hunterX D (by omega)) R.center
    (hunterDelta D) (hunterRho D) (hunterDelta_pos (by omega))
    R.theta R.selected R.target R.card_selected R.opportunities
  · apply boundedAP_radial_label_count
    · simpa using hunterY_le_M D (by omega)
    · exact hunter_radial_label_base_count D hD
  · exact (hunter_radialLower_eq_rho D).le
  · exact R.separated
  · exact hunter_four_mul_rho_lt_one (by omega)
  · exact R.step

end

end Erdos984
