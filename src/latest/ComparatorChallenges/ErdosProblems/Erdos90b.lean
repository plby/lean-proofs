/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped Classical

namespace Erdos

noncomputable def unitDist (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card / 2

end Erdos

namespace Erdos90b

abbrev Point := EuclideanSpace ℝ (Fin 2)

noncomputable abbrev unitDistancePairs (P : Finset Point) : ℕ :=
  Erdos.unitDist P

theorem erdos_90b :
    ∀ C : ℝ, 0 < C → ∀ N : ℕ,
      ∃ (n : ℕ) (P : Finset Point),
        N ≤ n ∧ P.card = n ∧
          (n : ℝ) ^ (1 + C / Real.log (Real.log n)) <
            (unitDistancePairs P : ℝ) := by
  sorry

end Erdos90b
