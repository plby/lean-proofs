import Mathlib

open scoped Classical

namespace Erdos

noncomputable def unitDist (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card / 2

end Erdos

namespace Erdos92

abbrev Point := EuclideanSpace ℝ (Fin 2)

noncomputable abbrev unitDistancePairs (P : Finset Point) : ℕ :=
  Erdos.unitDist P

def UnitDistanceUpperBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ P : Finset Point, P.card = n →
      (unitDistancePairs P : ℝ) ≤
        (n : ℝ) ^ (1 + C / Real.log (Real.log n))

theorem erdos_92 : ¬ UnitDistanceUpperBound := by
  sorry

end Erdos92
