/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

open SimpleGraph Filter Asymptotics

namespace Erdos765

/-- The 4-cycle over `Fin 4`, where vertices differing by 1 are adjacent. -/
def C4 : SimpleGraph (Fin 4) where
  Adj i j := j = i + 1 ∨ i = j + 1

theorem erdos_765 : (fun n ↦ (extremalNumber n C4 : ℝ)) ~[atTop] fun n ↦ n ^ (3 / 2 : ℝ) / 2 := by
  sorry

end Erdos765
