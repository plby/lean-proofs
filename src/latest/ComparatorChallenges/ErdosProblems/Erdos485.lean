/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Polynomial

noncomputable section

namespace Erdos485

open scoped Classical in
def termCount (P : ℚ[X]) : ℕ :=
  P.support.card

end Erdos485

namespace Erdos485

open scoped Classical in
def squareTermCounts (k : ℕ) : Set ℕ :=
  {m | ∃ P : ℚ[X], termCount P = k ∧ termCount (P ^ 2) = m}

end Erdos485

namespace Erdos485

open scoped Classical in
def f (k : ℕ) : ℕ :=
  sInf (squareTermCounts k)

end Erdos485

namespace Erdos485

open scoped Classical in
theorem erdos_485 : Tendsto f atTop atTop := by
  sorry

end Erdos485

end
