import Mathlib

open Filter Polynomial

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos485

def termCount (P : ℚ[X]) : ℕ :=
  P.support.card

end Erdos485

namespace Erdos485

def squareTermCounts (k : ℕ) : Set ℕ :=
  {m | ∃ P : ℚ[X], termCount P = k ∧ termCount (P ^ 2) = m}

end Erdos485

namespace Erdos485

def f (k : ℕ) : ℕ :=
  sInf (squareTermCounts k)

end Erdos485

namespace Erdos485

theorem erdos_485 : Tendsto f atTop atTop := by
  sorry

end Erdos485

end
