/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Polynomial

namespace Erdos485

def termCount (P : ℚ[X]) : ℕ :=
  P.support.card

def squareTermCounts (k : ℕ) : Set ℕ :=
  {m | ∃ P : ℚ[X], termCount P = k ∧ termCount (P ^ 2) = m}

noncomputable def f (k : ℕ) : ℕ :=
  sInf (squareTermCounts k)

theorem erdos_485 : Tendsto f atTop atTop := by
  sorry

end Erdos485
