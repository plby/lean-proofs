/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos57

def HasCycleLength {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ v, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = n

def IsOddCycleLength {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  Odd n ∧ HasCycleLength G n

noncomputable def oddCycleReciprocal {V : Type*} (G : SimpleGraph V) (n : ℕ) : ℝ :=
  by
    classical
    exact if IsOddCycleLength G n then (n : ℝ)⁻¹ else 0

theorem erdos_57 {V : Type*} (G : SimpleGraph V)
    (hχ : G.chromaticNumber = ⊤) :
    ¬Summable (oddCycleReciprocal G) := by
  sorry

end Erdos57
