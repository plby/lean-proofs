/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace UnitFractions

def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n

end UnitFractions

namespace Erdos308

def IsRepresentable (N k : ℕ) : Prop :=
  ∃ A : Finset ℕ,
    A ⊆ Finset.Icc 1 N ∧ UnitFractions.rec_sum A = (k : ℚ)

def representedPositiveIntegers (N : ℕ) : Set ℕ :=
  {k | 0 < k ∧ IsRepresentable N k}

def harmonicReal (N : ℕ) : ℝ :=
  ((harmonic N : ℚ) : ℝ)

noncomputable def harmonicFloor (N : ℕ) : ℕ :=
  ⌊harmonicReal N⌋₊

noncomputable def firstMissing (N : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ ¬ IsRepresentable N k}

theorem erdos_308 :
    ∀ᶠ N : ℕ in atTop,
      (representedPositiveIntegers N = Set.Icc 1 (harmonicFloor N - 1) ∧
        firstMissing N = harmonicFloor N) ∨
      (representedPositiveIntegers N = Set.Icc 1 (harmonicFloor N) ∧
        firstMissing N = harmonicFloor N + 1) := by
  sorry

end Erdos308
