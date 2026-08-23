/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Set Filter

namespace Erdos894

/-- A sequence of positive natural numbers is lacunary if its consecutive
terms grow by a fixed real factor strictly larger than one. -/
def IsLacunary (n : ℕ → ℕ) : Prop :=
  (∀ k, 0 < n k) ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ k, (1 + ε) * (n k : ℝ) ≤ n (k + 1)

/-- The exact finite-colouring conclusion in Erdős Problem 894. -/
def HasAvoidingColoring (n : ℕ → ℕ) : Prop :=
  ∃ C : ℕ, ∃ color : ℕ → Fin C,
    ∀ a b : ℕ, a - b ∈ Set.range n → color a ≠ color b

/-! ## A separated rotation for a sequence with ratio at least four -/

/-- Integer indices of recursively nested middle-half intervals. -/
private noncomputable def intervalIndex (n : ℕ → ℕ) : ℕ → ℤ
  | 0 => 0
  | k + 1 =>
      ⌊(n (k + 1) : ℝ) *
          (((intervalIndex n k : ℤ) : ℝ) + 1 / 4) / (n k : ℝ)⌋ + 1

private noncomputable def lowerEndpoint (n : ℕ → ℕ) (k : ℕ) : ℝ :=
  (((intervalIndex n k : ℤ) : ℝ) + 1 / 4) / (n k : ℝ)

private noncomputable def upperEndpoint (n : ℕ → ℕ) (k : ℕ) : ℝ :=
  (((intervalIndex n k : ℤ) : ℝ) + 3 / 4) / (n k : ℝ)

theorem erdos_894 {n : ℕ → ℕ} (hn : IsLacunary n) :
    HasAvoidingColoring n := by
  sorry

end Erdos894
