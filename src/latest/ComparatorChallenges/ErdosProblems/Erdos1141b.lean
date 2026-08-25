/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Nat

namespace Erdos1141b

def Pa (a n : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → Nat.Coprime k n → a * k ^ 2 < n → Nat.Prime (n - a * k ^ 2)

def Erdos1141Prop (n : ℕ) : Prop :=
  ∀ k, k ^ 2 < n → Coprime n k → (n - k ^ 2).Prime

theorem erdos_1141_variant : Set.Finite {n : ℕ | Pa 1 n} := by
  sorry

theorem not_erdos_1141 :
    ¬ Infinite { n | Erdos1141Prop n } := by
  sorry

end Erdos1141b
