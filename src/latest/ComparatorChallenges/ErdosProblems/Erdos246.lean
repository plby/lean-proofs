/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos246

def FS (A : Set ℕ) : Set ℕ :=
  {s | ∃ F : Finset ℕ, (↑F : Set ℕ) ⊆ A ∧ s = ∑ x ∈ F, x}
def IsCompleteSeq (A : Set ℕ) : Prop :=
  Set.Finite {n | n ∉ FS A}
def Gamma (a b : ℕ) : Set ℕ :=
  {x | ∃ k l : ℕ, x = a^k * b^l}

theorem erdos_246 (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (h_coprime : Nat.Coprime a b) :
  IsCompleteSeq (Gamma a b) := by
  sorry

end Erdos246
