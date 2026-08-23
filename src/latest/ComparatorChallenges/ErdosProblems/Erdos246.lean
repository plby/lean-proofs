/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos246

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

open BigOperators

def FS (A : Set ℕ) : Set ℕ :=
  {s | ∃ F : Finset ℕ, (↑F : Set ℕ) ⊆ A ∧ s = ∑ x ∈ F, x}
def IsCompleteSeq (A : Set ℕ) : Prop :=
  Set.Finite {n | n ∉ FS A}
def Gamma (a b : ℕ) : Set ℕ :=
  {x | ∃ k l : ℕ, x = a^k * b^l}
end Erdos246


open BigOperators

namespace Erdos246

open scoped Classical in
theorem erdos_246 (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (h_coprime : Nat.Coprime a b) :
  IsCompleteSeq (Gamma a b) := by
  sorry

end Erdos246
