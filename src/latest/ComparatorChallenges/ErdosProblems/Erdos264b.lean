import Mathlib

namespace Erdos264b

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Pointwise

def IsIrrationalitySequence (a : ℕ → ℕ) : Prop := ∀ b : ℕ → ℕ, BddAbove (Set.range b) →
  0 ∉ Set.range (a + b) → 0 ∉ Set.range b → Irrational (∑' n, (1 : ℝ) / (a n + b n))
end Erdos264b


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos264b

open scoped Classical in
theorem main_theorem : ∃ b : ℕ → ℕ, (∀ k, b k ∈ ({1, 2, 3, 4, 5} : Set ℕ)) ∧ ∃ q : ℚ, (∑' k, 1 / ((2 : ℝ)^(k + 1) + (b (k + 1) : ℝ))) = (q : ℝ) := by
  sorry

end Erdos264b
namespace Erdos264b.erdos_264.parts

open scoped Classical in
theorem i : ¬IsIrrationalitySequence (2 ^ ·) := by
  sorry

end Erdos264b.erdos_264.parts
