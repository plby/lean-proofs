import Mathlib

namespace Erdos646

set_option linter.style.longLine false
set_option linter.unusedVariables false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

def partial_sum (k : ℕ) (p : Fin k → ℕ) (n : ℕ) : Fin k → ZMod 2 :=
  fun i => padicValNat (p i) (Nat.factorial n)
end Erdos646

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos646

theorem infinitely_many_even_factorial_exponents (k : ℕ) (p : Fin k → ℕ) (hp : ∀ i, (p i).Prime) (h_distinct : Function.Injective p) :
  Set.Infinite { n | ∀ i, partial_sum k p n i = 0 } := by
  sorry

end Erdos646
