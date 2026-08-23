/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

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


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos646

open scoped Classical in
theorem infinitely_many_even_factorial_exponents (k : ℕ) (p : Fin k → ℕ) (hp : ∀ i, (p i).Prime) (h_distinct : Function.Injective p) :
  Set.Infinite { n | ∀ i, partial_sum k p n i = 0 } := by
  sorry

end Erdos646
