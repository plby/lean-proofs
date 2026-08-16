import Mathlib

namespace Erdos370

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

noncomputable def maxPrimeFac (n : ℕ) : ℕ := sSup {p : ℕ | p.Prime ∧ p ∣ n}
end Erdos370

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos370

theorem erdos_370 :
  { n | maxPrimeFac n < √n ∧ maxPrimeFac (n + 1) < √(n + 1) }.Infinite ↔ True := by
  sorry

end Erdos370
