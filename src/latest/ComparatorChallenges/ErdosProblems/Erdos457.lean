import Mathlib

namespace Erdos457

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable def A_func (n k : ℕ) : ℕ := ∏ i ∈ Finset.Icc 1 k, (n + i)
noncomputable def F (n : ℕ) : ℕ := A_func n ⌊Real.log n⌋₊
end Erdos457



open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos457

open scoped Classical in
theorem thm_main :
    Set.Infinite { n : ℕ | ∀ p : ℕ, p.Prime → p ≤ 2.1 * Real.log n → p ∣ F n } := by
  sorry


open scoped Classical in
theorem erdos_457 : ∃ ε > (0 : ℝ),
    { n : ℕ | ∀ (p : ℕ), p ≤ (2 + ε) * Real.log n → p.Prime →
      p ∣ ∏ i ∈ Finset.Icc 1 ⌊Real.log n⌋₊, (n + i) }.Infinite := by
  sorry

end Erdos457
