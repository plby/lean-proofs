import Mathlib

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.unusedVariables false

open scoped Real
open scoped Nat

set_option maxHeartbeats 50000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Erdos429

noncomputable instance instFintypeSetInterIccNat (B : Set ℕ) (a b : ℕ) :
    Fintype ↑(B ∩ Set.Icc a b) :=
  ((Set.finite_Icc a b).subset (by
    intro x hx
    exact hx.2)).fintype
def Admissible (B : Set ℕ) : Prop :=
  ∀ p, p.Prime → ∃ (a : ZMod p), ∀ b ∈ B, (b : ZMod p) ≠ a
end Erdos429


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos429

open scoped Classical in
theorem main_theorem (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
    ∃ B : Set ℕ, B.Infinite ∧
    (∀ N, (B ∩ Set.Icc 1 N).toFinset.card ≤ f N) ∧
    Admissible B ∧
    (∀ n : ℤ, ∃ b ∈ B, ¬ Nat.Prime (Int.toNat (b + n))) := by
  sorry

end Erdos429
