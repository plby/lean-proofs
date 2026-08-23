import Mathlib

namespace UnitFractions

open scoped BigOperators
open Filter Real Finset Nat
open _root_.Finset

noncomputable section

section

variable (A : Set ℕ)

variable {A}

end

open scoped Classical in
def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n
namespace Nat

end Nat

end

end UnitFractions


open UnitFractions

namespace Erdos299

open scoped Classical in
theorem not_erdos299 :
    ¬ ∃ a : ℕ → ℕ, StrictMono a ∧
      (∀ i : ℕ, 1 ≤ a i) ∧
      (∃ C : ℕ, ∀ i : ℕ, a (i + 1) - a i ≤ C) ∧
      ∀ S : Finset ℕ, rec_sum (S.image a) ≠ 1 := by
  sorry

end Erdos299
