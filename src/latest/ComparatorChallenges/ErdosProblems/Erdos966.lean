import Mathlib

namespace Erdos966

open scoped Real
open scoped Nat

set_option relaxedAutoImplicit false
set_option autoImplicit false

def HasAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, d ≠ 0 ∧ ∀ i : Fin k, a + i * d ∈ A
def HasMonochromaticAP (A : Set ℕ) (k : ℕ) {r : ℕ} (c : ℕ → Fin r) : Prop :=
  ∃ a d : ℕ,
    d ≠ 0 ∧ (∀ i : Fin k, a + i * d ∈ A) ∧
      ∃ y : Fin r, ∀ i : Fin k, c (a + i * d) = y
end Erdos966


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos966

open scoped Classical in
theorem existence_of_AP_free_Ramsey_set :
    ∀ k r : ℕ,
      k ≥ 2 → r ≥ 2 →
        ∃ A : Set ℕ,
          ¬ HasAP A (k + 1) ∧ ∀ c : ℕ → Fin r, HasMonochromaticAP A k c := by
  sorry

end Erdos966
