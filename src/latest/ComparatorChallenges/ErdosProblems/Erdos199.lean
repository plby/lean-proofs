import Mathlib.Data.Real.Basic

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

open scoped Real
open scoped Nat

namespace Erdos199

def IsThreeTermAP (a b c : ℝ) : Prop :=
  a + c = 2 * b ∧ a ≠ c
def IsInfiniteAP (S : Set ℝ) : Prop :=
  ∃ a b : ℝ, b ≠ 0 ∧ S = {x | ∃ n : ℕ, x = a + n * b}
def Conjecture : Prop :=
  ∀ A : Set ℝ, (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ¬ IsThreeTermAP a b c) →
    (∃ S : Set ℝ, IsInfiniteAP S ∧ S ⊆ (Set.univ \ A))
end Erdos199

attribute [local instance] Classical.propDecidable

theorem Erdos199.disproof_of_conjecture :
    Not Erdos199.Conjecture
  := by
  sorry
