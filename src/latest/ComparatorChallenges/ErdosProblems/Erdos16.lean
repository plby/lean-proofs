/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos16

open scoped Nat

def U : Set ℕ :=
  { n | Odd n ∧ ¬ ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ n = p + 2^k }

def density_zero (S : Set ℕ) : Prop :=
  ∀ m a : ℕ, m > 0 → ¬ {x | ∃ k, x = m * k + a} ⊆ S
end Erdos16

open scoped Nat
open scoped Pointwise

namespace Erdos16

open scoped Classical in
theorem ErdosProblem16 :
    ¬ ∃ m_0 a_0 : ℕ, m_0 > 0 ∧ ∃ W : Set ℕ,
      density_zero W ∧ U = { x | ∃ h, x = m_0 * h + a_0 } ∪ W := by
  sorry

end Erdos16
