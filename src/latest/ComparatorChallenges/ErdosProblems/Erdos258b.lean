/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos258b

def Q (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => Q a n * a (n + 1)

noncomputable def erdosTerm (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((n + 1).divisors.card : ℝ) / (Q a (n + 1) : ℝ)

noncomputable def erdosSeries (a : ℕ → ℕ) : ℝ := ∑' n, erdosTerm a n

theorem erdos_258 (a : ℕ → ℕ) (ha : ∀ n, 0 < a (n + 1))
    (ha_tendsto : Tendsto a atTop atTop) :
    Irrational (erdosSeries a) := by
  sorry

end Erdos258b
