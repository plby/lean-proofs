/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos205

def Omega (n : ℕ) : ℕ := n.primeFactorsList.length
noncomputable def pntRate (n : ℕ) : ℝ :=
  Real.sqrt (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))
def is_counterexample (c : ℝ) (n : ℕ) : Prop :=
  ∀ k, 2^k ≤ n → (Omega (n - 2^k) : ℝ) ≥ c * pntRate n

theorem not_erdos_205 :
    ∃ c : ℝ, 0 < c ∧ {n : ℕ | is_counterexample c n}.Infinite := by
  sorry

end Erdos205
