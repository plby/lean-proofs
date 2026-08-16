import Mathlib

namespace Erdos205

open Real Filter Asymptotics

def Omega (n : ℕ) : ℕ := n.primeFactorsList.length
noncomputable def pntRate (n : ℕ) : ℝ :=
  Real.sqrt (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))
def is_counterexample (c : ℝ) (n : ℕ) : Prop :=
  ∀ k, 2^k ≤ n → (Omega (n - 2^k) : ℝ) ≥ c * pntRate n
end Erdos205

attribute [local instance] Classical.propDecidable

open Real Filter Asymptotics

namespace Erdos205

theorem infinitely_many_counterexamples :
    ∃ c : ℝ, 0 < c ∧ {n : ℕ | is_counterexample c n}.Infinite := by
  sorry

end Erdos205
