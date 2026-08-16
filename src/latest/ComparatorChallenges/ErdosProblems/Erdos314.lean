import Mathlib

namespace Erdos314

open Finset Real MeasureTheory intervalIntegral

noncomputable section

set_option linter.style.setOption false
set_option linter.flexible false

def harmonicPartialSum (n m : ℕ) : ℝ :=
  ∑ ℓ ∈ Finset.Icc n m, (↑ℓ : ℝ)⁻¹
end
end Erdos314

attribute [local instance] Classical.propDecidable

open Finset Real MeasureTheory intervalIntegral

namespace Erdos314

theorem main_theorem (c : ℝ) (hc : c > 0) :
    ∀ N : ℕ, ∃ m n : ℕ, N ≤ n ∧
      1 ≤ harmonicPartialSum n m ∧ harmonicPartialSum n m ≤ 1 + c / (↑n) ^ 2 := by
  sorry

end Erdos314
