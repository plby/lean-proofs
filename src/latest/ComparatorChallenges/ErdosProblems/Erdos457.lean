/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos457

noncomputable def A_func (n k : ℕ) : ℕ := ∏ i ∈ Finset.Icc 1 k, (n + i)
noncomputable def F (n : ℕ) : ℕ := A_func n ⌊Real.log n⌋₊

theorem thm_main :
    Set.Infinite { n : ℕ | ∀ p : ℕ, p.Prime → p ≤ 2.1 * Real.log n → p ∣ F n } := by
  sorry

theorem erdos_457 : ∃ ε > (0 : ℝ),
    { n : ℕ | ∀ (p : ℕ), p ≤ (2 + ε) * Real.log n → p.Prime →
      p ∣ ∏ i ∈ Finset.Icc 1 ⌊Real.log n⌋₊, (n + i) }.Infinite := by
  sorry

end Erdos457
