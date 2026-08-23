/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos678

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.cases false
set_option maxHeartbeats 1000000
open scoped Nat


set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

open Real

open Filter

open scoped Classical in
def lcm_real (s : Finset ℕ) : ℝ := (s.lcm id : ℕ)
open Real Filter

open scoped Classical in
def lcmInterval (n k : ℕ) : ℕ := (Finset.Ioc n (n + k)).lcm id

end

end Erdos678



open scoped Classical in
theorem Erdos678.not_erdos_678_other :
    ¬ (∀ k ≥ 3,
      {(m, n) |
        n + k ≤ m ∧
          Erdos678.lcmInterval m (k + 1) < Erdos678.lcmInterval n k}.Infinite)
  := by
  sorry
open scoped Classical in
theorem Erdos678.main_theorem_expanded :
    ∀ C : ℝ, C ≥ 1 →
      ∃ K, ∀ k ≥ K, ∃ x y : ℕ,
        0 < x ∧ x < y ∧ y > x + k ∧
          Erdos678.lcm_real (Finset.Icc x (x + k - 1)) >
            C * Erdos678.lcm_real (Finset.Icc y (y + k))
  := by
  sorry
open scoped Classical in
theorem Erdos678.erdos_678 :
    ∃ K, ∀ k ≥ K,
      ∃ x y : ℕ,
        0 < x ∧ x < y ∧ y > x + k ∧
          Erdos678.lcm_real (Finset.Icc x (x + k - 1)) >
            Erdos678.lcm_real (Finset.Icc y (y + k))
  := by
  sorry
open scoped Classical in
theorem Erdos678.not_erdos_678_fc :
    ¬ (∀ᶠ k in Filter.atTop,
      {(m, n) |
        n + k ≤ m ∧
          Erdos678.lcmInterval m (k + 1) < Erdos678.lcmInterval n k}.Infinite)
  := by
  sorry
open scoped Classical in
theorem Erdos678.erdos_678_kmn_infinite :
    {(k, m, n) |
      3 ≤ k ∧ n + k ≤ m ∧
        Erdos678.lcmInterval m (k + 1) < Erdos678.lcmInterval n k}.Infinite
  := by
  sorry
