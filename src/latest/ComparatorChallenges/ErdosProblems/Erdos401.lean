/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos401

noncomputable def p (j : ℕ) : ℕ := Nat.nth Nat.Prime (j - 1)
noncomputable def P (r : ℕ) : ℕ := ∏ j ∈ Finset.range r, p (j + 1)
noncomputable def γ : ℝ := 9 / 70
noncomputable def ω (r : ℕ) : ℝ :=
  let q := (p (r + 1) : ℝ)
  (γ / 16) * (q - 1) / Real.log q

theorem erdos_401 (r : ℕ) (hr : r ≥ 1) :
    Set.Infinite {n : ℕ | ∃ a1 a2 : ℕ, a1 > 0 ∧ a2 > 0 ∧
      (a1 : ℝ) + a2 > n + ω r * Real.log n ∧
      (Nat.factorial a1 * Nat.factorial a2) ∣ (Nat.factorial n * (P r)^n)} := by
  sorry

end Erdos401
