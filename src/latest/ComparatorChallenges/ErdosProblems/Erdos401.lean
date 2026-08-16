import Mathlib

namespace Erdos401

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

attribute [local instance] Classical.propDecidable

noncomputable def p (j : ℕ) : ℕ := Nat.nth Nat.Prime (j - 1)
noncomputable def P (r : ℕ) : ℕ := ∏ j ∈ Finset.range r, p (j + 1)
noncomputable def γ : ℝ := 9 / 70
noncomputable def ω (r : ℕ) : ℝ :=
  let q := (p (r + 1) : ℝ)
  (γ / 16) * (q - 1) / Real.log q
end Erdos401

attribute [local instance] Classical.propDecidable

namespace Erdos401

theorem theorem_1 (r : ℕ) (hr : r ≥ 1) :
    Set.Infinite {n : ℕ | ∃ a1 a2 : ℕ, a1 > 0 ∧ a2 > 0 ∧
      (a1 : ℝ) + a2 > n + ω r * Real.log n ∧
      (Nat.factorial a1 * Nat.factorial a2) ∣ (Nat.factorial n * (P r)^n)} := by
  sorry

end Erdos401
