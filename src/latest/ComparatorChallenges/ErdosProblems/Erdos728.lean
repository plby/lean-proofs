import Mathlib

namespace Erdos728

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.unusedSimpArgs false

namespace Erdos728b

open Real

open scoped Nat Topology


open scoped Classical in
def good_triples (C ε : ℝ) : Set (ℕ × ℕ × ℕ) :=
  { t | let (a, b, n) := t; ε * n ≤ a ∧ a ≤ (1 - ε) * n ∧ ε * n ≤ b ∧ b ≤ (1 - ε) * n ∧
        Nat.factorial a * Nat.factorial b ∣ Nat.factorial n * Nat.factorial (a + b - n) ∧
        (a + b : ℝ) > n + C * Real.log n }
end Erdos728b

end Erdos728


open Real
open scoped Nat Topology

namespace Erdos728.Erdos728b

open scoped Classical in
theorem erdos_728 (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) (hε_small : ε < 1 / 2) :
    (good_triples C ε).Infinite := by
  sorry


open scoped Classical in
theorem erdos_728_fc :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ C > (0 : ℝ), ∀ C' > C,
      ∃ a b n : ℕ,
        0 < n ∧
        ε * n < a ∧
        ε * n < b ∧
        a ! * b ! ∣ n ! * (a + b - n)! ∧
        a + b > n + C * log n ∧
        a + b < n + C' * log n := by
  sorry

end Erdos728.Erdos728b
