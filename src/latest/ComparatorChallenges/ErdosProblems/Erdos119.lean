/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Finset

namespace Erdos119

/-
Here we use 0-indexing for generality and convenience, while in the original problem
formulation 1-indexing was used. This change does not affect the meaning of the problem.
In the description of the problem below we remain faithful to the original one.
-/

/-- Let $z_i$ be an infinite sequence of complex numbers such that $|z_i| = 1$ for all $i \geq 1$.
For $n \geq 1$ let $p_n(z) = \prod_{i \leq n} (z - z_i)$. -/
noncomputable def p (z : ℕ → ℂ) (n : ℕ) : ℂ → ℂ :=
  fun w => ∏ i ∈ range n, (w - z i)

/-- Let $M_n = \max_{|z| = 1} |p_n(z)|$. -/
noncomputable def M (z : ℕ → ℂ) (n : ℕ) : ℝ :=
  sSup {‖p z n w‖ | (w : ℂ) (_ : ‖w‖ = 1)}

theorem erdos_119.parts.iii_quantitative :
    ∀ (z : ℕ → ℂ) (_ : ∀ i : ℕ, ‖z i‖ = 1),
      ∃ C > 0, ∀ᶠ n : ℕ in atTop,
        C * ((n : ℝ) ^ (5 / 4 : ℝ) /
          Real.sqrt (Real.log (n : ℝ))) <
            ∑ k ∈ range n, M z k := by
  sorry

theorem erdos_119 :
    ∀ (z : ℕ → ℂ) (_ : ∀ i : ℕ, ‖z i‖ = 1),
      ∃ (c : ℝ) (_ : c > 0), ∀ᶠ n in atTop,
        ∑ k ∈ range n, M z k > n ^ (1 + c) := by
  sorry

theorem erdos_119.parts.ii :
    ∀ (z : ℕ → ℂ) (_ : ∀ i : ℕ, ‖z i‖ = 1),
      ∃ (c : ℝ) (_ : c > 0), Infinite {n : ℕ | M z n > n ^ c} := by
  sorry

theorem erdos_119.parts.i :
    ∀ (z : ℕ → ℂ) (_ : ∀ i : ℕ, ‖z i‖ = 1),
      atTop.limsup (fun n => (M z n : EReal)) = ⊤ := by
  sorry
