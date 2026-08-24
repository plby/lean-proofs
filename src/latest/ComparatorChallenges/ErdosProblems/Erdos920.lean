/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Real

/-!
# Erdős Problem 920
-/

/-- `g ≫ h` means that `h` is big-O of `g` at infinity. -/
notation:50 g " ≫ " h => Asymptotics.IsBigO Filter.atTop h g

namespace Erdos920

/--
`f k n` is the maximum possible chromatic number of a graph with `n` vertices
which contains no `K_k`.
-/
noncomputable def f (k n : ℕ) : ℕ :=
  sSup {(G.chromaticNumber) | (G : SimpleGraph (Fin n)) (_ : G.CliqueFree k)}

/--
For `k ≥ 4`, `f k n` has the expected Ramsey-theoretic lower bound up to a
power of `log n`.
-/
theorem erdos_920 :
    ∀ k : ℕ, k ≥ 4 → ∃ c > 0,
      (fun n : ℕ ↦ (f k n : ℝ)) ≫
        (fun n : ℕ ↦ (n : ℝ) ^ (1 - 1 / ((k : ℝ) - 1)) / (log n) ^ c) := by
  sorry

end Erdos920
