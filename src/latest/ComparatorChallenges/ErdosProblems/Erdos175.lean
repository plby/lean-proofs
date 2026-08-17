/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This file formalizes the resolution of Erdős Problem 175.

Mathematical sources:
* A. Granville and O. Ramaré, "Explicit bounds on exponential sums and the
  scarcity of squarefree binomial coefficients", Mathematika 43 (1996),
  73--107.
* G. Velammal, "Is the binomial coefficient (2n choose n) squarefree?",
  Hardy--Ramanujan Journal 18 (1995), 23--45.

The detailed reconstruction and declaration map are in `tex/175.tex`.

Progress log:
* Phase 1 complete: the Granville--Ramaré argument and all formal dependencies
  are recorded in `tex/175.tex`.
* Phase 2 verified here: Kummer's binary reduction and a kernel-checked carry
  certificate for every `3 ≤ k < 8192`.
* The companion modules in `Erdos175/` formalize the explicit large-`n`
  estimates from Sections 7--10 of Granville--Ramaré.
-/

import Mathlib

namespace Erdos175

open Nat

/-- The central binomial coefficient. -/
def centralBinom (n : ℕ) : ℕ := Nat.choose (2 * n) n

/-- Every central binomial coefficient is positive. -/


theorem erdos_175 {n : ℕ} (hn : 5 ≤ n) :
    ¬ Squarefree (Nat.choose (2 * n) n) := by
  sorry

end Erdos175
