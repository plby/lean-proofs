/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos147

noncomputable def polynomialGrowth (a : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ a

noncomputable def extremalGrowth {W : Type*} (H : SimpleGraph W) (n : ℕ) : ℝ :=
  SimpleGraph.extremalNumber n H

def HasConjecturedLowerBound {W : Type*} (H : SimpleGraph W) (r : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    (polynomialGrowth (2 - 1 / ((r : ℝ) - 1) + ε)) =O[atTop] extremalGrowth H

theorem not_erdos_147 :
    ¬ (∀ (W : Type) [Fintype W] [Nonempty W]
      (H : SimpleGraph W) [DecidableRel H.Adj] (r : ℕ),
        H.IsBipartite → H.minDegree = r → HasConjecturedLowerBound H r) := by
  sorry

end Erdos147
