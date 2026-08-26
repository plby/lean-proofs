/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Released under the Apache 2.0 license. This file has been modified. -/
/-
Erdős Problem 183. Informal proof: Astra (internal OpenAI model).
Formalization: Astra (internal OpenAI model), OpenAI team.
Source: https://www.erdosproblems.com/forum/thread/183#post-8250
https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean
Original Lean/Mathlib version: 4.32.0. Ported to 4.33.0.
-/
import ErdosProblems.Erdos183.Proof

open Filter

namespace Erdos183

theorem erdos_183 :
    Filter.Tendsto
      (fun k : ℕ =>
        (triangleRamseyNumber k : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
      atTop atTop := by
  exact divergentRamseyRoot

#print axioms erdos_183
-- 'Erdos183.erdos_183' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos183
