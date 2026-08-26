/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Released under the Apache 2.0 license. This file has been modified. -/
/-
Erdős Problem 180. Informal proof: Astra (internal OpenAI model).
Formalization: Astra (internal OpenAI model), OpenAI team.
Source: https://www.erdosproblems.com/forum/thread/180#post-8255
https://github.com/openai/ten-proofs/blob/a13547c6be4563746881d0b3b4c9fd03f72f0484/CompactnessAndDegeneracy.lean
Original Lean/Mathlib version: 4.32.0. Ported to 4.33.0.
-/
import ErdosProblems.Erdos180.Quantitative

namespace Erdos180

theorem not_erdos_180 :
    ¬ (∀ family : Finset FiniteGraph,
      family.Nonempty → (∀ forbidden ∈ family, ¬ forbidden.graph.IsAcyclic) →
        ∃ forbidden ∈ family, ∃ C : ℝ, 0 < C ∧
          ∀ᶠ n : ℕ in Filter.atTop,
            (SimpleGraph.extremalNumber n forbidden.graph : ℝ) ≤
              C * (familyExtremal family n : ℝ)) :=
  not_erdos_180_source

#print axioms not_erdos_180
-- 'Erdos180.not_erdos_180' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos180
