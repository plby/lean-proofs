/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 518.
https://www.erdosproblems.com/forum/thread/518

Informal authors:
- Alexey Pokrovskiy
- Leo Versteegen
- Ella Williams

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos518.md
-/
import ErdosProblems.Erdos518.MainInduction
import ErdosProblems.Erdos518.NoConfiguration

/-!
# Erdős Problem 518

In every red--blue colouring of the edges of `K_n`, all vertices are covered by at most
`Nat.sqrt n` paths of one colour.  Singleton paths are allowed and the covering paths need
not be vertex-disjoint, matching the statement of the problem.
-/

open scoped SimpleGraph

namespace Erdos518

/-- The affirmative resolution of Erdős Problem 518. -/
theorem erdos518 (n : ℕ) (G : SimpleGraph (Fin n)) : Erdos518For n G := by
  apply erdos518For_of_configuration_impossible
  intro V _ C
  exact configuration_impossible C

#print axioms erdos518

end Erdos518
