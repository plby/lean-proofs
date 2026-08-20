/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
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
