/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Monotonicity of the number of irreducible covering sets.
Informal argument: the injective extension D ↦ {2} ∪ 2D adds one modulus.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.Doubling
import ErdosProblems.Erdos1189.MaximumModulus

namespace Erdos1189

lemma irreducibleCount_le_succ (k : ℕ) : irreducibleCount k ≤ irreducibleCount (k + 1) := by
  apply Set.ncard_le_ncard_of_injOn (s := irreducibleSetsOfSize k)
    (t := irreducibleSetsOfSize (k + 1)) doublingExtension ?_ ?_
    (finite_irreducibleSetsOfSize (k + 1))
  · intro D hD
    exact ⟨hD.1.doublingExtension, (doublingExtension_card hD.1.1.1).trans
      (congrArg (· + 1) hD.2)⟩
  · intro D hD E hE hDE
    exact doublingExtension_inj hD.1.1.1 hE.1.1.1 hDE

theorem irreducibleCount_mono : Monotone irreducibleCount :=
  monotone_nat_of_le_succ irreducibleCount_le_succ

end Erdos1189
