/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1198

attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup
  Ultrafilter.add Ultrafilter.addSemigroup

/-- A finite family of index blocks is an admissible Problem 1198 expression. -/
def Admissible (blocks : Finset (Finset ℕ)) : Prop :=
  blocks.Nonempty ∧
    (∀ S ∈ blocks, S.Nonempty) ∧
    (↑blocks : Set (Finset ℕ)).PairwiseDisjoint id

/-- The only excluded expressions are one-block, one-index expressions. -/
def Nontrivial (blocks : Finset (Finset ℕ)) : Prop :=
  ¬ ∃ i : ℕ, blocks = {{i}}

/-- The sum of products represented by a finite family of index blocks. -/
def expressionValue (a : ℕ → ℕ) (blocks : Finset (Finset ℕ)) : ℕ :=
  ∑ S ∈ blocks, ∏ i ∈ S, a i

theorem not_erdos_1198 :
    ¬ (∀ c : ℕ → Fin 2,
      ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ i, 0 < a i) ∧
        ∃ color : Fin 2,
          ∀ blocks : Finset (Finset ℕ),
            Admissible blocks → Nontrivial blocks →
              c (expressionValue a blocks) = color) := by
  sorry

end Erdos1198
