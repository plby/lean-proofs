/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 1198

Gregory L. Smith proved that there is a two-colouring of the positive
integers which separates finite products from sums of two ordered finite
products.  Pairing consecutive members of a hypothetical solution turns
every finite product into a nontrivial expression, so Smith's colouring
disproves the problem exactly as stated.

The mathematical reconstruction is in `tex/1198.tex`.
-/

namespace Erdos1198

open Filter
open scoped BigOperators

attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup
  Ultrafilter.add Ultrafilter.addSemigroup

/-- Ordered sums of two nonempty finite products from a stream. -/
def SP2 (x : Stream' ℕ+) : Set ℕ+ :=
  {n | ∃ F G : Finset ℕ,
    F.Nonempty ∧ G.Nonempty ∧
    (∀ i ∈ F, ∀ j ∈ G, i < j) ∧
    n = (∏ i ∈ F, x.get i) + ∏ j ∈ G, x.get j}

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

/-- The exact positive assertion asked in Erdős Problem 1198. -/
def Erdos1198Statement : Prop :=
  ∀ c : ℕ → Fin 2,
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ i, 0 < a i) ∧
      ∃ color : Fin 2,
        ∀ blocks : Finset (Finset ℕ),
          Admissible blocks → Nontrivial blocks →
            c (expressionValue a blocks) = color

private def hi (n : ℕ+) : ℕ := Nat.log 2 n
private def lo (n : ℕ+) : ℕ := padicValNat 2 n

private abbrev ValBucket := Fin 3

private def valBucket (n : ℕ+) : ValBucket :=
  if lo n = 0 then 0 else if lo n = 1 then 1 else 2

private def IsTwoPower (n : ℕ+) : Prop := (n : ℕ) = 2 ^ hi n

private def LowSide (n : ℕ+) : Prop :=
  (n : ℕ) < 2 ^ hi n + 2 ^ (hi n - lo n)

private def HighSide (n : ℕ+) : Prop :=
  2 ^ (hi n + 1) - 2 ^ (hi n - lo n) < (n : ℕ)

private abbrev SmithColor := ValBucket × Bool × Fin 2 × Bool × Bool

/-- A finite refinement of the seven dyadic cells in Smith's proof. -/
private noncomputable def smithColor (n : ℕ+) : SmithColor :=
  by
    classical
    exact
      (valBucket n, if IsTwoPower n then true else false,
        ⟨hi n % 2, Nat.mod_lt _ (by omega)⟩,
        if LowSide n then true else false, if HighSide n then true else false)

theorem erdos1198 : ¬ Erdos1198Statement := by
  sorry

end Erdos1198
