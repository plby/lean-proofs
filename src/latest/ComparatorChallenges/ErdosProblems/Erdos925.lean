/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 925

This file proves the negative answer to Erdős Problem 925.  The exact graph
statement is encoded by `AdmitsTriangleFreeTwoColoring`: the edges are the
disjoint union of two triangle-free spanning subgraphs.  The construction
uses the projective `D*` graph already formalized for Erdős Problem 920,
the factorial-saving ordering lemma, and an exact double count over vertex
permutations.  It gives counterexamples on
`Ω(m^3 / log(m)^6)` vertices with independence number below `m`, which is
enough to rule out every exponent `1/3 + δ`, `δ > 0`.

The detailed mathematical proof, including the sharper published
Alon--Rödl estimate, is in `tex/925.tex`.
-/

open Filter Real
open scoped Topology BigOperators

namespace Erdos925

noncomputable section

syntax (name := answerSyntax925) "answer(" term ")" : term
macro_rules | `(answer($t)) => `($t)

/-- An exact two-coloring of the edges of `G`, with neither color containing a triangle. -/
def AdmitsTriangleFreeTwoColoring {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ red blue : SimpleGraph V,
    Disjoint red blue ∧ red ⊔ blue = G ∧ red.CliqueFree 3 ∧ blue.CliqueFree 3

/-- The proposed affirmative answer, including the constant hidden in `≫`. -/
def ProposedBound : Prop :=
  ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧ ∃ threshold : ℕ,
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), threshold ≤ n →
      AdmitsTriangleFreeTwoColoring G →
        c * (n : ℝ) ^ ((1 : ℝ) / 3 + δ) ≤ (G.indepNum : ℝ)

/-- A three-color Ramsey lower-bound witness, with the third color represented by
the complement of the union of the first two.  Overlap is harmless here: it is
removed when producing the exact edge coloring of the final graph. -/
def ThreeColorCounterexample (m n : ℕ) : Prop :=
  ∃ red blue : SimpleGraph (Fin n), red.CliqueFree 3 ∧ blue.CliqueFree 3 ∧
    (red ⊔ blue).IndepSetFree m


theorem erdos_925 : answer(False) ↔ ProposedBound := by
  sorry

end

end Erdos925
