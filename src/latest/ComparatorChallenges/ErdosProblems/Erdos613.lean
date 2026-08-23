/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import Std.Tactic.BVDecide.LRAT.Internal.Clause

open scoped BigOperators

namespace Erdos613

def hasMonoStar {V : Type*} (G : SimpleGraph V) (color : Sym2 V → Fin 2)
    (col : Fin 2) (k : ℕ) : Prop :=
  ∃ (x : V) (S : Finset V),
    S.card = k ∧
    x ∉ S ∧
    ∀ ⦃y : V⦄, y ∈ S → G.Adj x y ∧ color (s(x, y)) = col

def hasMonoTriangle {V : Type*} (G : SimpleGraph V) (color : Sym2 V → Fin 2)
    (col : Fin 2) : Prop :=
  ∃ a b c : V,
    G.Adj a b ∧ G.Adj b c ∧ G.Adj a c ∧
    color (s(a, b)) = col ∧
    color (s(b, c)) = col ∧
    color (s(a, c)) = col

def Pikhurko_n5_statement : Prop :=
  ∃ (V:Type) (G : SimpleGraph V),
    G.edgeSet.ncard = 44 ∧
    ∀ (color : Sym2 V → Fin 2),
      hasMonoStar G color 0 5 ∨ hasMonoTriangle G color 1

end Erdos613


open scoped Classical in
theorem Erdos613.PikhurkoN5.main :
    Erdos613.Pikhurko_n5_statement
  := by
  sorry
