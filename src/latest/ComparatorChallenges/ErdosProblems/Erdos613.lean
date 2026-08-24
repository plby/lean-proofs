/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import Std.Tactic.BVDecide.LRAT.Internal.Clause

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

end Erdos613

theorem Erdos613.PikhurkoN5.not_erdos_613 :
    ∃ (V:Type) (G : SimpleGraph V),
      G.edgeSet.ncard = 44 ∧
      ∀ (color : Sym2 V → Fin 2),
        Erdos613.hasMonoStar G color 0 5 ∨ Erdos613.hasMonoTriangle G color 1 := by
  sorry
