import Mathlib

namespace Erdos904

open List Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (l : List V)

variable (V) in
abbrev n : ℕ := Fintype.card V

section TuranNumber

abbrev turanNumber (n r : ℕ) : ℕ := #(_root_.SimpleGraph.turanGraph n r).edgeFinset
end TuranNumber

end SimpleGraph

end Erdos904

attribute [local instance] Classical.propDecidable


open List Finset

namespace Erdos904.SimpleGraph

theorem erdos904 {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {r : ℕ}
    (hr : r ∈ Set.Icc 1 (n V))
    (hm : turanNumber (n V) r ≤ #G.edgeFinset) :
    ∃ s, G.IsNClique r s ∧ 2 * r * #G.edgeFinset ≤ n V * ∑ v ∈ s, G.degree v := by
  sorry

end Erdos904.SimpleGraph
