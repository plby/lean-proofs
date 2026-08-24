/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset

namespace Erdos904

namespace SimpleGraph

section

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (l : List V)

variable (V) in
abbrev n : ℕ := Fintype.card V

section TuranNumber

abbrev turanNumber (n r : ℕ) : ℕ := #(_root_.SimpleGraph.turanGraph n r).edgeFinset
end TuranNumber

end

theorem erdos_904 {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {r : ℕ}
    (hr : r ∈ Set.Icc 1 (n V))
    (hm : turanNumber (n V) r ≤ #G.edgeFinset) :
    ∃ s, G.IsNClique r s ∧ 2 * r * #G.edgeFinset ≤ n V * ∑ v ∈ s, G.degree v := by
  sorry

end SimpleGraph

end Erdos904
