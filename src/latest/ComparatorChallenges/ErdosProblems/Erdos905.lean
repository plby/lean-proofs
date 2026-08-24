/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos905

namespace ErdosProblems.P905

section

variable {V : Type*} [Fintype V]

noncomputable def triangleDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V) : ℕ :=
  Sym2.lift
    ⟨fun u v => Fintype.card (G.commonNeighbors u v),
     fun u v => by simp [G.commonNeighbors_symm]⟩ e
end

theorem erdos_905 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : Fintype.card V ^ 2 / 4 < G.edgeFinset.card) :
    ∃ e ∈ G.edgeFinset, Fintype.card V / 6 ≤ triangleDegree G e := by
  sorry

end ErdosProblems.P905

end Erdos905
