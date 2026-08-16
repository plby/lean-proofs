import Mathlib

namespace Erdos905

open SimpleGraph

namespace ErdosProblems.P905

variable {V : Type*} [Fintype V]

noncomputable def triangleDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V) : ℕ :=
  Sym2.lift
    ⟨fun u v => Fintype.card (G.commonNeighbors u v),
     fun u v => by simp [G.commonNeighbors_symm]⟩ e
end ErdosProblems.P905

end Erdos905

attribute [local instance] Classical.propDecidable


open SimpleGraph

namespace Erdos905.ErdosProblems.P905

theorem erdos_905 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : Fintype.card V ^ 2 / 4 < G.edgeFinset.card) :
    ∃ e ∈ G.edgeFinset, Fintype.card V / 6 ≤ triangleDegree G e := by
  sorry

end Erdos905.ErdosProblems.P905
