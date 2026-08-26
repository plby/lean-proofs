import ErdosProblems.Erdos556.ThreeColourTools

/-! Renaming the three colours by a permutation. -/

namespace Erdos556

open SimpleGraph

def ThreeColouring.relabel {V : Type*} (c : ThreeColouring V) (e : Fin 3 ≃ Fin 3) :
    ThreeColouring V where
  colour u v := e.symm (c.colour u v)
  symm u v := congrArg e.symm (c.symm u v)

theorem ThreeColouring.graph_relabel {V : Type*} (c : ThreeColouring V)
    (e : Fin 3 ≃ Fin 3) (i : Fin 3) : (c.relabel e).graph i = c.graph (e i) := by
  ext u v
  simp only [graph_adj, relabel, Equiv.symm_apply_eq]

end Erdos556
