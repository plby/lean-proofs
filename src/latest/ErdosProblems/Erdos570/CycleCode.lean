/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos79.Core
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- The canonical coded cycle on `k` vertices. -/
def cycleCode (k : ℕ) : GraphCode := ⟨k, SimpleGraph.cycleGraph k⟩

@[simp] theorem cycleCode_vertexCount (k : ℕ) :
    (cycleCode k).vertexCount = k := rfl

@[simp] theorem cycleCode_graph (k : ℕ) :
    (cycleCode k).graph = SimpleGraph.cycleGraph k := rfl

end Erdos570

