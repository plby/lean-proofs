import ErdosProblems.Erdos593.Graph.Bridge
import ErdosProblems.Erdos593.TripleSystem.Levi

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Intrinsic structural conditions

The finite structural kernel characterizes the constructive class by linearity,
a genuine Levi-graph bridge at each hyperedge-node, and even Berge-cycle length.
A Berge cycle of length `k` is represented by a Levi cycle of length `2 * k`, so
even Berge length is encoded by divisibility of the Levi-cycle length by four.
-/

namespace Erdos593

universe u v

namespace TripleSystem

variable {V : Type u} {E : Type v} (F : TripleSystem V E)

/-- Every Levi hyperedge-node is incident with an actual bridge edge. -/
def BridgeAtEveryEdge : Prop :=
  ∀ e : E, ∃ x : V,
    s(Sum.inl x, Sum.inr e) ∈ SimpleGraph.bridgeEdges F.levi

/-- Every Berge cycle has even length, expressed on the corresponding Levi cycle. -/
def EvenBergeCycles : Prop :=
  ∀ ⦃z : V ⊕ E⦄ (c : F.levi.Walk z z), c.IsCycle → 4 ∣ c.length

/-- The three intrinsic conditions appearing in the finite classification. -/
def Intrinsic : Prop :=
  F.Linear ∧ F.BridgeAtEveryEdge ∧ F.EvenBergeCycles

end TripleSystem

end Erdos593
