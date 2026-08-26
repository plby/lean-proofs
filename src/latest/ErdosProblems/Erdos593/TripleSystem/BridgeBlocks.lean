import ErdosProblems.Erdos593.Graph.BridgeFree
import ErdosProblems.Erdos593.TripleSystem.Intrinsic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Bridge-deleted Levi components

Small glue lemmas connecting the intrinsic bridge condition on a triple system
to the generic bridge-deletion results for finite simple graphs.
-/

namespace Erdos593

universe u v

namespace TripleSystem

variable {V : Type u} {E : Type v} (F : TripleSystem V E)

/-- In a finite intrinsic triple system, every Levi hyperedge-node has either
zero or two incidences left after every bridge is deleted. -/
-- REVERSE_OBLIGATION R1
theorem levi_bridgeFree_edge_degree_eq_zero_or_two
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [DecidableRel F.levi.Adj]
    (hbridge : F.BridgeAtEveryEdge) (e : E) :
    Or ((Erdos593.SimpleGraph.bridgeFree F.levi).degree (Sum.inr e) = 0)
       ((Erdos593.SimpleGraph.bridgeFree F.levi).degree (Sum.inr e) = 2) := by
  have hdeg : F.levi.degree (Sum.inr e) = 3 := by
    rw [(_root_.SimpleGraph.card_neighborFinset_eq_degree
          F.levi (Sum.inr e)).symm,
      _root_.SimpleGraph.neighborFinset_def,
      (Set.ncard_eq_toFinset_card'
        (F.levi.neighborSet (Sum.inr e))).symm]
    exact F.levi_edge_neighbor_ncard e
  let x := Exists.choose (hbridge e)
  have hx := Exists.choose_spec (hbridge e)
  change And (F.levi.Adj (Sum.inl x) (Sum.inr e))
      (F.levi.IsBridge s(Sum.inl x, Sum.inr e)) at hx
  exact Erdos593.SimpleGraph.bridgeFree_degree_eq_zero_or_two
    F.levi (Sum.inr e) hdeg
      (Exists.intro (Sum.inl x) (And.intro hx.1.symm (by
        simpa [Sym2.eq_swap] using! hx.2)))

end TripleSystem

end Erdos593
