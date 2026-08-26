import ErdosProblems.Erdos593.TripleSystem.BridgeBlockRestriction
import ErdosProblems.Erdos593.TripleSystem.SingleEdgePieceConstructible

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Degenerate bridge-free blocks

A bridge-free Levi component containing a hyperedge-node of degree zero cannot
contain any other hyperedge-node.  Its exact ambient edge restriction is
therefore the constructible singleton-edge restriction.
-/

namespace Erdos593

universe w

namespace TripleSystem
namespace BridgeBlock

variable {V E : Type w} (F : TripleSystem V E)
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [DecidableRel F.levi.Adj]

/-- A bridge-free component containing a degree-zero hyperedge-node contains
no other hyperedge-node. -/
theorem componentHyperedgeSet_eq_singleton_of_edge_degree_zero
    {C : Component F} {e : E} (heC : Sum.inr e ∈ C.supp)
    (hzero : (Erdos593.SimpleGraph.bridgeFree F.levi).degree (Sum.inr e) = 0) :
    componentHyperedgeSet F C = {e} := by
  ext f
  constructor
  · intro hfC
    have hre : (Erdos593.SimpleGraph.bridgeFree F.levi).Reachable
        (Sum.inr e) (Sum.inr f) :=
      C.reachable_of_mem_supp heC hfC
    by_contra hef
    have hnodes : (Sum.inr e : V ⊕ E) ≠ Sum.inr f := by
      intro h
      apply hef
      exact (Sum.inr.inj h).symm
    have hpos : 0 <
        (Erdos593.SimpleGraph.bridgeFree F.levi).degree (Sum.inr e) :=
      hre.degree_pos_left hnodes
    omega
  · intro hf
    have hfe : f = e := Set.mem_singleton_iff.mp hf
    subst f
    exact heC

/-- The exact edge restriction represented by a degree-zero hyperedge
component belongs to the constructive class. -/
theorem degreeZeroComponentRestriction_constructible
    {C : Component F} {e : E} (heC : Sum.inr e ∈ C.supp)
    (hzero : (Erdos593.SimpleGraph.bridgeFree F.levi).degree (Sum.inr e) = 0) :
    Constructible (F.edgeRestriction (componentHyperedgeSet F C)) := by
  rw [componentHyperedgeSet_eq_singleton_of_edge_degree_zero F heC hzero]
  exact singletonEdgeRestriction_constructible F e

end BridgeBlock
end TripleSystem
end Erdos593
