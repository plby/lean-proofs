import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Elementary bridge lemmas

Small finite/simple-graph facts used by the Levi-graph decomposition.
-/

namespace Erdos593

namespace SimpleGraph

universe u

variable {V : Type u}

/-- The manuscript-level set of bridges.  The edge-membership conjunct is
essential: mathlib's `SimpleGraph.IsBridge` is an endpoint-disconnection
predicate and does not itself assert that the unordered pair is an edge. -/
def bridgeEdges (G : _root_.SimpleGraph V) : Set (Sym2 V) :=
  {e | e ∈ G.edgeSet ∧ G.IsBridge e}

/-- An edge whose endpoint `v` has no neighbour other than `u` is a bridge. -/
-- ARISTOTLE_TARGET G1
theorem isBridge_of_adj_of_unique_neighbor
    (G : _root_.SimpleGraph V) {u v : V}
    (huv : G.Adj u v)
    (hv : ∀ ⦃w : V⦄, G.Adj v w → w = u) :
    G.IsBridge s(u, v) := by
  rw [_root_.SimpleGraph.isBridge_iff]
  intro hreach
  have hr := hreach.symm
  rw [_root_.SimpleGraph.reachable_eq_reflTransGen] at hr
  rcases hr.cases_head with h | ⟨w, hw, -⟩
  · exact huv.ne' h
  · rw [_root_.SimpleGraph.deleteEdges_adj] at hw
    obtain ⟨hgvw, hnot⟩ := hw
    have hwu : w = u := hv hgvw
    subst w
    exact hnot (by simp [Sym2.eq_swap])

end SimpleGraph

end Erdos593
