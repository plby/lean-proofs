import ErdosProblems.Erdos593.TripleSystem.Intrinsic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Bridge selectors

This optional interface records one incident Levi bridge at every hyperedge
node.  It is equivalent to `BridgeAtEveryEdge` and allows the all-bridges
decomposition used by the core formalization to interoperate with the
selected-incidence formulation in Eric Li's contemporaneous proof
(`arXiv:2606.24882`, Sections 3--5).  No result from that paper is assumed here.
-/

namespace Erdos593

open scoped Sym2

universe u v

namespace TripleSystem

variable {V : Type u} {E : Type v} (F : TripleSystem V E)

/-- A choice of one point on every hyperedge whose corresponding Levi
incidence is an actual bridge. -/
structure BridgeSelector where
  point : E → V
  inc : ∀ e, F.Inc (point e) e
  isBridge : ∀ e, F.levi.IsBridge s(Sum.inl (point e), Sum.inr e)

/-- The intrinsic bridge condition supplies a bridge selector. -/
noncomputable def bridgeSelectorOfBridgeAtEveryEdge
    (h : F.BridgeAtEveryEdge) : F.BridgeSelector where
  point e := Classical.choose (h e)
  inc e := by
    have hs := Classical.choose_spec (h e)
    change F.levi.Adj (Sum.inl (Classical.choose (h e))) (Sum.inr e) ∧
      F.levi.IsBridge
        s(Sum.inl (Classical.choose (h e)), Sum.inr e) at hs
    exact F.levi_adj_point_edge.mp hs.1
  isBridge e := by
    have hs := Classical.choose_spec (h e)
    change F.levi.Adj (Sum.inl (Classical.choose (h e))) (Sum.inr e) ∧
      F.levi.IsBridge
        s(Sum.inl (Classical.choose (h e)), Sum.inr e) at hs
    exact hs.2

/-- Selecting one incident bridge at every hyperedge-node is exactly the
intrinsic bridge-at-every-edge condition. -/
theorem nonempty_bridgeSelector_iff :
    Nonempty F.BridgeSelector ↔ F.BridgeAtEveryEdge := by
  constructor
  · rintro ⟨p⟩ e
    refine ⟨p.point e, ?_⟩
    change F.levi.Adj (Sum.inl (p.point e)) (Sum.inr e) ∧
      F.levi.IsBridge s(Sum.inl (p.point e), Sum.inr e)
    exact ⟨F.levi_adj_point_edge.mpr (p.inc e), p.isBridge e⟩
  · intro h
    exact ⟨F.bridgeSelectorOfBridgeAtEveryEdge h⟩

end TripleSystem
end Erdos593
