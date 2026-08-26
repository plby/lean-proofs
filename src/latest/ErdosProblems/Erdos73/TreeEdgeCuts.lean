import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! The two sides and unique crossing edge of a tree-edge cut. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph

variable {U : Type*} (T : SimpleGraph U)

def treeEdgeSide (u v x : U) : Prop := (T.deleteEdges {s(u, v)}).Reachable u x

theorem treeEdgeSide_self (u v : U) : treeEdgeSide T u v u := .refl u

theorem treeEdgeSide_not_other (hT : T.IsAcyclic) {u v : U} (huv : T.Adj u v) :
    ¬treeEdgeSide T u v v :=
  (isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp hT huv))

theorem treeEdgeSide_eq_of_adj_ne {u v x y : U} (hxy : T.Adj x y)
    (hne : s(x, y) ≠ s(u, v)) : treeEdgeSide T u v x ↔ treeEdgeSide T u v y := by
  have hadj : (T.deleteEdges {s(u, v)}).Adj x y :=
    deleteEdges_adj.mpr ⟨hxy, by simpa only [Set.mem_singleton_iff] using hne⟩
  exact ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.reachable.symm⟩

theorem treeEdgeSide_crossing (hT : T.IsAcyclic) {u v x y : U} (huv : T.Adj u v)
    (hxy : T.Adj x y) (hx : treeEdgeSide T u v x) (hy : ¬treeEdgeSide T u v y) :
    x = u ∧ y = v := by
  have he : s(x, y) = s(u, v) := by
    by_contra hn
    exact hy ((treeEdgeSide_eq_of_adj_ne T hxy hn).mp hx)
  rcases Sym2.eq_iff.mp he with h | h
  · exact h
  · exact False.elim ((treeEdgeSide_not_other T hT huv) (h.1 ▸ hx))

theorem exists_treeEdgeSide_separating (hT : T.IsTree) {u v : U} (huv : u ≠ v) :
    ∃ w, T.Adj u w ∧ ¬treeEdgeSide T u w v := by
  obtain ⟨p, hp⟩ := hT.connected.exists_isPath u v
  obtain ⟨w, hadj, p, rfl⟩ := p.exists_eq_cons_of_ne huv
  refine ⟨w, hadj, ?_⟩
  have hnot : s(u, w) ∉ p.edges := (Walk.isTrail_cons hadj p).mp hp.isTrail |>.2
  have htail : (T.deleteEdges {s(u, w)}).Reachable w v := by
    refine ⟨p.toDeleteEdges {s(u, w)} ?_⟩
    intro e he hm
    have heq : e = s(u, w) := Set.mem_singleton_iff.mp hm
    exact hnot (heq ▸ he)
  intro hreach
  exact (treeEdgeSide_not_other T hT.isAcyclic hadj) (hreach.trans htail.symm)

end
end Erdos73
