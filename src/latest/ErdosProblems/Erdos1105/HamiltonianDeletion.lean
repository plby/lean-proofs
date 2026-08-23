import ErdosProblems.Erdos1105.OrePath

namespace Erdos1105

open SimpleGraph

/-- A Hamiltonian graph of order at least three has no bridge edges. -/
theorem hamiltonian_not_isBridge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsHamiltonian) (hcard : 3 ≤ Fintype.card V)
    (a b : V) : ¬G.IsBridge s(a, b) := by
  intro hbridge
  obtain ⟨v, p, hp⟩ := hG (by omega)
  have hnot := hbridge.notMem_edges_of_isCycle hp.isCycle
  have hsub : ∀ e ∈ p.edges, e ∈ (G.deleteEdges {s(a, b)}).edgeSet := by
    intro e he
    rw [edgeSet_deleteEdges]
    exact ⟨p.edges_subset_edgeSet he, fun heq ↦ hnot (heq ▸ he)⟩
  have hdel : (G.deleteEdges {s(a, b)}).IsHamiltonian :=
    fun _ ↦ ⟨v, p.transfer _ hsub, hp.transfer hsub⟩
  exact (isBridge_iff.mp hbridge) (hdel.connected.preconnected a b)

/-- Reachability can be transported when every edge has a replacement path. -/
theorem reachable_of_edges_reachable {V : Type*} (G H : SimpleGraph V)
    (h : ∀ x y, G.Adj x y → H.Reachable x y) {u v : V} (huv : G.Reachable u v) :
    H.Reachable u v := by
  obtain ⟨p⟩ := huv
  induction p with
  | nil => exact Reachable.refl _
  | @cons x y z hxy p ih => exact (h x y hxy).trans ih

/-- Removing a non-bridge preserves every old connectivity relation,
also for graphs with more than one component. -/
theorem reachable_delete_edge_of_not_isBridge {V : Type*} (G : SimpleGraph V)
    {a b u v : V} (hnb : ¬G.IsBridge s(a, b)) (huv : G.Reachable u v) :
    (G.deleteEdges {s(a, b)}).Reachable u v := by
  classical
  have hab : (G.deleteEdges {s(a, b)}).Reachable a b := by
    simpa only [isBridge_iff, not_not] using hnb
  apply reachable_of_edges_reachable G _ (fun x y hxy ↦ ?_) huv
  by_cases heq : s(x, y) = s(a, b)
  · rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hab
    · exact hab.symm
  · exact (show (G.deleteEdges {s(a, b)}).Adj x y from
      deleteEdges_adj.mpr ⟨hxy, heq⟩).reachable

/-- A Hamiltonian component certifies that each of its edges is not a
bridge in the ambient graph. -/
theorem component_hamiltonian_not_isBridge {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) (B : R.ConnectedComponent) [Fintype B]
    (hB : B.toSimpleGraph.IsHamiltonian) (hcard : 3 ≤ Fintype.card B)
    {a b : V} (ha : a ∈ B.supp) (hb : b ∈ B.supp) : ¬R.IsBridge s(a, b) := by
  classical
  have hnb := hamiltonian_not_isBridge B.toSimpleGraph hB hcard ⟨a, ha⟩ ⟨b, hb⟩
  have hr : (B.toSimpleGraph.deleteEdges {s(⟨a, ha⟩, ⟨b, hb⟩)}).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
    simpa only [isBridge_iff, not_not] using hnb
  let f : (B.toSimpleGraph.deleteEdges {s(⟨a, ha⟩, ⟨b, hb⟩)}) →g R.deleteEdges {s(a, b)} :=
    { toFun := Subtype.val
      map_rel' := by
        intro x y hxy
        rw [deleteEdges_adj, Set.mem_singleton_iff] at hxy ⊢
        refine ⟨hxy.1, fun heq ↦ hxy.2 ?_⟩
        rcases Sym2.eq_iff.mp heq with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
        · rw [show x = ⟨a, ha⟩ from Subtype.ext ha', show y = ⟨b, hb⟩ from Subtype.ext hb']
        · rw [show x = ⟨b, hb⟩ from Subtype.ext ha', show y = ⟨a, ha⟩ from Subtype.ext hb',
            Sym2.eq_swap] }
  intro hbridge
  exact (isBridge_iff.mp hbridge) (hr.map f)

end Erdos1105
