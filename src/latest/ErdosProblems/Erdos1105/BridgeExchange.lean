import ErdosProblems.Erdos1105.ColorRepresentative

namespace Erdos1105

open SimpleGraph

/-- Suppose all current edges other than `f` respect the components
obtained by cutting `f` in a reference graph. Swapping a non-bridge
representative edge for a same-colored edge across that cut puts `f`
on a cycle. This is the exchange step for the bridge-color closure. -/
theorem crossing_swap_makes_nonbridge {V C : Type*} (R K : SimpleGraph V)
    (c : Sym2 V → C) (hK : Set.InjOn c K.edgeSet) (hconn : K.Preconnected)
    (e : K.edgeSet) (hne : ¬K.IsBridge e.val) (f : Sym2 V)
    (hrespect : ∀ a b, K.Adj a b → s(a, b) ≠ f →
      (R.deleteEdges {f}).Reachable a b)
    {a b : V} (hab : a ≠ b) (hcol : c s(a, b) = c e.val)
    (hcross : ¬(R.deleteEdges {f}).Reachable a b) :
    ¬(swapRepresentative K e.val s(a, b)).IsBridge f := by
  classical
  let d : (⊤ : SimpleGraph V).edgeSet := ⟨s(a, b), hab⟩
  let L := swapRepresentative K e.val d.val
  obtain ⟨p, hp⟩ := (reachable_delete_of_not_isBridge K hne (hconn a b)).exists_isPath
  have hdnot : d.val ∉ p.edges := by
    intro hd
    have hdK : d.val ∈ K.edgeSet ∧ d.val ≠ e.val := by
      simpa only [edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff] using
        p.edges_subset_edgeSet hd
    exact hdK.2 (hK hdK.1 e.property hcol)
  have hfmem : f ∈ p.edges := by
    by_contra hfnot
    have hsub : ∀ g ∈ p.edges, g ∈ (K.deleteEdges {f}).edgeSet := by
      intro g hg
      rw [edgeSet_deleteEdges]
      refine ⟨edgeSet_mono (K.deleteEdges_le _) (p.edges_subset_edgeSet hg), ?_⟩
      intro heq
      exact hfnot (heq ▸ hg)
    have hreach : (K.deleteEdges {f}).Reachable a b := ⟨p.transfer _ hsub⟩
    apply hcross
    apply reachable_of_edges_reachable (K.deleteEdges {f}) (R.deleteEdges {f}) ?_ hreach
    intro x y hxy
    have hxy' : K.Adj x y ∧ s(x, y) ≠ f := by
      simpa only [deleteEdges_adj, Set.mem_singleton_iff] using hxy
    exact hrespect x y hxy'.1 hxy'.2
  have hdel : K.deleteEdges {e.val} ≤ L := deleteEdges_le_swapRepresentative K e.val d
  have hsub : ∀ g ∈ p.edges, g ∈ L.edgeSet :=
    fun g hg ↦ edgeSet_mono hdel (p.edges_subset_edgeSet hg)
  let p' := p.transfer L hsub
  have hp' : p'.IsPath := hp.transfer hsub
  have hnew : L.Adj a b := (mem_swapRepresentative K e.val d d.val).mpr (Or.inr rfl)
  have hc : (Walk.cons hnew.symm p').IsCycle := by
    apply (Walk.cons_isCycle_iff p' hnew.symm).mpr
    refine ⟨hp', ?_⟩
    rw [Sym2.eq_swap, Walk.edges_transfer]
    exact hdnot
  intro hbridge
  apply hbridge.notMem_edges_of_isCycle hc
  apply List.mem_cons_of_mem
  change f ∈ p'.edges
  have hep : p'.edges = p.edges := Walk.edges_transfer p hsub
  rwa [hep]

end Erdos1105

#print axioms Erdos1105.crossing_swap_makes_nonbridge
