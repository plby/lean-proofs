import ErdosProblems.Erdos19.CommonNeighborColoring

/-! # Coloring linear hypergraphs in a subprojective size window -/

namespace Erdos19.SetHypergraph

attribute [local instance] Classical.propDecidable

theorem lineGraph_degree_le_of_size_window {V : Type*} [Fintype V]
    (H : SetHypergraph V) (hlinear : H.IsLinear) (r R D : ℕ) (hr : 2 ≤ r)
    (hmin : ∀ e : H, r ≤ e.1.ncard) (hmax : ∀ e : H, e.1.ncard ≤ R)
    (hbound : R * Fintype.card V ≤ D * (r - 1)) (e : H) :
    (H.lineGraph.neighborSet e).ncard ≤ D := by
  have hpairs := H.ncard_mul_le_pairBudget hlinear e (H.neighborEdges e)
    (Set.Subset.refl _) (r - 1) (fun f _ ↦ Nat.sub_le_sub_right (hmin f) 1)
  have hupper : e.1.ncard * (Fintype.card V - e.1.ncard) ≤ R * Fintype.card V :=
    Nat.mul_le_mul (hmax e) (Nat.sub_le _ _)
  exact Nat.le_of_mul_le_mul_right ((hpairs.trans hupper).trans hbound) (by omega)

theorem eventually_edgeColorable_of_size_window (h : ℕ) (hh : 1 ≤ h) :
    ∃ q : ℕ, 0 < q ∧ ∃ N : ℕ, q ≤ N ∧ ∀ D : ℕ, N ≤ D →
      ∀ (V : Type*) [Fintype V], ∀ H : SetHypergraph V, H.IsLinear →
      ∀ r R : ℕ, 2 ≤ r → (∀ e : H, r ≤ e.1.ncard) → (∀ e : H, e.1.ncard ≤ R) →
      R * Fintype.card V ≤ D * (r - 1) →
      (R - 1) ^ 2 + (Fintype.card V - 1) / (r - 1) + D / h ≤ D →
      H.EdgeColorable (D - D / q) := by
  obtain ⟨q, hq, N, hN, hcolor⟩ := eventually_colorable_of_common_neighbor_gap h hh
  refine ⟨q, hq, N, hN, ?_⟩
  intro D hD V _ H hlinear r R hr hmin hmax hdegree hcommon
  apply (H.edgeColorable_iff_lineGraph_colorable _).mpr
  apply hcolor D hD H H.lineGraph
    (H.lineGraph_degree_le_of_size_window hlinear r R D hr hmin hmax hdegree)
  intro e f hef
  have hcount := H.commonNeighborEdges_ncard_le_of_size_range hlinear r R hr hmin hmax e f hef.1 hef.2
  change (H.commonNeighborEdges e f).ncard + D / h ≤ D
  have h' : (H.commonNeighborEdges e f).ncard ≤
      (R - 1) ^ 2 + (Fintype.card V - 1) / (r - 1) := by simpa only [pow_two] using hcount
  omega

#print axioms eventually_edgeColorable_of_size_window

end Erdos19.SetHypergraph
