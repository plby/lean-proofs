import ErdosProblems.Erdos745.ComponentPair
import ErdosProblems.Erdos745.ProbabilityBounds
import ErdosProblems.Erdos745.VertexSetSums

/-!
# Spanning-tree upper bounds for arbitrary components

Unlike the exact isolated-tree law, these estimates allow additional internal
edges. Only the cut is required to be absent.
-/

open scoped BigOperators Sym2

namespace Erdos745

noncomputable section

attribute [local instance] Classical.propDecidable

theorem vertex_compl_disjoint {n : ℕ} (S : Finset (Fin n)) : Disjoint S Sᶜ :=
  Finset.disjoint_left.mpr (fun _ hx hxc ↦ Finset.mem_compl.mp hxc hx)

/-- The full edge cut between a vertex set and its complement. -/
def cutEdges {n : ℕ} (S : Finset (Fin n)) : Finset (Edge n) :=
  Erdos746.crossingEdges S Sᶜ (vertex_compl_disjoint S)

theorem card_cutEdges {n : ℕ} (S : Finset (Fin n)) :
    (cutEdges S).card = S.card * (n - S.card) := by
  rw [cutEdges, Erdos746.card_crossingEdges, Finset.card_compl, Fintype.card_fin]

theorem isClosedVertexSet_iff_cut {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) :
    IsClosedVertexSet G S ↔ Disjoint (cutEdges S) (edgeCoordinates G) := by
  rw [Finset.disjoint_left]
  constructor
  · intro hclosed e he hG
    obtain ⟨u, hu, v, hv, heq⟩ :=
      (Erdos746.mem_crossingEdges_iff (vertex_compl_disjoint S) e).mp he
    rw [mem_edgeCoordinates, heq, SimpleGraph.mem_edgeSet] at hG
    exact (Finset.mem_compl.mp hv) (hclosed u hu v hG)
  · intro hcut u hu v huv
    by_contra hv
    let e : Edge n := ⟨s(u, v), by simpa using huv.ne⟩
    have he : e ∈ cutEdges S :=
      (Erdos746.mem_crossingEdges_iff (vertex_compl_disjoint S) e).mpr
        ⟨u, hu, v, Finset.mem_compl.mpr hv, rfl⟩
    have hG : e ∈ edgeCoordinates G := by
      rw [mem_edgeCoordinates, SimpleGraph.mem_edgeSet]
      exact huv
    exact hcut he hG

theorem extendEdges_disjoint_cut {n : ℕ} (S : Finset (Fin n)) (H : SimpleGraph S) :
    Disjoint (edgeCoordinates (extendGraph S H)) (cutEdges S) := by
  have hsubset : cutEdges S ⊆ incidentEdges Sᶜ := by
    rw [cutEdges, ← incidentEdges_inter (vertex_compl_disjoint S)]
    exact Finset.inter_subset_right
  exact (extendEdges_disjoint_incident (vertex_compl_disjoint S) H).mono_right hsubset

theorem extendGraph_le_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (H : SimpleGraph S) :
    extendGraph S H ≤ G ↔ H ≤ G.induce (S : Set (Fin n)) := by
  constructor
  · intro h u v huv
    exact h ((extendGraph_adj S H u.val v.val).mpr ⟨u.property, v.property, huv⟩)
  · intro h u v huv
    obtain ⟨hu, hv, hadj⟩ := (extendGraph_adj S H u v).mp huv
    exact h hadj

theorem edgeCoordinates_subset_iff_le {n : ℕ} (G H : SimpleGraph (Fin n)) :
    edgeCoordinates G ⊆ edgeCoordinates H ↔ G ≤ H := by
  constructor
  · intro h u v huv
    let e : Edge n := ⟨s(u, v), by simpa using huv.ne⟩
    have he : e ∈ edgeCoordinates G := by
      rw [mem_edgeCoordinates, SimpleGraph.mem_edgeSet]
      exact huv
    have hmem := h he
    simpa only [mem_edgeCoordinates, e, SimpleGraph.mem_edgeSet] using hmem
  · intro h e he
    rw [mem_edgeCoordinates] at he ⊢
    exact SimpleGraph.edgeSet_mono h he

theorem probability_containsTree_closed (lam : ℝ) (n : ℕ)
    (S : Finset (Fin n)) (T : SimpleGraph S) (hT : T.IsTree) :
    probability lam n (fun G ↦ T ≤ G.induce (S : Set (Fin n)) ∧ IsClosedVertexSet G S) =
      (edgeProbability lam n : ℝ) ^ (S.card - 1) *
        (1 - (edgeProbability lam n : ℝ)) ^ (S.card * (n - S.card)) := by
  have hevent : (fun G ↦ T ≤ G.induce (S : Set (Fin n)) ∧ IsClosedVertexSet G S) =
      (fun G ↦ edgeCoordinates (extendGraph S T) ⊆ edgeCoordinates G ∧
        Disjoint (cutEdges S) (edgeCoordinates G)) := by
    funext G
    apply propext
    rw [edgeCoordinates_subset_iff_le, extendGraph_le_iff, isClosedVertexSet_iff_cut]
  rw [hevent, probability_edge_cylinder _ _ _ _ (extendEdges_disjoint_cut S T),
    card_edgeCoordinates, ncard_edgeSet_extendGraph, tree_edge_ncard hT, card_cutEdges]
  simp only [Fintype.card_coe]

theorem sum_constant_tree_shapes {n : ℕ} (S : Finset (Fin n)) (a : ℝ) :
    (∑ _T ∈ (Finset.univ : Finset (SimpleGraph S)).filter SimpleGraph.IsTree, a) =
      (labelledTreeCount S.card : ℝ) * a := by
  rw [Finset.sum_const, nsmul_eq_mul]
  apply congrArg (fun m : ℕ ↦ (m : ℝ) * a)
  calc
    _ = Fintype.card {H : SimpleGraph S // H.IsTree} := by
      rw [Fintype.card_subtype]
    _ = labelledTreeCount S.card := by
      have hcard := card_trees_eq_labelledTreeCount (V := S)
      rw [Fintype.card_eq_nat_card, Fintype.card_coe] at hcard
      rw [Fintype.card_eq_nat_card]
      exact hcard

theorem probability_isComponentSet_le (lam : ℝ) (n : ℕ) (S : Finset (Fin n)) :
    probability lam n (fun G ↦ IsComponentSet G S) ≤
      (labelledTreeCount S.card : ℝ) * (edgeProbability lam n : ℝ) ^ (S.card - 1) *
        (1 - (edgeProbability lam n : ℝ)) ^ (S.card * (n - S.card)) := by
  let I := (Finset.univ : Finset (SimpleGraph S)).filter SimpleGraph.IsTree
  have hsub : probability lam n (fun G ↦ IsComponentSet G S) ≤
      probability lam n (fun G ↦ ∃ T ∈ I,
        T ≤ G.induce (S : Set (Fin n)) ∧ IsClosedVertexSet G S) := by
    apply probability_mono
    intro G hG
    obtain ⟨hc, hclosed⟩ := (isComponentSet_iff_connected_closed G S).mp hG
    obtain ⟨T, hle, hT⟩ := hc.exists_isTree_le
    exact ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩, hle, hclosed⟩
  calc
    _ ≤ ∑ T ∈ I, probability lam n
        (fun G ↦ T ≤ G.induce (S : Set (Fin n)) ∧ IsClosedVertexSet G S) :=
      hsub.trans (probability_exists_finset_le _ _ _ _)
    _ = ∑ _T ∈ I, (edgeProbability lam n : ℝ) ^ (S.card - 1) *
        (1 - (edgeProbability lam n : ℝ)) ^ (S.card * (n - S.card)) := by
      apply Finset.sum_congr rfl
      intro T hT
      exact probability_containsTree_closed lam n S T (Finset.mem_filter.mp hT).2
    _ = _ := by
      rw [sum_constant_tree_shapes]
      exact (mul_assoc _ _ _).symm

/-- The spanning-tree union-bound contribution for one component order. -/
def componentUpper (lam : ℝ) (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * (labelledTreeCount k : ℝ) *
    (edgeProbability lam n : ℝ) ^ (k - 1) *
      (1 - (edgeProbability lam n : ℝ)) ^ (k * (n - k))

theorem sum_vertexWindow_card (n : ℕ) (I : Finset ℕ) (f : ℕ → ℝ) :
    (∑ S ∈ vertexWindow n I, f S.card) = ∑ k ∈ I, (n.choose k : ℝ) * f k := by
  rw [sum_vertexWindow]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = ∑ _S ∈ Finset.univ.powersetCard k, f k := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [(Finset.mem_powersetCard.mp hS).2]
    _ = _ := by simp only [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]

/-- A finite union bound for components in any chosen window of orders. -/
theorem probability_componentOrder_mem_le (lam : ℝ) (n : ℕ) (I : Finset ℕ) :
    probability lam n (fun G ↦ ∃ C : G.ConnectedComponent, C.supp.ncard ∈ I) ≤
      ∑ k ∈ I, componentUpper lam n k := by
  have hsub : probability lam n (fun G ↦ ∃ C : G.ConnectedComponent, C.supp.ncard ∈ I) ≤
      probability lam n (fun G ↦ ∃ S ∈ vertexWindow n I, IsComponentSet G S) := by
    apply probability_mono
    rintro G ⟨C, hC⟩
    refine ⟨C.supp.toFinset, ?_, C, by simp⟩
    simp only [vertexWindow, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ,
      true_and, ← Set.ncard_eq_toFinset_card']
    exact hC
  calc
    _ ≤ ∑ S ∈ vertexWindow n I, probability lam n (fun G ↦ IsComponentSet G S) :=
      hsub.trans (probability_exists_finset_le _ _ _ _)
    _ ≤ ∑ S ∈ vertexWindow n I,
        (labelledTreeCount S.card : ℝ) * (edgeProbability lam n : ℝ) ^ (S.card - 1) *
          (1 - (edgeProbability lam n : ℝ)) ^ (S.card * (n - S.card)) :=
      Finset.sum_le_sum (fun S _ ↦ probability_isComponentSet_le lam n S)
    _ = _ := by
      rw [sum_vertexWindow_card n I (fun k ↦ (labelledTreeCount k : ℝ) *
        (edgeProbability lam n : ℝ) ^ (k - 1) *
          (1 - (edgeProbability lam n : ℝ)) ^ (k * (n - k)))]
      apply Finset.sum_congr rfl
      intro k _
      unfold componentUpper
      ring

end

end Erdos745
