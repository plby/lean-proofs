import ErdosProblems.Erdos745.EdgeLaw
import ErdosProblems.Erdos745.TreeComponents
import ErdosProblems.Erdos745.TreeCounting

/-!
# Exact probabilities of prescribed components

Every edge incident to a prescribed component is fixed, while edges on its
complement are free.  This file identifies those events with finite Bernoulli
cylinders in the exact random-graph model.
-/

open scoped BigOperators Sym2

namespace Erdos745

noncomputable section

attribute [local instance] Classical.propDecidable

theorem edge_exists_pair {n : ℕ} (e : Edge n) :
    ∃ u v : Fin n, e.val = s(u, v) := by
  obtain ⟨⟨u, v⟩, h⟩ := Sym2.mk_surjective e.val
  exact ⟨u, v, h.symm⟩

theorem card_edgeCoordinates {n : ℕ} (G : SimpleGraph (Fin n)) :
    (edgeCoordinates G).card = G.edgeSet.ncard := by
  rw [← Erdos746.ncard_edgeSet_graphOfEdges, graphOfEdges_edgeCoordinates]

/-- Extend a graph on a finite vertex set by isolated vertices. -/
def extendGraph {n : ℕ} (S : Finset (Fin n)) (H : SimpleGraph S) : SimpleGraph (Fin n) :=
  H.map (Function.Embedding.subtype (· ∈ S))

theorem extendGraph_adj {n : ℕ} (S : Finset (Fin n)) (H : SimpleGraph S)
    (u v : Fin n) :
    (extendGraph S H).Adj u v ↔ ∃ hu : u ∈ S, ∃ hv : v ∈ S, H.Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
  rw [extendGraph, SimpleGraph.map_adj]
  constructor
  · rintro ⟨u', v', h, rfl, rfl⟩
    exact ⟨u'.property, v'.property, h⟩
  · rintro ⟨hu, hv, h⟩
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩, h, rfl, rfl⟩

theorem ncard_edgeSet_extendGraph {n : ℕ} (S : Finset (Fin n)) (H : SimpleGraph S) :
    (extendGraph S H).edgeSet.ncard = H.edgeSet.ncard := by
  rw [extendGraph, SimpleGraph.edgeSet_map]
  exact Set.ncard_image_of_injective _ (Function.Embedding.sym2Map _).injective

/-- All possible edges internal to a vertex set. -/
def internalEdges {n : ℕ} (S : Finset (Fin n)) : Finset (Edge n) :=
  edgeCoordinates (extendGraph S ⊤)

theorem mem_internalEdges_pair {n : ℕ} (S : Finset (Fin n)) (e : Edge n)
    {u v : Fin n} (he : e.val = s(u, v)) :
    e ∈ internalEdges S ↔ u ∈ S ∧ v ∈ S := by
  have huv : u ≠ v := by
    have h := e.property
    rw [SimpleGraph.mem_edgeFinset, he, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj] at h
    exact h
  rw [internalEdges, mem_edgeCoordinates, he, SimpleGraph.mem_edgeSet, extendGraph_adj]
  simp only [SimpleGraph.top_adj, ne_eq, Subtype.mk.injEq, huv, not_false_eq_true,
    exists_prop, and_true]

theorem card_internalEdges {n : ℕ} (S : Finset (Fin n)) :
    (internalEdges S).card = S.card.choose 2 := by
  rw [internalEdges, card_edgeCoordinates, ncard_edgeSet_extendGraph]
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_coe]

/-- All possible edges with at least one endpoint in `S`. -/
def incidentEdges {n : ℕ} (S : Finset (Fin n)) : Finset (Edge n) :=
  Finset.univ \ internalEdges Sᶜ

theorem mem_incidentEdges_pair {n : ℕ} (S : Finset (Fin n)) (e : Edge n)
    {u v : Fin n} (he : e.val = s(u, v)) :
    e ∈ incidentEdges S ↔ u ∈ S ∨ v ∈ S := by
  simp only [incidentEdges, Finset.mem_sdiff, Finset.mem_univ, true_and,
    mem_internalEdges_pair Sᶜ e he, Finset.mem_compl]
  tauto

theorem card_incidentEdges {n : ℕ} (S : Finset (Fin n)) :
    (incidentEdges S).card = n.choose 2 - (n - S.card).choose 2 := by
  rw [incidentEdges, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Erdos746.card_edge, card_internalEdges, Finset.card_compl]
  simp only [Erdos746.edgeCount, Fintype.card_fin]

theorem edgeCoordinates_extend_subset_incident {n : ℕ} (S : Finset (Fin n))
    (H : SimpleGraph S) : edgeCoordinates (extendGraph S H) ⊆ incidentEdges S := by
  intro e he
  obtain ⟨u, v, huv⟩ := edge_exists_pair e
  rw [mem_incidentEdges_pair S e huv]
  rw [mem_edgeCoordinates, huv, SimpleGraph.mem_edgeSet, extendGraph_adj] at he
  exact Or.inl he.choose

/-- Prescribe the graph on `S` and require all its cut edges to be absent. -/
def HasIsolatedInducedGraph {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (H : SimpleGraph S) : Prop :=
  G.induce (S : Set (Fin n)) = H ∧ IsClosedVertexSet G S

theorem hasIsolatedInducedGraph_iff_cylinder {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (H : SimpleGraph S) :
    HasIsolatedInducedGraph G S H ↔
      edgeCoordinates (extendGraph S H) ⊆ edgeCoordinates G ∧
      Disjoint (incidentEdges S \ edgeCoordinates (extendGraph S H)) (edgeCoordinates G) := by
  constructor
  · rintro ⟨hH, hclosed⟩
    constructor
    · intro e he
      obtain ⟨u, v, huv⟩ := edge_exists_pair e
      rw [mem_edgeCoordinates, huv, SimpleGraph.mem_edgeSet, extendGraph_adj] at he
      obtain ⟨hu, hv, hadj⟩ := he
      rw [mem_edgeCoordinates, huv, SimpleGraph.mem_edgeSet]
      have hi : (G.induce (S : Set (Fin n))).Adj ⟨u, hu⟩ ⟨v, hv⟩ := hH ▸ hadj
      exact hi
    · rw [Finset.disjoint_left]
      intro e he hGe
      obtain ⟨hinc, hnot⟩ := Finset.mem_sdiff.mp he
      obtain ⟨u, v, huv⟩ := edge_exists_pair e
      rw [mem_incidentEdges_pair S e huv] at hinc
      rw [mem_edgeCoordinates, huv, SimpleGraph.mem_edgeSet] at hGe
      have hu : u ∈ S := hinc.elim id (fun hv ↦ hclosed v hv u hGe.symm)
      have hv : v ∈ S := hclosed u hu v hGe
      apply hnot
      rw [mem_edgeCoordinates, huv, SimpleGraph.mem_edgeSet, extendGraph_adj]
      refine ⟨hu, hv, ?_⟩
      have hi : (G.induce (S : Set (Fin n))).Adj ⟨u, hu⟩ ⟨v, hv⟩ := hGe
      exact hH ▸ hi
  · rintro ⟨hpres, habsent⟩
    have hadj (u v : Fin n) (huv : u ≠ v) (hinc : u ∈ S ∨ v ∈ S) :
        G.Adj u v ↔ (extendGraph S H).Adj u v := by
      let e : Edge n := ⟨s(u, v), by simpa using huv⟩
      have he : e ∈ incidentEdges S := (mem_incidentEdges_pair S e rfl).mpr hinc
      have hmem : e ∈ edgeCoordinates G ↔ e ∈ edgeCoordinates (extendGraph S H) := by
        constructor
        · intro hG
          by_contra hnot
          exact Finset.disjoint_left.mp habsent (Finset.mem_sdiff.mpr ⟨he, hnot⟩) hG
        · exact fun h ↦ hpres h
      simpa only [mem_edgeCoordinates, e, SimpleGraph.mem_edgeSet] using hmem
    constructor
    · ext u v
      by_cases huv : u.val = v.val
      · have : u = v := Subtype.ext huv
        subst v
        simp
      · change G.Adj u.val v.val ↔ H.Adj u v
        rw [hadj _ _ huv (Or.inl u.property), extendGraph_adj]
        constructor
        · rintro ⟨_, _, h⟩
          exact h
        · exact fun h ↦ ⟨u.property, v.property, h⟩
    · intro u hu v huv
      have he := (hadj u v huv.ne (Or.inl hu)).mp huv
      rw [extendGraph_adj] at he
      exact he.choose_spec.choose

theorem probability_hasIsolatedInducedGraph (lam : ℝ) (n : ℕ)
    (S : Finset (Fin n)) (H : SimpleGraph S) :
    probability lam n (fun G ↦ HasIsolatedInducedGraph G S H) =
      (edgeProbability lam n : ℝ) ^ H.edgeSet.ncard *
        (1 - (edgeProbability lam n : ℝ)) ^
          (n.choose 2 - (n - S.card).choose 2 - H.edgeSet.ncard) := by
  have hP : (fun G ↦ HasIsolatedInducedGraph G S H) =
      (fun G ↦ edgeCoordinates (extendGraph S H) ⊆ edgeCoordinates G ∧
        Disjoint (incidentEdges S \ edgeCoordinates (extendGraph S H)) (edgeCoordinates G)) := by
    funext G
    exact propext (hasIsolatedInducedGraph_iff_cylinder G S H)
  rw [hP, probability_edge_cylinder _ _ _ _ disjoint_sdiff_self_right]
  rw [Finset.card_sdiff_of_subset (edgeCoordinates_extend_subset_incident S H),
    card_edgeCoordinates, ncard_edgeSet_extendGraph, card_incidentEdges]

/-- Every tree shape has the same number of present edges. -/
theorem tree_edge_ncard {V : Type*} [Fintype V] {H : SimpleGraph V} (hH : H.IsTree) :
    H.edgeSet.ncard = Fintype.card V - 1 := by
  have h := hH.card_edgeFinset
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  omega

/-- The common mass of any one tree shape on a prescribed `k`-set. -/
def treeShapeWeight (lam : ℝ) (n k : ℕ) : ℝ :=
  (edgeProbability lam n : ℝ) ^ (k - 1) *
    (1 - (edgeProbability lam n : ℝ)) ^
      (n.choose 2 - (n - k).choose 2 - (k - 1))

theorem probability_hasIsolatedTree (lam : ℝ) (n : ℕ) (S : Finset (Fin n))
    (H : SimpleGraph S) (hH : H.IsTree) :
    probability lam n (fun G ↦ HasIsolatedInducedGraph G S H) =
      treeShapeWeight lam n S.card := by
  rw [probability_hasIsolatedInducedGraph, tree_edge_ncard hH, Fintype.card_coe]
  rfl

theorem probability_isTreeComponentSet_eq_sum (lam : ℝ) (n : ℕ)
    (S : Finset (Fin n)) :
    probability lam n (fun G ↦ IsTreeComponentSet G S) =
      ∑ H ∈ (Finset.univ : Finset (SimpleGraph S)).filter SimpleGraph.IsTree,
        probability lam n (fun G ↦ HasIsolatedInducedGraph G S H) := by
  let T := (Finset.univ : Finset (SimpleGraph S)).filter SimpleGraph.IsTree
  have hsum := probability_sum_fibers lam n T
    (fun G ↦ G.induce (S : Set (Fin n))) (fun G ↦ IsClosedVertexSet G S)
  have hevent : (fun G ↦ IsTreeComponentSet G S) =
      (fun G ↦ G.induce (S : Set (Fin n)) ∈ T ∧ IsClosedVertexSet G S) := by
    funext G
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, isTreeComponentSet_iff]
  rw [hevent]
  exact hsum

theorem sum_treeShapeWeight (lam : ℝ) (n : ℕ) (S : Finset (Fin n)) :
    (∑ _H ∈ (Finset.univ : Finset (SimpleGraph S)).filter SimpleGraph.IsTree,
      treeShapeWeight lam n S.card) =
      (labelledTreeCount S.card : ℝ) * treeShapeWeight lam n S.card := by
  rw [Finset.sum_const, nsmul_eq_mul]
  apply congrArg (fun m : ℕ ↦ (m : ℝ) * treeShapeWeight lam n S.card)
  calc
    _ = Fintype.card {H : SimpleGraph S // H.IsTree} := by
      rw [Fintype.card_subtype]
    _ = labelledTreeCount S.card := by
      have hcard := card_trees_eq_labelledTreeCount (V := S)
      rw [Fintype.card_eq_nat_card, Fintype.card_coe] at hcard
      rw [Fintype.card_eq_nat_card]
      exact hcard

/-- Probability that one prescribed vertex set is a tree component. -/
theorem probability_isTreeComponentSet (lam : ℝ) (n : ℕ) (S : Finset (Fin n)) :
    probability lam n (fun G ↦ IsTreeComponentSet G S) =
      (labelledTreeCount S.card : ℝ) * (edgeProbability lam n : ℝ) ^ (S.card - 1) *
        (1 - (edgeProbability lam n : ℝ)) ^
          (n.choose 2 - (n - S.card).choose 2 - (S.card - 1)) := by
  rw [probability_isTreeComponentSet_eq_sum]
  calc
    _ = ∑ _H ∈ (Finset.univ : Finset (SimpleGraph S)).filter SimpleGraph.IsTree,
        treeShapeWeight lam n S.card := by
      apply Finset.sum_congr rfl
      intro H hH
      exact probability_hasIsolatedTree lam n S H (Finset.mem_filter.mp hH).2
    _ = _ := by rw [sum_treeShapeWeight, treeShapeWeight, mul_assoc]

end

end Erdos745
