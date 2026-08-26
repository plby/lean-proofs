import ErdosProblems.Erdos745.ComponentLaw
import ErdosProblems.Erdos746.NeighborhoodCount

/-!
# The exact two-component correction

For disjoint vertex sets the only coordinates shared by their component
events are the absent edges between them.  The formula is proved without
division and therefore remains valid even at boundary edge probabilities.
-/

open scoped BigOperators Sym2

namespace Erdos745

noncomputable section

attribute [local instance] Classical.propDecidable

theorem extendEdges_disjoint_incident {n : ℕ} {S U : Finset (Fin n)}
    (hSU : Disjoint S U) (H : SimpleGraph S) :
    Disjoint (edgeCoordinates (extendGraph S H)) (incidentEdges U) := by
  rw [Finset.disjoint_left]
  intro e he hinc
  obtain ⟨u, v, huv⟩ := edge_exists_pair e
  rw [mem_edgeCoordinates, huv, SimpleGraph.mem_edgeSet, extendGraph_adj] at he
  obtain ⟨hu, hv, _⟩ := he
  rw [mem_incidentEdges_pair U e huv] at hinc
  rcases hinc with huU | hvU
  · exact Finset.disjoint_left.mp hSU hu huU
  · exact Finset.disjoint_left.mp hSU hv hvU

theorem incidentEdges_inter {n : ℕ} {S U : Finset (Fin n)} (hSU : Disjoint S U) :
    incidentEdges S ∩ incidentEdges U = Erdos746.crossingEdges S U hSU := by
  ext e
  rw [Finset.mem_inter, Erdos746.mem_crossingEdges_iff]
  constructor
  · rintro ⟨heS, heU⟩
    obtain ⟨u, v, huv⟩ := edge_exists_pair e
    rw [mem_incidentEdges_pair S e huv] at heS
    rw [mem_incidentEdges_pair U e huv] at heU
    rcases heS with huS | hvS <;> rcases heU with huU | hvU
    · exact False.elim (Finset.disjoint_left.mp hSU huS huU)
    · exact ⟨u, huS, v, hvU, huv⟩
    · exact ⟨v, hvS, u, huU, huv.trans (Sym2.eq_swap)⟩
    · exact False.elim (Finset.disjoint_left.mp hSU hvS hvU)
  · rintro ⟨u, hu, v, hv, huv⟩
    rw [mem_incidentEdges_pair S e huv, mem_incidentEdges_pair U e huv]
    exact ⟨Or.inl hu, Or.inr hv⟩

/-- The edges prescribed absent by an isolated induced-graph event. -/
def componentAbsentEdges {n : ℕ} (S : Finset (Fin n)) (H : SimpleGraph S) : Finset (Edge n) :=
  incidentEdges S \ edgeCoordinates (extendGraph S H)

theorem componentAbsentEdges_inter {n : ℕ} {S U : Finset (Fin n)}
    (hSU : Disjoint S U) (H : SimpleGraph S) (J : SimpleGraph U) :
    componentAbsentEdges S H ∩ componentAbsentEdges U J = incidentEdges S ∩ incidentEdges U := by
  ext e
  simp only [componentAbsentEdges, Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · exact fun h ↦ ⟨h.1.1, h.2.1⟩
  · rintro ⟨hS, hU⟩
    exact ⟨⟨hS, fun he ↦ Finset.disjoint_left.mp (extendEdges_disjoint_incident hSU H) he hU⟩,
      ⟨hU, fun he ↦ Finset.disjoint_left.mp (extendEdges_disjoint_incident hSU.symm J) he hS⟩⟩

theorem card_componentAbsentEdges_inter {n : ℕ} {S U : Finset (Fin n)}
    (hSU : Disjoint S U) (H : SimpleGraph S) (J : SimpleGraph U) :
    (componentAbsentEdges S H ∩ componentAbsentEdges U J).card = S.card * U.card := by
  rw [componentAbsentEdges_inter hSU, incidentEdges_inter hSU, Erdos746.card_crossingEdges]

/-- Exact multiplication law for two prescribed disjoint components. -/
theorem probability_hasIsolatedInducedGraph_pair (lam : ℝ) (n : ℕ)
    {S U : Finset (Fin n)} (hSU : Disjoint S U)
    (H : SimpleGraph S) (J : SimpleGraph U) :
    probability lam n (fun G ↦ HasIsolatedInducedGraph G S H ∧ HasIsolatedInducedGraph G U J) *
        (1 - (edgeProbability lam n : ℝ)) ^ (S.card * U.card) =
      probability lam n (fun G ↦ HasIsolatedInducedGraph G S H) *
        probability lam n (fun G ↦ HasIsolatedInducedGraph G U J) := by
  have hS := extendEdges_disjoint_incident hSU H
  have hU := extendEdges_disjoint_incident hSU.symm J
  have hpres := hS.mono_right (edgeCoordinates_extend_subset_incident U J)
  have h := probability_edge_cylinder_pair lam n
    (edgeCoordinates (extendGraph S H)) (componentAbsentEdges S H)
    (edgeCoordinates (extendGraph U J)) (componentAbsentEdges U J)
    hpres disjoint_sdiff_self_right (hS.mono_right Finset.sdiff_subset)
    (hU.mono_right Finset.sdiff_subset) disjoint_sdiff_self_right
  rw [card_componentAbsentEdges_inter hSU H J] at h
  simpa only [componentAbsentEdges, ← hasIsolatedInducedGraph_iff_cylinder] using h

theorem probability_two_treeComponents_eq_sum (lam : ℝ) (n : ℕ)
    (S U : Finset (Fin n)) :
    probability lam n (fun G ↦ IsTreeComponentSet G S ∧ IsTreeComponentSet G U) =
      ∑ H ∈ (Finset.univ : Finset (SimpleGraph S)).filter SimpleGraph.IsTree,
        ∑ J ∈ (Finset.univ : Finset (SimpleGraph U)).filter SimpleGraph.IsTree,
          probability lam n (fun G ↦ HasIsolatedInducedGraph G S H ∧
            HasIsolatedInducedGraph G U J) := by
  let TS := (Finset.univ : Finset (SimpleGraph S)).filter SimpleGraph.IsTree
  let TU := (Finset.univ : Finset (SimpleGraph U)).filter SimpleGraph.IsTree
  let f := fun G : SimpleGraph (Fin n) ↦
    (G.induce (S : Set (Fin n)), G.induce (U : Set (Fin n)))
  let R := fun G : SimpleGraph (Fin n) ↦ IsClosedVertexSet G S ∧ IsClosedVertexSet G U
  have hsum := probability_sum_fibers lam n (TS ×ˢ TU) f R
  have hevent : (fun G ↦ IsTreeComponentSet G S ∧ IsTreeComponentSet G U) =
      (fun G ↦ f G ∈ TS ×ˢ TU ∧ R G) := by
    funext G
    apply propext
    simp only [f, R, TS, TU, Finset.mem_product, Finset.mem_filter,
      Finset.mem_univ, true_and, isTreeComponentSet_iff]
    tauto
  rw [hevent, hsum, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro H _
  apply Finset.sum_congr rfl
  intro J _
  congr 1
  funext G
  apply propext
  simp only [f, R, HasIsolatedInducedGraph, Prod.mk.injEq]
  tauto

/-- Exact correction for two disjoint tree-component events. -/
theorem probability_two_treeComponents_mul (lam : ℝ) (n : ℕ)
    {S U : Finset (Fin n)} (hSU : Disjoint S U) :
    probability lam n (fun G ↦ IsTreeComponentSet G S ∧ IsTreeComponentSet G U) *
        (1 - (edgeProbability lam n : ℝ)) ^ (S.card * U.card) =
      probability lam n (fun G ↦ IsTreeComponentSet G S) *
        probability lam n (fun G ↦ IsTreeComponentSet G U) := by
  rw [probability_two_treeComponents_eq_sum, Finset.sum_mul]
  simp_rw [Finset.sum_mul, probability_hasIsolatedInducedGraph_pair lam n hSU]
  rw [← Finset.sum_mul_sum, ← probability_isTreeComponentSet_eq_sum,
    ← probability_isTreeComponentSet_eq_sum]

theorem probability_two_treeComponents_div (lam : ℝ) (n : ℕ)
    {S U : Finset (Fin n)} (hSU : Disjoint S U)
    (hq : 1 - (edgeProbability lam n : ℝ) ≠ 0) :
    probability lam n (fun G ↦ IsTreeComponentSet G S ∧ IsTreeComponentSet G U) =
      (probability lam n (fun G ↦ IsTreeComponentSet G S) *
        probability lam n (fun G ↦ IsTreeComponentSet G U)) /
          (1 - (edgeProbability lam n : ℝ)) ^ (S.card * U.card) := by
  exact (eq_div_iff (pow_ne_zero _ hq)).mpr (probability_two_treeComponents_mul lam n hSU)

theorem probability_two_treeComponents_eq_zero (lam : ℝ) (n : ℕ)
    {S U : Finset (Fin n)} (hne : S ≠ U) (hSU : ¬Disjoint S U) :
    probability lam n (fun G ↦ IsTreeComponentSet G S ∧ IsTreeComponentSet G U) = 0 := by
  have hevent : (fun G ↦ IsTreeComponentSet G S ∧ IsTreeComponentSet G U) =
      (fun _ ↦ False) := by
    funext G
    apply propext
    constructor
    · rintro ⟨hS, hU⟩
      exact hSU (componentSets_disjoint_of_ne hS.1 hU.1 hne)
    · exact False.elim
  rw [hevent, probability_false]

end

end Erdos745
