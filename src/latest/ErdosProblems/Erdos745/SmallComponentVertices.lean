import ErdosProblems.Erdos745.ComponentUpper
import ErdosProblems.Erdos745.FixedComponentMean
import ErdosProblems.Erdos745.SmallMassSeries

/-! # Vertex accounting for the small-component mass -/

open Filter
open scoped BigOperators Topology

namespace Erdos745

noncomputable section

attribute [local instance] Classical.propDecidable

def smallComponentVertices {n : ℕ} (G : SimpleGraph (Fin n)) (K : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun r ↦ rootComponentOrder G r ≤ K)

theorem rootComponentOrder_mono {n : ℕ} {G H : SimpleGraph (Fin n)} (hGH : G ≤ H)
    (r : Fin n) : rootComponentOrder G r ≤ rootComponentOrder H r := by
  exact Set.ncard_mono ((H.connectedComponentMk r).connectedComponentMk_supp_subset_supp hGH
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem)

/-- Adding edges can only remove vertices from the union of small components. -/
theorem smallComponentVertices_antitone {n : ℕ} {G H : SimpleGraph (Fin n)} (hGH : G ≤ H)
    (K : ℕ) : smallComponentVertices H K ⊆ smallComponentVertices G K := by
  intro r hr
  have hrH := (Finset.mem_filter.mp hr).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (rootComponentOrder_mono hGH r).trans hrH⟩

theorem smallComponentVertices_eq_union {n : ℕ} (G : SimpleGraph (Fin n)) (K : ℕ) :
    smallComponentVertices G K =
      (Finset.univ.filter (fun C : G.ConnectedComponent ↦ C.supp.ncard ≤ K)).biUnion
        (fun C ↦ C.supp.toFinset) := by
  ext r
  simp only [smallComponentVertices, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_biUnion, Set.mem_toFinset]
  constructor
  · intro hr
    exact ⟨G.connectedComponentMk r, hr, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
  · rintro ⟨C, hC, hrC⟩
    have he := (C.mem_supp_iff r).mp hrC
    simpa only [rootComponentOrder, he] using hC

theorem smallComponentVertices_card_eq_components {n : ℕ} (G : SimpleGraph (Fin n)) (K : ℕ) :
    (smallComponentVertices G K).card =
      ∑ C ∈ Finset.univ.filter (fun C : G.ConnectedComponent ↦ C.supp.ncard ≤ K), C.supp.ncard := by
  rw [smallComponentVertices_eq_union, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro C _
    exact (Set.ncard_eq_toFinset_card' _).symm
  · intro C _ D _ hCD
    exact Set.disjoint_toFinset.mpr (G.pairwise_disjoint_supp_connectedComponent hCD)

theorem component_support_image {n : ℕ} (G : SimpleGraph (Fin n)) (I : Finset ℕ) :
    (Finset.univ.filter (fun C : G.ConnectedComponent ↦ C.supp.ncard ∈ I)).image
        (fun C ↦ C.supp.toFinset) =
      (vertexWindow n I).filter (IsComponentSet G) := by
  ext S
  constructor
  · intro hS
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hS
    apply Finset.mem_filter.mpr
    refine ⟨?_, C, by simp⟩
    have hCI := (Finset.mem_filter.mp hC).2
    simp only [vertexWindow, Finset.mem_filter, Finset.mem_powerset,
      Finset.subset_univ, true_and, ← Set.ncard_eq_toFinset_card']
    exact hCI
  · intro hS
    obtain ⟨hSwin, C, hC⟩ := Finset.mem_filter.mp hS
    have hsize : S.card ∈ I := (Finset.mem_filter.mp hSwin).2
    have heq : C.supp.toFinset = S := by
      apply Finset.coe_injective
      simpa using hC
    apply Finset.mem_image.mpr
    refine ⟨C, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, heq⟩
    simpa only [hC, Set.ncard_coe_finset] using hsize

theorem sum_component_orders_eq_vertex_sets {n : ℕ} (G : SimpleGraph (Fin n)) (I : Finset ℕ) :
    (∑ C ∈ Finset.univ.filter (fun C : G.ConnectedComponent ↦ C.supp.ncard ∈ I), C.supp.ncard) =
      ∑ S ∈ vertexWindow n I, if IsComponentSet G S then S.card else 0 := by
  rw [← Finset.sum_filter, ← component_support_image G I, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro C _
    exact Set.ncard_eq_toFinset_card' _
  · intro C _ D _ hCD
    exact component_support_toFinset_injective G hCD

theorem smallComponentVertices_card_eq_vertex_sets {n : ℕ}
    (G : SimpleGraph (Fin n)) (K : ℕ) :
    ((smallComponentVertices G K).card : ℝ) =
      ∑ S ∈ vertexWindow n (Finset.range (K + 1)),
        if IsComponentSet G S then (S.card : ℝ) else 0 := by
  have h := sum_component_orders_eq_vertex_sets G (Finset.range (K + 1))
  simp only [Finset.mem_range, Nat.lt_succ_iff] at h
  rw [← smallComponentVertices_card_eq_components] at h
  exact_mod_cast h

theorem expectation_component_indicator (lam : ℝ) (n : ℕ) (S : Finset (Fin n)) :
    expectation lam n (fun G ↦ if IsComponentSet G S then (S.card : ℝ) else 0) =
      (S.card : ℝ) * probability lam n (fun G ↦ IsComponentSet G S) := by
  have heq : (fun G ↦ if IsComponentSet G S then (S.card : ℝ) else 0) =
      (fun G ↦ (S.card : ℝ) * (if IsComponentSet G S then 1 else 0)) := by
    funext G
    split_ifs <;> simp
  rw [heq, expectation_const_mul, expectation_indicator]

/-- Exact finite expectation identity for the number of vertices in small components. -/
theorem expectation_smallComponentVertices (lam : ℝ) (n K : ℕ) :
    expectation lam n (fun G ↦ ((smallComponentVertices G K).card : ℝ)) =
      ∑ k ∈ Finset.range (K + 1), (k : ℝ) * componentMean lam n k := by
  simp_rw [smallComponentVertices_card_eq_vertex_sets]
  rw [expectation_finset_sum]
  simp only [expectation_component_indicator]
  rw [sum_vertexWindow]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = ∑ S ∈ Finset.univ.powersetCard k,
        (k : ℝ) * probability lam n (fun G ↦ IsComponentSet G S) := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [(Finset.mem_powersetCard.mp hS).2]
    _ = _ := by rw [componentMean, Finset.mul_sum]

theorem tendsto_smallComponentVertices_mean {lam : ℝ} (hlam : 0 ≤ lam) (K : ℕ) :
    Tendsto (fun n ↦ expectation lam n (fun G ↦ ((smallComponentVertices G K).card : ℝ)) / n)
      atTop (𝓝 (∑ k ∈ Finset.range (K + 1), smallMassTerm lam k)) := by
  simp only [expectation_smallComponentVertices, Finset.sum_div]
  apply tendsto_finsetSum
  intro k _
  by_cases hk : k = 0
  · subst k
    simp [smallMassTerm]
  · have ht := (tendsto_componentMean_div hlam (Nat.pos_of_ne_zero hk)).const_mul (k : ℝ)
    simpa only [smallMassTerm, mul_div_assoc] using ht

end

end Erdos745
