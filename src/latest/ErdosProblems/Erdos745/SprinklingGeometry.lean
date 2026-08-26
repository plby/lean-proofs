import ErdosProblems.Erdos745.SmallComponentVertices

/-! # Deterministic component geometry for sprinkling -/

open scoped BigOperators

namespace Erdos745

noncomputable section

attribute [local instance] Classical.propDecidable

def largeBaseComponents {n : ℕ} (G : SimpleGraph (Fin n)) (K : ℕ) : Finset G.ConnectedComponent :=
  Finset.univ.filter (fun C ↦ K < C.supp.ncard)

def componentUnion {n : ℕ} {G : SimpleGraph (Fin n)} (J : Finset G.ConnectedComponent) :
    Finset (Fin n) := J.biUnion (fun C ↦ C.supp.toFinset)

theorem componentUnion_card {n : ℕ} {G : SimpleGraph (Fin n)} (J : Finset G.ConnectedComponent) :
    (componentUnion J).card = ∑ C ∈ J, C.supp.ncard := by
  rw [componentUnion, Finset.card_biUnion]
  · exact Finset.sum_congr rfl (fun C _ ↦ (Set.ncard_eq_toFinset_card' _).symm)
  · intro C _ D _ hCD
    exact Set.disjoint_toFinset.mpr (G.pairwise_disjoint_supp_connectedComponent hCD)

theorem largeBaseComponents_budget {n : ℕ} (G : SimpleGraph (Fin n)) (K : ℕ) :
    (K + 1) * (largeBaseComponents G K).card ≤ n := by
  calc
    _ = ∑ _C ∈ largeBaseComponents G K, (K + 1) := by simp [mul_comm]
    _ ≤ ∑ C ∈ largeBaseComponents G K, C.supp.ncard :=
      Finset.sum_le_sum (fun C hC ↦ (Finset.mem_filter.mp hC).2)
    _ = (componentUnion (largeBaseComponents G K)).card := (componentUnion_card _).symm
    _ ≤ n := by simpa using Finset.card_le_univ (componentUnion (largeBaseComponents G K))

/-- The large base components contained in one component of the final graph. -/
def componentsInside {n : ℕ} (G H : SimpleGraph (Fin n)) (K : ℕ) (C : H.ConnectedComponent) :
    Finset G.ConnectedComponent :=
  (largeBaseComponents G K).filter (fun D ↦ D.supp ⊆ C.supp)

theorem componentUnion_inside_eq {n : ℕ} {G H : SimpleGraph (Fin n)} (hGH : G ≤ H)
    (K : ℕ) (C : H.ConnectedComponent) :
    componentUnion (componentsInside G H K C) = C.supp.toFinset \ smallComponentVertices G K := by
  ext r
  simp only [componentUnion, componentsInside, Finset.mem_biUnion, Finset.mem_filter,
    largeBaseComponents, Finset.mem_univ, true_and, Set.mem_toFinset,
    Finset.mem_sdiff, smallComponentVertices, not_le]
  constructor
  · rintro ⟨D, ⟨hD, hDC⟩, hrD⟩
    have hrEq := (D.mem_supp_iff r).mp hrD
    refine ⟨hDC hrD, ?_⟩
    simpa only [rootComponentOrder, hrEq] using hD
  · rintro ⟨hrC, hrLarge⟩
    refine ⟨G.connectedComponentMk r, ⟨hrLarge, ?_⟩,
      SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
    exact C.connectedComponentMk_supp_subset_supp hGH hrC

theorem large_component_disjoint_small {n K : ℕ} (H : SimpleGraph (Fin n))
    (C : H.ConnectedComponent) (hC : K < C.supp.ncard) :
    Disjoint C.supp.toFinset (smallComponentVertices H K) := by
  rw [Finset.disjoint_left]
  intro r hrC hrSmall
  have hrEq := (C.mem_supp_iff r).mp (Set.mem_toFinset.mp hrC)
  have hrK := (Finset.mem_filter.mp hrSmall).2
  have : C.supp.ncard ≤ K := by simpa only [rootComponentOrder, hrEq] using hrK
  omega

/-- A large final component retains all but at most the global small-vertex loss. -/
theorem componentUnion_inside_card_lower {n K : ℕ} {G H : SimpleGraph (Fin n)} (hGH : G ≤ H)
    (C : H.ConnectedComponent) (hC : K < C.supp.ncard) :
    (C.supp.ncard : ℝ) - ((smallComponentVertices G K \ smallComponentVertices H K).card : ℝ) ≤
      ((componentUnion (componentsInside G H K C)).card : ℝ) := by
  have hdis := large_component_disjoint_small H C hC
  have hsub : C.supp.toFinset ∩ smallComponentVertices G K ⊆
      smallComponentVertices G K \ smallComponentVertices H K := by
    intro r hr
    obtain ⟨hrC, hrG⟩ := Finset.mem_inter.mp hr
    exact Finset.mem_sdiff.mpr ⟨hrG, fun hrH ↦ Finset.disjoint_left.mp hdis hrC hrH⟩
  have hle := Finset.card_le_card hsub
  have heq := Finset.card_sdiff_add_card_inter C.supp.toFinset (smallComponentVertices G K)
  rw [← Set.ncard_eq_toFinset_card'] at heq
  rw [componentUnion_inside_eq hGH]
  have hnat : C.supp.ncard ≤ (C.supp.toFinset \ smallComponentVertices G K).card +
      (smallComponentVertices G K \ smallComponentVertices H K).card := by omega
  have hreal : (C.supp.ncard : ℝ) ≤ ((C.supp.toFinset \ smallComponentVertices G K).card : ℝ) +
      ((smallComponentVertices G K \ smallComponentVertices H K).card : ℝ) := by exact_mod_cast hnat
  linarith

theorem componentUnion_inside_subset {n K : ℕ} (G H : SimpleGraph (Fin n))
    (C : H.ConnectedComponent) :
    componentUnion (componentsInside G H K C) ⊆ C.supp.toFinset := by
  intro r hr
  obtain ⟨D, hD, hrD⟩ := Finset.mem_biUnion.mp hr
  have hDC := (Finset.mem_filter.mp hD).2
  exact Set.mem_toFinset.mpr (hDC (Set.mem_toFinset.mp hrD))

theorem componentUnion_inside_disjoint {n K : ℕ} (G H : SimpleGraph (Fin n))
    (C D : H.ConnectedComponent) (hCD : C ≠ D) :
    Disjoint (componentUnion (componentsInside G H K C))
      (componentUnion (componentsInside G H K D)) := by
  exact (Set.disjoint_toFinset.mpr (H.pairwise_disjoint_supp_connectedComponent hCD)).mono
    (componentUnion_inside_subset G H C) (componentUnion_inside_subset G H D)

theorem crossingEdges_avoided_of_components {n : ℕ} (H : SimpleGraph (Fin n))
    (C D : H.ConnectedComponent) (hCD : C ≠ D) (S T : Finset (Fin n))
    (hS : S ⊆ C.supp.toFinset) (hT : T ⊆ D.supp.toFinset) (hST : Disjoint S T)
    (B : Finset (Edge n)) (hB : B ⊆ edgeCoordinates H) :
    Disjoint (Erdos746.crossingEdges S T hST) B := by
  rw [Finset.disjoint_left]
  intro e he heB
  obtain ⟨u, hu, v, hv, heq⟩ := (Erdos746.mem_crossingEdges_iff hST e).mp he
  have hadj := hB heB
  rw [mem_edgeCoordinates, heq, SimpleGraph.mem_edgeSet] at hadj
  have huC : u ∈ C.supp := Set.mem_toFinset.mp (hS hu)
  have hvD : v ∈ D.supp := Set.mem_toFinset.mp (hT hv)
  exact hCD (SimpleGraph.ConnectedComponent.eq_of_common_vertex
    (C.mem_supp_of_adj_mem_supp huC hadj) hvD)

end

end Erdos745
