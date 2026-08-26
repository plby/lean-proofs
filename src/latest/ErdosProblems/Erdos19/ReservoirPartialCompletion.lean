import ErdosProblems.Erdos19.BufferedPartialCompletion
import ErdosProblems.Erdos19.BlockReservoir
import ErdosProblems.Erdos19.PaletteCoverageCounts

/-! # Exact completion from an almost unused block reservoir -/

namespace Erdos19

open _root_.SimpleGraph

variable {V I : Type*} [Fintype V]

theorem missing_neighbors_after_reservoir_use (G used : _root_.SimpleGraph V)
    (X : Set V) (v : V) :
    (X \ (G \ used).neighborSet v).ncard ≤
      (X \ G.neighborSet v).ncard + ((G ⊓ used).neighborSet v).ncard := by
  have hsub : X \ (G \ used).neighborSet v ⊆
      (X \ G.neighborSet v) ∪ (G ⊓ used).neighborSet v := by
    intro w hw
    by_cases hG : G.Adj v w
    · right
      refine ⟨hG, ?_⟩
      by_contra hused
      exact hw.2 ⟨hG, hused⟩
    · exact Or.inl ⟨hw.1, hG⟩
  exact (Set.ncard_le_ncard hsub).trans (Set.ncard_union_le _ _)

namespace SetHypergraph

attribute [local instance] Classical.propDecidable

theorem edgeColorable_of_block_reservoir_coloring (H J : SetHypergraph V)
    (hJH : J ⊆ H) (hlinear : H.IsLinear) (hmin : ∀ e : H, 2 ≤ e.1.ncard)
    (hpair : ∀ e ∈ H, e ∉ J → e.ncard = 2)
    (m D : ℕ) (hD : 0 < D) (hvertices : Fintype.card V = m + D)
    (color : J.EdgeColoring (Fin m)) (p : ℕ) (index : Fin p ↪ Fin m) (bad : Fin m)
    (U Y Z : Set V) (hUY : Disjoint U Y) (z : V → I)
    (used : _root_.SimpleGraph V)
    (hrest : (H \ J).twoGraph = insideBlocks H.twoGraph z \ used)
    (missing load requests : ℕ)
    (hmissing : ∀ v ∈ U, (H.twoGraph.neighborSet v)ᶜ.ncard ≤ missing)
    (hload : ∀ v ∈ U,
      ((insideBlocks H.twoGraph z ⊓ used).neighborSet v).ncard ≤ load)
    (hrequestDegree : ∀ v ∈ U,
      m + ((insideBlocks H.twoGraph z).neighborSet v).ncard ≤
        (H.twoGraph.neighborSet v).ncard + requests)
    (B : Fin p → I → Set V)
    (hBY : ∀ i j, B i j ⊆ Y) (hBX : ∀ i j v, v ∈ B i j → z v = j)
    (hBavoid : ∀ i j, Disjoint (B i j) (J.coveredVertices {e | color e = index i}))
    (hBsize : ∀ i j, missing + load + requests ≤ (B i j).ncard)
    (hinactive : ∀ a, a ∉ Set.range index → ∀ v ∈ U,
      v ∉ Z ∨ a ≠ bad → v ∈ J.coveredVertices {e | color e = a})
    (houtside : ∀ v, v ∉ U → ((insideBlocks H.twoGraph z).neighborSet v).ncard < D)
    (hindependent : ∀ x ∈ Z, ∀ y ∈ Z, ¬H.twoGraph.Adj x y) :
    H.EdgeColorable (m + D) := by
  classical
  let R := insideBlocks H.twoGraph z
  let X : I → Set V := fun j ↦ {v | z v = j}
  have hresLe : (H \ J).twoGraph ≤ R := by rw [hrest]; exact sdiff_le
  have hinc : ∀ v ∈ U, m ≤ (J.incidentEdges v).ncard + requests := by
    intro v hv
    have h := H.graph_degree_le_colored_incidence_add_residual J hJH R hresLe v
    have h' := hrequestDegree v hv
    change m + (R.neighborSet v).ncard ≤ _ at h'
    omega
  have hrequests := J.active_requests_le_of_incident_lower m p color index U requests hinc
  apply H.edgeColorable_of_buffered_partial_coloring J hJH hlinear hmin hpair
    m D hD hvertices color p index bad U Y Z hUY X
    (fun i j hij ↦ Set.disjoint_left.mpr (fun _ hi hj ↦ hij (hi.symm.trans hj)))
    (fun v ↦ ⟨z v, rfl⟩) (missing + load) requests B hBY hBX hBavoid hBsize
    ?_ hrequests hinactive ?_ hindependent
  · intro i j u hu
    let T := ((U \ J.coveredVertices {e | color e = index i}) ∩ X j) ∪ B i j
    have hT : ∀ v ∈ T, z v = j := by
      intro v hv
      exact hv.elim (fun h ↦ h.2) (hBX i j v)
    have hlocal : (T \ R.neighborSet u).ncard ≤ missing := by
      rw [insideBlocks_missing_on_block H.twoGraph z j T hT u hu.2]
      exact (Set.ncard_le_ncard (show T \ H.twoGraph.neighborSet u ⊆
        (H.twoGraph.neighborSet u)ᶜ from fun _ h ↦ h.2)).trans (hmissing u hu.1.1)
    rw [hrest]
    exact (missing_neighbors_after_reservoir_use R used T u).trans
      (Nat.add_le_add hlocal (hload u hu.1.1))
  · intro v hv
    exact (_root_.SimpleGraph.degree_le_of_le hresLe).trans_lt (by
      rw [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]
      exact houtside v hv)

#print axioms edgeColorable_of_block_reservoir_coloring

end SetHypergraph
end Erdos19
