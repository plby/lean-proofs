import ErdosProblems.Erdos19.MaximumMatchingCoverage
import ErdosProblems.Erdos19.MatchingPartner

/-! # Covering a prescribed set without unnecessary matching edges -/

namespace Erdos19

open _root_.SimpleGraph

variable {V : Type*} {G : _root_.SimpleGraph V}

def trimMatching (M : G.Subgraph) (U : Set V) : G.Subgraph where
  verts := {v | ∃ w, M.Adj v w ∧ (v ∈ U ∨ w ∈ U)}
  Adj v w := M.Adj v w ∧ (v ∈ U ∨ w ∈ U)
  adj_sub := fun {_ _} h ↦ M.adj_sub h.1
  edge_vert := fun {_ _} h ↦ ⟨_, h.1, h.2⟩
  symm := ⟨by
    intro v w h
    exact ⟨h.1.symm, h.2.symm⟩⟩

theorem trimMatching_le (M : G.Subgraph) (U : Set V) : trimMatching M U ≤ M := by
  constructor
  · rintro v ⟨w, h, _⟩
    exact h.fst_mem
  · intro v w h
    exact h.1

theorem trimMatching_isMatching (M : G.Subgraph) (hM : M.IsMatching) (U : Set V) :
    (trimMatching M U).IsMatching := by
  intro v hv
  obtain ⟨w, hvw, hU⟩ := hv
  refine ⟨w, ⟨hvw, hU⟩, ?_⟩
  intro z hz
  exact hM.eq_of_adj_left hz.1 hvw

theorem trimMatching_covers (M : G.Subgraph) (hM : M.IsMatching) (U : Set V)
    (hU : U ⊆ M.verts) : U ⊆ (trimMatching M U).verts := by
  intro v hv
  obtain ⟨w, hvw, _⟩ := hM (hU hv)
  exact ⟨w, hvw, Or.inl hv⟩

theorem trimMatching_verts_subset (M : G.Subgraph) (hM : M.IsMatching) (U : Set V) :
    (trimMatching M U).verts ⊆ U ∪ matchingPartner M hM '' U := by
  rintro v ⟨w, hvw, hvU | hwU⟩
  · exact Or.inl hvU
  · right
    refine ⟨w, hwU, ?_⟩
    exact hM.eq_of_adj_left (matchingPartner_adj M hM hvw.snd_mem) hvw.symm

theorem trimMatching_verts_ncard_le [Fintype V] (M : G.Subgraph) (hM : M.IsMatching)
    (U : Set V) : (trimMatching M U).verts.ncard ≤ 2 * U.ncard := by
  have himage : (matchingPartner M hM '' U).ncard ≤ U.ncard := Set.ncard_image_le
  have hsub := Set.ncard_le_ncard (trimMatching_verts_subset M hM U)
  have hunion := Set.ncard_union_le U (matchingPartner M hM '' U)
  omega

theorem exists_small_matching_covering [Fintype V] (G : _root_.SimpleGraph V) (U : Set V)
    (hdegree : ∀ u ∈ U, U.ncard ≤ (G.neighborSet u).ncard) :
    ∃ M : G.Subgraph, M.IsMatching ∧ U ⊆ M.verts ∧
      M.verts.ncard ≤ 2 * U.ncard ∧ ∀ u v, M.Adj u v → u ∈ U ∨ v ∈ U := by
  obtain ⟨M, hM, hU, _⟩ := exists_maximum_matching_covering G U hdegree
  exact ⟨trimMatching M U, trimMatching_isMatching M hM U, trimMatching_covers M hM U hU,
    trimMatching_verts_ncard_le M hM U, fun _ _ h ↦ h.2⟩

theorem matching_verts_ncard_le_of_edges_meet [Fintype V] (M : G.Subgraph)
    (hM : M.IsMatching) (U : Set V) (hmeet : ∀ u v, M.Adj u v → u ∈ U ∨ v ∈ U) :
    M.verts.ncard ≤ 2 * U.ncard := by
  have hsub : M.verts ⊆ (trimMatching M U).verts := by
    intro v hv
    obtain ⟨w, hvw, _⟩ := hM hv
    exact ⟨w, hvw, hmeet v w hvw⟩
  exact (Set.ncard_le_ncard hsub).trans (trimMatching_verts_ncard_le M hM U)

#print axioms exists_small_matching_covering

end Erdos19
