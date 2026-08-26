import ErdosProblems.Erdos73.OddCycleTails
import ErdosProblems.Erdos73.OddPathRegion
import ErdosProblems.Erdos73.Menger

/-! Order-one cuts between odd cycles and terminals, localized to an induced region. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem IsOddCycleSubgraph.exists_terminal_separator {H : G.Subgraph}
    (hH : IsOddCycleSubgraph H) (N : Finset V)
    (hno : ¬ ∃ P : GraphPath G, IsOddTerminalPath N P) :
    ∃ Y : Finset V, Y.card ≤ 1 ∧ STSeparator G H.verts.toFinset N Y := by
  rcases Menger.finite_vertex_menger_sharp G H.verts.toFinset N 2 with hpaths | ⟨Y, hY, hsep⟩
  · exact (hno (hH.exists_oddTerminalPath_of_two_paths N hpaths)).elim
  · exact ⟨Y, by omega, hsep⟩

theorem exists_oddCycle_region_separator (N R : Finset V)
    (hR : ¬ (G.induce (R : Set V)).IsBipartite)
    (hno : ¬ ∃ P : GraphPath (G.induce (R : Set V)),
      IsOddTerminalPath (regionTerminals N R) P) :
    ∃ H : G.Subgraph, IsOddCycleSubgraph H ∧ H.verts ⊆ (R : Set V) ∧
      ∃ Y : Finset V, Y ⊆ R ∧ Y.card ≤ 1 ∧
        ∀ S : Finset V, S ⊆ R → (G.induce (S : Set V)).Connected →
          Disjoint S Y → (∃ v ∈ S, v ∈ N) → Disjoint (S : Set V) H.verts := by
  have hex : ∃ H : (G.induce (R : Set V)).Subgraph, IsOddCycleSubgraph H := by
    by_contra hnone
    exact hR ((isBipartite_iff_no_oddCycleSubgraph _).mpr hnone)
  obtain ⟨H, hH⟩ := hex
  obtain ⟨Z, hZ, hsep⟩ := hH.exists_terminal_separator (regionTerminals N R) hno
  let f : G.induce (R : Set V) ↪g G := Embedding.induce (R : Set V)
  let K := H.map f.toHom
  let Y := Z.image Subtype.val
  refine ⟨K, hH.map_embedding f, ?_, Y, ?_, ?_, ?_⟩
  · rintro v ⟨w, _, rfl⟩
    exact w.property
  · intro v hv
    obtain ⟨w, _, rfl⟩ := mem_image.mp hv
    exact w.property
  · exact (card_image_le).trans hZ
  · intro S hSR hS hSY hSN
    apply Set.disjoint_left.mpr
    intro v hvS hvK
    obtain ⟨w, hwH, hwv⟩ := hvK
    obtain ⟨n, hnS, hnN⟩ := hSN
    let P := GraphPath.ofConnectedInduce S hS v n hvS hnS
    have hPS : P.vertexSet ⊆ S := GraphPath.ofConnectedInduce_vertexSet_subset S hS v n hvS hnS
    let Q := P.induce R (hPS.trans hSR)
    have hQs : Q.source ∈ H.verts.toFinset := by
      have he : Q.source = w := Subtype.ext hwv.symm
      exact Set.mem_toFinset.mpr (he ▸ hwH)
    have hQt : Q.target ∈ regionTerminals N R := (mem_regionTerminals _ _ _).mpr hnN
    obtain ⟨z, hzQ, hzZ⟩ := hsep Q (Or.inl ⟨hQs, hQt⟩)
    have hzP : z.val ∈ P.vertexSet := (P.mem_induce_vertexSet _ _ z).mp hzQ
    exact Finset.disjoint_left.mp hSY (hPS hzP) (mem_image.mpr ⟨z, hzZ, rfl⟩)

end
end Erdos73
