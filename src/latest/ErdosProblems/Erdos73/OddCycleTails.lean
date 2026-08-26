import ErdosProblems.Erdos73.OddCycleArcs
import ErdosProblems.Erdos73.OddTerminalSegments
import ErdosProblems.Erdos73.MengerDefs

/-! Two disjoint tails from an odd cycle give an odd terminal path. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem join_disjoint_tails (S : Finset V) (P Q L : GraphPath G)
    (hPQ : Disjoint P.vertexSet Q.vertexSet)
    (hP : ∀ x ∈ P.vertexSet, x ∈ S → x = P.source)
    (hQ : ∀ x ∈ Q.vertexSet, x ∈ S → x = Q.source)
    (hL : L.vertexSet ⊆ S) (hs : L.source = P.source) (ht : L.target = Q.source) :
    ∃ B : GraphPath G, B.source = P.target ∧ B.target = Q.target ∧
      B.vertexSet ⊆ P.vertexSet ∪ S ∪ Q.vertexSet ∧
      B.walk.length = P.walk.length + L.walk.length + Q.walk.length := by
  have hinter : ∀ ⦃x⦄, x ∈ P.reverse.vertexSet → x ∈ L.vertexSet → x = P.reverse.target := by
    intro x hx hy
    exact hP x (by simpa using hx) (hL hy)
  let A := P.reverse.appendWithEqOfInterSubsetTarget L hs.symm hinter
  have hAsub : A.vertexSet ⊆ P.vertexSet ∪ S := by
    intro x hx
    have hh := GraphPath.appendWithEq_vertexSet_subset P.reverse L hs.symm
      (P.reverse.appendWithEq_isPath_of_inter_subset_target L hs.symm hinter) hx
    rcases mem_union.mp hh with hh | hh
    · exact mem_union_left _ (by simpa using hh)
    · exact mem_union_right _ (hL hh)
  have hinter' : ∀ ⦃x⦄, x ∈ A.vertexSet → x ∈ Q.vertexSet → x = A.target := by
    intro x hx hy
    rcases mem_union.mp (hAsub hx) with hx | hx
    · exact (Finset.disjoint_left.mp hPQ hx hy).elim
    · exact (hQ x hy hx).trans ht.symm
  let B := A.appendWithEqOfInterSubsetTarget Q ht hinter'
  refine ⟨B, rfl, rfl, ?_, ?_⟩
  · exact (GraphPath.appendWithEq_vertexSet_subset A Q ht
      (A.appendWithEq_isPath_of_inter_subset_target Q ht hinter')).trans
      (Finset.union_subset_union hAsub subset_rfl)
  · simp only [B, A, GraphPath.appendWithEqOfInterSubsetTarget, GraphPath.appendWithEq,
      GraphPath.reverse, Walk.length_append, Walk.length_copy, Walk.length_reverse]

theorem IsOddCycleSubgraph.exists_oddTerminalPath_of_two_clean_tails
    {H : G.Subgraph} (hH : IsOddCycleSubgraph H) (N : Finset V) (P Q : GraphPath G)
    (hP : P.EndpointClean H.verts.toFinset N)
    (hQ : Q.EndpointClean H.verts.toFinset N)
    (hPQ : Disjoint P.vertexSet Q.vertexSet) :
    ∃ B : GraphPath G, IsOddTerminalPath N B ∧
      B.vertexSet ⊆ P.vertexSet ∪ H.verts.toFinset ∪ Q.vertexSet := by
  have hne : P.source ≠ Q.source := by
    intro he
    exact Finset.disjoint_left.mp hPQ P.source_mem_vertexSet
      (he ▸ Q.source_mem_vertexSet)
  obtain ⟨L, R, hLs, hLt, hRs, hRt, hL, hR, ho⟩ :=
    hH.exists_oppositeParity_paths (Set.mem_toFinset.mp hP.source_mem)
      (Set.mem_toFinset.mp hQ.source_mem) hne
  obtain ⟨B, hBs, hBt, hBsub, hBlen⟩ := join_disjoint_tails H.verts.toFinset P Q L hPQ
    (fun _ hx hy => hP.left_eq_source hx hy) (fun _ hx hy => hQ.left_eq_source hx hy)
    hL hLs hLt
  obtain ⟨C, hCs, hCt, hCsub, hClen⟩ := join_disjoint_tails H.verts.toFinset P Q R hPQ
    (fun _ hx hy => hP.left_eq_source hx hy) (fun _ hx hy => hQ.left_eq_source hx hy)
    hR hRs hRt
  have hparity : Odd B.walk.length ∨ Odd C.walk.length := by
    rw [Nat.odd_iff] at ho ⊢
    rw [Nat.odd_iff]
    omega
  rcases hparity with hBodd | hCodd
  · obtain ⟨D, hD, hDsub⟩ := exists_oddTerminalSegment N B
      (hBs ▸ hP.target_mem) (hBt ▸ hQ.target_mem) hBodd
    exact ⟨D, hD, hDsub.trans hBsub⟩
  · obtain ⟨D, hD, hDsub⟩ := exists_oddTerminalSegment N C
      (hCs ▸ hP.target_mem) (hCt ▸ hQ.target_mem) hCodd
    exact ⟨D, hD, hDsub.trans hCsub⟩

theorem IsOddCycleSubgraph.exists_oddTerminalPath_of_two_paths
    {H : G.Subgraph} (hH : IsOddCycleSubgraph H) (N : Finset V)
    (hpaths : HasDisjointSTPaths G H.verts.toFinset N 2) :
    ∃ B : GraphPath G, IsOddTerminalPath N B := by
  obtain ⟨P, hP⟩ := hpaths
  let Q := P.toEndpointClean
  have hcard : 2 ≤ Fintype.card Q.Index := hP
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card Q.Index)
  obtain ⟨B, hB, _⟩ := hH.exists_oddTerminalPath_of_two_clean_tails N (Q.path i) (Q.path j)
    (Q.endpoint_clean i) (Q.endpoint_clean j) (Q.node_disjoint hij)
  exact ⟨B, hB⟩

end
end Erdos73
