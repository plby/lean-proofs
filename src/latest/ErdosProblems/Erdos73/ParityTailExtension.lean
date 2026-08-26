import ErdosProblems.Erdos73.ParityColoring
import ErdosProblems.Erdos73.OddCycleTails

/-! Extend a parity-breaking external path through two disjoint balanced tails. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem exists_parityBreaking_extension_supported {R T : Finset V} (c : BipartiteColoringOn G R)
    (U P Q : GraphPath G) (hU : IsParityBreakingPath c.color R U)
    (hPQ : Disjoint P.vertexSet Q.vertexSet)
    (hPR : P.vertexSet ⊆ R) (hQR : Q.vertexSet ⊆ R)
    (hPs : P.source = U.source) (hQs : Q.source = U.target)
    (hPt : P.target ∈ T) (hQt : Q.target ∈ T) :
    ∃ B : GraphPath G, IsParityBreakingPath c.color T B ∧
      B.vertexSet ⊆ P.vertexSet ∪ U.vertexSet ∪ Q.vertexSet := by
  have hPclean : ∀ x ∈ P.vertexSet, x ∈ U.vertexSet → x = P.source := by
    intro x hxP hxU
    rcases hU.internal_disjoint x hxU (hPR hxP) with hx | hx
    · exact hx.trans hPs.symm
    · have hxQ : x ∈ Q.vertexSet := (hx.trans hQs.symm) ▸ Q.source_mem_vertexSet
      exact (Finset.disjoint_left.mp hPQ hxP hxQ).elim
  have hQclean : ∀ x ∈ Q.vertexSet, x ∈ U.vertexSet → x = Q.source := by
    intro x hxQ hxU
    rcases hU.internal_disjoint x hxU (hQR hxQ) with hx | hx
    · have hxP : x ∈ P.vertexSet := (hx.trans hPs.symm) ▸ P.source_mem_vertexSet
      exact (Finset.disjoint_left.mp hPQ hxP hxQ).elim
    · exact hx.trans hQs.symm
  obtain ⟨B, hBs, hBt, hBsub, hBlen⟩ := join_disjoint_tails U.vertexSet P Q U hPQ
    hPclean hQclean subset_rfl hPs.symm hQs.symm
  have heP := c.even_walk P.walk (fun v hv => hPR (List.mem_toFinset.mpr hv))
  have heQ := c.even_walk Q.walk (fun v hv => hQR (List.mem_toFinset.mpr hv))
  have hbreak : ParityBreaking c.color B := by
    have ho := hU.breaking
    rw [ParityBreaking, Nat.odd_iff] at ho ⊢
    simp only [hBlen, hBs, hBt]
    simp only [Nat.even_iff, hPs] at heP
    simp only [Nat.even_iff, hQs] at heQ
    omega
  obtain ⟨D, hD, hDB⟩ := exists_parityBreaking_segment c.color T B
    (hBs ▸ hPt) (hBt ▸ hQt) hbreak
  exact ⟨D, hD, hDB.trans hBsub⟩

theorem exists_parityBreaking_extension {R T : Finset V} (c : BipartiteColoringOn G R)
    (U P Q : GraphPath G) (hU : IsParityBreakingPath c.color R U)
    (hPQ : Disjoint P.vertexSet Q.vertexSet)
    (hPR : P.vertexSet ⊆ R) (hQR : Q.vertexSet ⊆ R)
    (hPs : P.source = U.source) (hQs : Q.source = U.target)
    (hPt : P.target ∈ T) (hQt : Q.target ∈ T) :
    ∃ B : GraphPath G, IsParityBreakingPath c.color T B ∧
      B.vertexSet ⊆ R ∪ U.vertexSet := by
  obtain ⟨B, hB, hsub⟩ := exists_parityBreaking_extension_supported c U P Q hU hPQ
    hPR hQR hPs hQs hPt hQt
  refine ⟨B, hB, hsub.trans ?_⟩
  apply union_subset
  · exact union_subset_union hPR subset_rfl
  · exact hQR.trans subset_union_left

end
end Erdos73
