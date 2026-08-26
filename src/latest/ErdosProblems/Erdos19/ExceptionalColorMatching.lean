import ErdosProblems.Erdos19.MaximumMatchingCoverage
import ErdosProblems.Erdos19.SubgraphLift

/-! # Starting the exceptional color with an independent uncovered set -/

namespace Erdos19

open _root_.SimpleGraph

variable {V : Type*} [Fintype V]

theorem exists_matching_avoiding_with_independent_remainder (G : _root_.SimpleGraph V)
    (C : Set V) :
    ∃ M : G.Subgraph, M.IsMatching ∧ Disjoint M.verts C ∧
      ∀ x y, x ∉ C → y ∉ C → x ∉ M.verts → y ∉ M.verts → ¬G.Adj x y := by
  let Q : _root_.SimpleGraph V :=
    { Adj := fun x y ↦ G.Adj x y ∧ x ∉ C ∧ y ∉ C
      symm := ⟨by intro x y h; exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
      loopless := ⟨by intro x h; exact h.1.ne rfl⟩ }
  have hQG : Q ≤ G := fun _ _ h ↦ h.1
  obtain ⟨M, hM, _, hmax⟩ := exists_maximum_matching_covering Q ∅
    (fun u hu ↦ (Set.notMem_empty u hu).elim)
  refine ⟨liftSubgraph hQG M, hM, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro v hv hvC
    obtain ⟨w, hvw, _⟩ := hM hv
    exact (M.adj_sub hvw).2.1 hvC
  · intro x y hxC hyC hxM hyM hxy
    apply maximum_matching_unmatched_pairwise_not_adj M hM hmax hxM hyM hxy.ne
    exact ⟨hxy, hxC, hyC⟩

#print axioms exists_matching_avoiding_with_independent_remainder

end Erdos19
