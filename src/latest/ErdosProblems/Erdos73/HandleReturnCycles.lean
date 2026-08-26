import ErdosProblems.Erdos73.ColumnHandleFamilies
import ErdosProblems.Erdos73.ParityReturnPaths

/-! Disjoint return paths inside the balanced wall close the handles to odd cycles. -/

namespace Erdos73.ColumnHandleFamily
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {c r k : ℕ}
variable {S : GraphSubdivisionModel (elementaryWall c r) G}
variable {col : BipartiteColoringOn G S.vertexSet}

theorem oddCyclePacking_of_disjoint_return_paths (F : ColumnHandleFamily S col (Fin k))
    (Q : Fin k → GraphPath G) (hs : ∀ i, (Q i).source = (F.path i).source)
    (ht : ∀ i, (Q i).target = (F.path i).target)
    (hQW : ∀ i, (Q i).vertexSet ⊆ S.vertexSet)
    (hQQ : Pairwise (fun i j => Disjoint (Q i).vertexSet (Q j).vertexSet)) :
    HasOddCyclePacking k G := by
  have hPQ {i j : Fin k} (hij : i ≠ j) : Disjoint (F.path i).vertexSet (Q j).vertexSet := by
    apply Finset.disjoint_left.mpr
    intro x hxP hxQ
    rcases (F.clean i).internal_disjoint x hxP (hQW j hxQ) with rfl | rfl
    · apply Finset.disjoint_left.mp (hQQ hij) _ hxQ
      rw [← hs]
      exact (Q i).source_mem_vertexSet
    · apply Finset.disjoint_left.mp (hQQ hij) _ hxQ
      rw [← ht]
      exact (Q i).target_mem_vertexSet
  let M : DisjointNonbipartiteRegions k G := {
    region := fun i => (F.path i).vertexSet ∪ (Q i).vertexSet
    pairwise_disjoint := by
      intro i j hij
      exact Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_union_right.mpr ⟨F.disjoint hij, hPQ hij⟩,
          Finset.disjoint_union_right.mpr ⟨(hPQ hij.symm).symm, hQQ hij⟩⟩
    nonbipartite := fun i => not_bipartite_union_of_parityBreaking col (F.path i) (Q i)
      (F.clean i).breaking (hs i).symm (ht i).symm (hQW i) }
  exact M.hasOddCyclePacking

end
end Erdos73.ColumnHandleFamily
