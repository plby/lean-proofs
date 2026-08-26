import ErdosProblems.Erdos73.BrickHorizontalPaths
import ErdosProblems.Erdos73.ColumnHandleFamilies
import ErdosProblems.Erdos73.ParityReturnPaths

/-! Handles on distinct single rows close to vertex-disjoint odd cycles. -/

namespace Erdos73.ColumnHandleFamily
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {c r k : ℕ}
variable {S : GraphSubdivisionModel (elementaryWall c r) G}
variable {col : BipartiteColoringOn G S.vertexSet}

theorem oddCyclePacking_of_same_row (F : ColumnHandleFamily S col (Fin k))
    (hsame : ∀ i, (F.sourceNail i).val.1 = (F.targetNail i).val.1)
    (hrows : Pairwise (fun i j => (F.sourceNail i).val.1 ≠ (F.sourceNail j).val.1)) :
    HasOddCyclePacking k G := by
  let R (i : Fin k) := S.supportOver (brickRowVertices (F.sourceNail i).val.1)
  have hR : Pairwise (fun i j => Disjoint (R i) (R j)) :=
    fun i j hij => S.supportOver_disjoint (brickRowVertices_disjoint (hrows hij))
  have hRW (i : Fin k) : R i ⊆ S.vertexSet := S.supportOver_mono (subset_univ _)
  have hex (i : Fin k) : ∃ Q : GraphPath G,
      Q.source = S.branchVertex (F.sourceNail i) ∧
      Q.target = S.branchVertex (F.targetNail i) ∧ Q.vertexSet ⊆ R i :=
    S.exists_horizontal_path (F.sourceNail i) (F.targetNail i) (hsame i)
  choose Q hQs hQt hQ using hex
  have hsource (i : Fin k) : (F.path i).source ∈ R i := by
    rw [F.source_eq]
    exact (S.mem_supportOver _ _).mpr (Or.inl
      ⟨F.sourceNail i, mem_filter.mpr ⟨mem_univ _, rfl⟩, rfl⟩)
  have htarget (i : Fin k) : (F.path i).target ∈ R i := by
    rw [F.target_eq]
    exact (S.mem_supportOver _ _).mpr (Or.inl
      ⟨F.targetNail i, mem_filter.mpr ⟨mem_univ _, (hsame i).symm⟩, rfl⟩)
  have hPQ {i j : Fin k} (hij : i ≠ j) : Disjoint (F.path i).vertexSet (Q j).vertexSet := by
    apply Finset.disjoint_left.mpr
    intro x hxP hxQ
    have hxR := hQ j hxQ
    have hxW := hRW j hxR
    rcases (F.clean i).internal_disjoint x hxP hxW with rfl | rfl
    · exact Finset.disjoint_left.mp (hR hij) (hsource i) hxR
    · exact Finset.disjoint_left.mp (hR hij) (htarget i) hxR
  let M : DisjointNonbipartiteRegions k G := {
    region := fun i => (F.path i).vertexSet ∪ (Q i).vertexSet
    pairwise_disjoint := by
      intro i j hij
      exact Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_union_right.mpr ⟨F.disjoint hij, hPQ hij⟩,
          Finset.disjoint_union_right.mpr
            ⟨(hPQ hij.symm).symm, (hR hij).mono (hQ i) (hQ j)⟩⟩
    nonbipartite := fun i => not_bipartite_union_of_parityBreaking col (F.path i) (Q i)
      (F.clean i).breaking ((F.source_eq i).trans (hQs i).symm)
      ((F.target_eq i).trans (hQt i).symm) ((hQ i).trans (hRW i)) }
  exact M.hasOddCyclePacking

end
end Erdos73.ColumnHandleFamily
