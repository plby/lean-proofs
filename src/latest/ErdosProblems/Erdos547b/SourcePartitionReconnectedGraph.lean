/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceReconnectedGraph
import ErdosProblems.Erdos547b.Lemma58CutForestReconstruction

/-!
# The reconnected coordinate graph is the original source tree
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePartitionReconnectedGraph

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceReconnectedGraph Erdos547b.ZhaoSourcePartitionCutCoordinates
open Erdos547b.ZhaoLemma58CutForestReconstruction Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoSourceGlobalPrefixState Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim616HierarchyAttachments

variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable {globalRoot : U} {small : ℕ} (P : ZhaoForestPartition T globalRoot small)

theorem cutBranchGraphIso_coordinateVertex (x : (branchForest P).Vertex) :
    cutBranchGraphIso P (coordinateVertex P x) = x := by
  cases x with
  | inl i => exact cutBranchGraphIso_root P i
  | inr a =>
      change cutBranchGraphIso P (partitionBranchEquivNonroots P a).1 = _
      rw [cutBranchGraphIso_nonroot P _ (partitionBranchEquivNonroots P a).2,
        (partitionBranchEquivNonroots P).symm_apply_apply]

theorem cutBranchGraphIso_parent (i : Fin P.numParts) (hi : i.val ≠ 0) :
    cutBranchGraphIso P (P.parent i hi) = partitionParent P i hi := by
  rw [← partitionParent_vertex]
  exact cutBranchGraphIso_coordinateVertex P _

variable (hT : T.IsTree) {k : ℕ}
variable (locate : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin 2 × Fin k)
variable (hlocate : ∀ i, (locate i).1 = componentReservoirSide P ((branchForest P).owner i))

theorem reconnected_adj_iff_tree (x y : U) :
    (reconnectedGraph (branchForest P) (partitionCutSource P hT locate hlocate)).Adj
      (cutBranchGraphIso P x) (cutBranchGraphIso P y) ↔ T.Adj x y := by
  constructor
  · intro h
    rcases h with h | ⟨i, hi, h | h⟩
    · have hc := (cutBranchGraphIso P).symm.toHom.map_rel h
      have hxy : P.cutForest.Adj x y := by
        change P.cutForest.Adj ((cutBranchGraphIso P).symm (cutBranchGraphIso P x))
          ((cutBranchGraphIso P).symm (cutBranchGraphIso P y)) at hc
        simpa only [(cutBranchGraphIso P).symm_apply_apply] using hc
      exact (SimpleGraph.deleteEdges_adj.mp hxy).1
    · have hx : x = P.parent i hi := (cutBranchGraphIso P).injective
        (h.1.trans (cutBranchGraphIso_parent P i hi).symm)
      have hy : y = P.roots i := (cutBranchGraphIso P).injective
        (h.2.trans (cutBranchGraphIso_root P i).symm)
      subst x
      subst y
      exact (P.cut_adj i hi).symm
    · have hy : y = P.parent i hi := (cutBranchGraphIso P).injective
        (h.1.trans (cutBranchGraphIso_parent P i hi).symm)
      have hx : x = P.roots i := (cutBranchGraphIso P).injective
        (h.2.trans (cutBranchGraphIso_root P i).symm)
      subst x
      subst y
      exact P.cut_adj i hi
  · intro hxy
    by_cases hdeleted : s(x, y) ∈ zhaoCutEdges P.roots P.parent
    · rw [zhaoCutEdges, Finset.mem_image] at hdeleted
      obtain ⟨i, _, hi⟩ := hdeleted
      rcases Sym2.eq_iff.mp hi with h | h
      · rcases h with ⟨rfl, rfl⟩
        exact Or.inr ⟨i.1, i.2, Or.inr ⟨cutBranchGraphIso_parent P i.1 i.2, cutBranchGraphIso_root P i.1⟩⟩
      · rcases h with ⟨rfl, rfl⟩
        exact Or.inr ⟨i.1, i.2, Or.inl ⟨cutBranchGraphIso_parent P i.1 i.2, cutBranchGraphIso_root P i.1⟩⟩
    · exact Or.inl ((cutBranchGraphIso P).toHom.map_rel (SimpleGraph.deleteEdges_adj.mpr ⟨hxy, hdeleted⟩))

def reconnectedPartitionIso : T ≃g reconnectedGraph (branchForest P) (partitionCutSource P hT locate hlocate) where
  toEquiv := (cutBranchGraphIso P).toEquiv
  map_rel_iff' := reconnected_adj_iff_tree P hT locate hlocate _ _

end Erdos547b.ZhaoSourcePartitionReconnectedGraph

#print axioms Erdos547b.ZhaoSourcePartitionReconnectedGraph.cutBranchGraphIso_parent
#print axioms Erdos547b.ZhaoSourcePartitionReconnectedGraph.reconnectedPartitionIso
