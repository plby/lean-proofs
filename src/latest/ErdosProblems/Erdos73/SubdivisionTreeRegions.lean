import ErdosProblems.Erdos73.SubdivisionSupports
import ErdosProblems.Erdos73.MonochromaticPathParity
import ErdosProblems.Erdos73.SubdivisionAnchors
import ErdosProblems.Erdos73.ParityGraphTransport
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Connected pattern regions yield actual, support-controlled, even-corridor tree cells. -/

namespace Erdos73.GraphSubdivisionModel
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {W V : Type*} [Fintype W] [LinearOrder W] [Fintype V]
variable {H : SimpleGraph W} {G : SimpleGraph V}

theorem exists_tree_region (S : GraphSubdivisionModel H G) (R : Finset W)
    (hR : (H.induce (R : Set W)).Connected) :
    ∃ T : SimpleGraph (R : Set W), T.IsTree ∧
      ∃ S' : GraphSubdivisionModel T G,
        (∀ w, S'.branchVertex w = S.branchVertex w.val) ∧ S'.vertexSet ⊆ S.supportOver R := by
  obtain ⟨T, hTle, hT⟩ := hR.exists_isTree_le
  let f : T.Copy H := {
    toHom := { toFun := Subtype.val, map_rel' := fun h => hTle h }
    injective' := Subtype.val_injective }
  refine ⟨T, hT, S.restrictCopy f, fun _ => rfl, ?_⟩
  apply (S.restrictCopy_vertexSet_subset f).trans
  apply S.supportOver_mono
  intro w hw
  obtain ⟨x, _, rfl⟩ := mem_image.mp hw
  exact x.property

theorem exists_even_tree_region (S : GraphSubdivisionModel H G)
    (col : BipartiteColoringOn G S.vertexSet) (b : Bool)
    (hb : ∀ w, col.color (S.branchVertex w) = b) (R : Finset W)
    (hR : (H.induce (R : Set W)).Connected) :
    ∃ T : SimpleGraph (R : Set W), T.IsTree ∧
      ∃ S' : GraphSubdivisionModel T G,
        (∀ w, S'.branchVertex w = S.branchVertex w.val) ∧
        S'.vertexSet ⊆ S.supportOver R ∧ (∀ e, Even (S'.edgePath e).walk.length) := by
  obtain ⟨T, hT, S', hbranch, hsub⟩ := S.exists_tree_region R hR
  have hsub' : S'.vertexSet ⊆ S.vertexSet := hsub.trans (S.supportOver_mono (subset_univ _))
  let col' := col.mono_support hsub'
  have hb' : ∀ w, col'.color (S'.branchVertex w) = b := by
    intro w
    change col.color (S'.branchVertex w) = b
    rw [hbranch]
    exact hb w.val
  exact ⟨T, hT, S', hbranch, hsub, S'.even_edgePaths_of_monochromaticBranches col' b hb'⟩

end
end Erdos73.GraphSubdivisionModel
