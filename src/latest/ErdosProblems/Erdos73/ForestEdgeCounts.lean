import ErdosProblems.Erdos73.OrientedEdgeMaps
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Finite forests have strictly fewer edges than vertices on every nonempty carrier. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset

variable {W : Type*} [Fintype W] [LinearOrder W] (T : SimpleGraph W)

def OrientedEdge.edgeSetEquiv : OrientedEdge T ≃ T.edgeSet :=
  Equiv.ofBijective (fun e => ⟨s(e.lo, e.hi), e.adj⟩) ⟨by
    intro e f he
    exact OrientedEdge.eq_of_sym2_eq (congrArg Subtype.val he), by
    rintro ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | hf u v =>
      refine ⟨OrientedEdge.ofAdj he, Subtype.ext ?_⟩
      exact OrientedEdge.ofAdj_sym2 he⟩

theorem card_orientedEdge_eq_edgeFinset : Fintype.card (OrientedEdge T) = T.edgeFinset.card := by
  rw [Fintype.card_congr (OrientedEdge.edgeSetEquiv T), T.card_edgeSet]

theorem acyclic_card_orientedEdge_lt [Nonempty W] (hT : T.IsAcyclic) :
    Fintype.card (OrientedEdge T) < Fintype.card W := by
  obtain ⟨F, hTF, _, hF⟩ := (connected_top (V := W)).exists_isTree_le_of_le_of_isAcyclic le_top hT
  have hh := Finset.card_le_card (edgeFinset_mono hTF)
  have he := hF.card_edgeFinset
  rw [card_orientedEdge_eq_edgeFinset]
  omega

theorem tree_card_orientedEdge_add_one (hT : T.IsTree) :
    Fintype.card (OrientedEdge T) + 1 = Fintype.card W := by
  rw [card_orientedEdge_eq_edgeFinset]
  exact hT.card_edgeFinset

end
end Erdos73
