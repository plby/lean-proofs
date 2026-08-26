/- Minor transport preserves actual hits on labelled columns. -/
import ErdosProblems.Erdos73.ColumnWitnesses

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Erdos73Infrastructure.SimpleGraph
open Erdos73Infrastructure.SimpleGraph.TreewidthSparsifier

variable {V I : Type*} {G H : SimpleGraph V} {Q : I → Finset V} {g : ℕ}

theorem ColumnRichGrid.mono (h : ColumnRichGrid G Q g) (hGH : G ≤ H) :
    ColumnRichGrid H Q g := by
  let f : G.Copy H := {
    toHom := { toFun := id, map_rel' := fun h => hGH h }
    injective' := Function.injective_id }
  exact h.trans (MinorModel.of_copy f) (fun _ w hw => ⟨w, hw, Finset.mem_singleton_self _⟩)

theorem ColumnRichGrid.of_contract [DecidableEq V] {a b : V} (hab : G.Adj a b)
    (h : ColumnRichGrid (contractEdgeGraph G hab)
      (fun i => edgeContractImageSet (a := a) (b := b) (Q i)) g) :
    ColumnRichGrid G Q g := by
  apply h.trans (contractEdgeGraph.minorModel (huv := hab))
  intro i w hw
  obtain ⟨v, hv, rfl⟩ := mem_edgeContractImageSet_iff.mp hw
  exact ⟨v, hv, EdgeContractVertex.mem_branchSet_projection v⟩

theorem ColumnRichGrid.of_induce (U : Finset V) (hQU : ∀ i, Q i ⊆ U)
    (h : ColumnRichGrid (G.induce {v | v ∈ U})
      (fun i => PathPacking.subtypeFinset (Q i) U (hQU i)) g) :
    ColumnRichGrid G Q g := by
  apply h.trans (MinorModel.of_embedding (SimpleGraph.Embedding.induce _))
  intro i w hw
  exact ⟨w.val, (PathPacking.mem_subtypeFinset (hQU i) w).mp hw,
    Finset.mem_singleton_self _⟩

end
end Erdos73
