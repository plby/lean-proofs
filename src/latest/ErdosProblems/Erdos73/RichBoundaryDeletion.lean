/- Proper linkage deletion with a boundary-rooted column-rich obstruction. -/
import ErdosProblems.Erdos73.RootedColumnObstruction

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Erdos73Infrastructure.SimpleGraph

/-- Delete one member of a sufficiently large proper linkage while
retaining a proper sublinkage of a fixed positive fraction of the rows. -/
theorem boundaryProper_linkage_avoiding_path_of_no_rootedRichGrid
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {A B S T Z : Finset V}
    (P : PathPacking G A B) (Q : PathPacking G S T)
    (hP : P.IsBoundaryProper Z) (hQ : Q.IsBoundaryProper Z)
    (hAZ : A ⊆ Z) (hBZ : B ⊆ Z)
    (g : ℕ) (hm : controlledGrillRows g ≤ P.card)
    (hsize : (P.card + 1) * (2 * controlledGrillColumns g) ≤ Q.card)
    (hgrid : NoRootedColumnRichGrid G Z g) :
    ∃ i : Q.Index, ∃ R : PathPacking G (A \ (Q.path i).vertexSet) (B \ (Q.path i).vertexSet),
      P.card / (2 * controlledGrillRows g) + 1 ≤ R.card ∧
      (∀ r, Disjoint (R.path r).vertexSet (Q.path i).vertexSet) ∧ R.IsBoundaryProper Z := by
  let J := P.spanningGraph ⊔ Q.spanningGraph
  have hJG : J ≤ G := sup_le P.spanningGraph_le Q.spanningGraph_le
  let PJ : PathPacking J A B := P.inSpanningGraph.mapLe le_sup_left
  let QJ : PathPacking J S T := Q.inSpanningGraph.mapLe le_sup_right
  have hQverts (i : Q.Index) : (QJ.path i).vertexSet = (Q.path i).vertexSet := by
    change (((Q.inSpanningGraph.path i).mapLe le_sup_right).vertexSet) = _
    rw [GraphPath.mapLe_vertexSet]
    simp only [PathPacking.inSpanningGraph, PathPacking.transfer, GraphPath.transfer_vertexSet]
  have hconn (i : Q.Index) : (J.induce ((Q.path i).vertexSet : Set V)).Connected := by
    have hc := (QJ.path i).connected_induce_vertexSet
    rw [hQverts i] at hc
    exact hc
  obtain ⟨i, R, hcard, havoid⟩ := linkage_avoiding_column_of_no_richGrid PJ
    (fun i : Q.Index => (Q.path i).vertexSet)
    (fun i => ⟨_, (Q.path i).source_mem_vertexSet⟩) hconn Q.node_disjoint
    g hm hsize (by
      apply (hgrid.mono hJG) Q.Index (fun i => (Q.path i).vertexSet) hconn Q.node_disjoint
      intro i
      exact ⟨(Q.path i).source, (Q.path i).source_mem_vertexSet, (hQ i).source_mem⟩)
  let C := R.cleanToTerminals
  have hCavoid (r : C.Index) : Disjoint (C.path r).vertexSet (Q.path i).vertexSet :=
    (havoid r).mono_left (R.cleanToTerminals_path_vertexSet_subset r)
  have hCproper : C.IsBoundaryProper Z := by
    intro r
    exact P.boundaryProper_of_clean_avoiding Q hP hQ hAZ hBZ (C.path r)
      (C.connects r) (R.cleanToTerminals_terminalClean r) (hCavoid r)
  refine ⟨i, C.mapLe hJG, hcard, ?_, ?_⟩
  · intro r
    change Disjoint ((C.path r).mapLe hJG).vertexSet (Q.path i).vertexSet
    rw [GraphPath.mapLe_vertexSet]
    exact hCavoid r
  · intro r
    exact (hCproper r).mapLe hJG

end
end Erdos73

