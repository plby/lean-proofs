import Util.IncidenceGeometry.OrdinaryPolygonalDrawing
import Mathlib.Combinatorics.SimpleGraph.Copy

open Classical
noncomputable section

lemma OrdinaryPolygonalDrawingDeleteEdges {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (D : OrdinaryPolygonalDrawing G)
    (S : Finset (Sym2 V)) :
    ∃ D' : OrdinaryPolygonalDrawing (G.deleteEdges (S : Set (Sym2 V))),
      D'.crossingSet =
          D.crossingSet.filter (fun p =>
            ∃ e₁ e₂ : G.edgeFinset,
              e₁ ≠ e₂ ∧ e₁.1 ∉ S ∧ e₂.1 ∉ S ∧
                p ∈ (D.edgeArc e₁).relativeInterior ∧
                  p ∈ (D.edgeArc e₂).relativeInterior) ∧
        (G.deleteEdges (S : Set (Sym2 V))).edgeFinset.card =
          G.edgeFinset.card - (S ∩ G.edgeFinset).card := by
  classical
  let oldEdge : (G.deleteEdges (S : Set (Sym2 V))).edgeFinset →
      G.edgeFinset := fun ed =>
    ⟨ed.1, by
      apply SimpleGraph.mem_edgeFinset.mpr
      have hed : ed.1 ∈ (G.deleteEdges (S : Set (Sym2 V))).edgeSet :=
        SimpleGraph.mem_edgeFinset.mp ed.2
      rw [SimpleGraph.edgeSet_deleteEdges] at hed
      exact hed.1⟩
  have oldEdge_val :
      ∀ ed : (G.deleteEdges (S : Set (Sym2 V))).edgeFinset,
        (oldEdge ed).1 = ed.1 := by
    intro ed
    rfl
  have oldEdge_not_mem :
      ∀ ed : (G.deleteEdges (S : Set (Sym2 V))).edgeFinset,
        (oldEdge ed).1 ∉ S := by
    intro ed
    have hed := SimpleGraph.mem_edgeFinset.mp ed.2
    rw [SimpleGraph.edgeSet_deleteEdges] at hed
    exact hed.2
  have oldEdge_injective : Function.Injective oldEdge := by
    intro e₁ e₂ h
    apply Subtype.ext
    simpa [oldEdge_val] using congrArg Subtype.val h
  let retainedEdge :
      (e : G.edgeFinset) → e.1 ∉ S →
        (G.deleteEdges (S : Set (Sym2 V))).edgeFinset := fun e he =>
    ⟨e.1, by
      apply SimpleGraph.mem_edgeFinset.mpr
      rw [SimpleGraph.edgeSet_deleteEdges]
      exact ⟨SimpleGraph.mem_edgeFinset.mp e.2, he⟩⟩
  have retainedEdge_oldEdge :
      ∀ (e : G.edgeFinset) (he : e.1 ∉ S),
        oldEdge (retainedEdge e he) = e := by
    intro e he
    apply Subtype.ext
    rfl
  let retainedCrossingSet : Finset (EuclideanSpace ℝ (Fin 2)) :=
    D.crossingSet.filter (fun p =>
      ∃ e₁ e₂ : G.edgeFinset,
        e₁ ≠ e₂ ∧ e₁.1 ∉ S ∧ e₂.1 ∉ S ∧
          p ∈ (D.edgeArc e₁).relativeInterior ∧
            p ∈ (D.edgeArc e₂).relativeInterior)
  let restrictedEdgeArc :
      (G.deleteEdges (S : Set (Sym2 V))).edgeFinset → PolygonalArc :=
    fun ed => D.edgeArc (oldEdge ed)
  let retainedAdjacentCrossingSet : Finset (EuclideanSpace ℝ (Fin 2)) :=
    retainedCrossingSet.filter (fun p =>
      ∃ e₁ e₂ : (G.deleteEdges (S : Set (Sym2 V))).edgeFinset,
        e₁ ≠ e₂ ∧
          (∃ v : V, v ∈ e₁.1 ∧ v ∈ e₂.1) ∧
            p ∈ (restrictedEdgeArc e₁).relativeInterior ∧
              p ∈ (restrictedEdgeArc e₂).relativeInterior)
  let D' : OrdinaryPolygonalDrawing (G.deleteEdges (S : Set (Sym2 V))) :=
    { vertexPlacement := D.vertexPlacement
      vertexPlacement_injective := D.vertexPlacement_injective
      edgeArc := restrictedEdgeArc
      edgeArc_endpoints := by
        intro ed
        rcases D.edgeArc_endpoints (oldEdge ed) with ⟨u, v, huv, hedge, hends⟩
        refine ⟨u, v, ?_, ?_, ?_⟩
        · rw [← SimpleGraph.mem_edgeSet, SimpleGraph.edgeSet_deleteEdges]
          exact ⟨by simpa using huv, by simpa [← hedge] using oldEdge_not_mem ed⟩
        · simpa [oldEdge_val] using hedge
        · exact hends
      crossingSet := retainedCrossingSet
      no_vertex_in_edge_interior := by
        intro v ed
        exact D.no_vertex_in_edge_interior v (oldEdge ed)
      no_three_edge_interiors_meet := by
        intro e₁ e₂ e₃ p h₁₂ h₁₃ h₂₃ hp₁ hp₂ hp₃
        exact D.no_three_edge_interiors_meet
          (oldEdge_injective.ne h₁₂) (oldEdge_injective.ne h₁₃)
          (oldEdge_injective.ne h₂₃) hp₁ hp₂ hp₃
      transverse_intersections := by
        intro e₁ e₂ p h₁₂ hp₁ hp₂
        exact D.transverse_intersections (oldEdge_injective.ne h₁₂) hp₁ hp₂
      no_shared_nondegenerate_subarc := by
        intro e₁ e₂ h₁₂
        exact D.no_shared_nondegenerate_subarc (oldEdge_injective.ne h₁₂)
      crossingSet_spec := by
        intro p
        constructor
        · intro hp
          rcases (Finset.mem_filter.mp hp).2 with
            ⟨e₁, e₂, h₁₂, he₁, he₂, hp₁, hp₂⟩
          let ed₁ := retainedEdge e₁ he₁
          let ed₂ := retainedEdge e₂ he₂
          have hed₁ : oldEdge ed₁ = e₁ := retainedEdge_oldEdge e₁ he₁
          have hed₂ : oldEdge ed₂ = e₂ := retainedEdge_oldEdge e₂ he₂
          refine ⟨ed₁, ed₂, ?_, ?_, ?_⟩
          · intro h
            apply h₁₂
            simpa [hed₁, hed₂] using congrArg oldEdge h
          · simpa [restrictedEdgeArc, hed₁] using hp₁
          · simpa [restrictedEdgeArc, hed₂] using hp₂
        · rintro ⟨ed₁, ed₂, h₁₂, hp₁, hp₂⟩
          have hpOld : p ∈ D.crossingSet :=
            (D.crossingSet_spec p).2
              ⟨oldEdge ed₁, oldEdge ed₂, oldEdge_injective.ne h₁₂,
                by simpa [restrictedEdgeArc] using hp₁,
                by simpa [restrictedEdgeArc] using hp₂⟩
          exact Finset.mem_filter.mpr
            ⟨hpOld, oldEdge ed₁, oldEdge ed₂, oldEdge_injective.ne h₁₂,
              oldEdge_not_mem ed₁, oldEdge_not_mem ed₂,
              by simpa [restrictedEdgeArc] using hp₁,
              by simpa [restrictedEdgeArc] using hp₂⟩
      adjacentEdgeCrossingCount := retainedAdjacentCrossingSet.card
      adjacentEdgeCrossingCount_eq := by
        dsimp [retainedAdjacentCrossingSet] }
  refine ⟨D', rfl, ?_⟩
  rw [SimpleGraph.edgeFinset_deleteEdges]
  exact Finset.card_sdiff

