import Util.IncidenceGeometry.OrdinaryDrawingPartialData

open Classical
noncomputable section

noncomputable def OrdinaryDrawingPartialDataComplete {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet]
    (P : OrdinaryDrawingPartialData G (Finset.univ : Finset G.edgeFinset)) :
    OrdinaryPolygonalDrawing G := by
  classical
  let toDrawn : G.edgeFinset → {e : G.edgeFinset // e ∈ (Finset.univ : Finset G.edgeFinset)} :=
    fun e => ⟨e, by simp⟩
  refine {
    vertexPlacement := P.vertexPlacement
    vertexPlacement_injective := P.vertexPlacement_injective
    edgeArc := fun e => P.edgeArc (toDrawn e)
    edgeArc_endpoints := ?_
    crossingSet := P.crossingSet
    no_vertex_in_edge_interior := ?_
    no_three_edge_interiors_meet := ?_
    transverse_intersections := ?_
    no_shared_nondegenerate_subarc := ?_
    crossingSet_spec := ?_
    adjacentEdgeCrossingCount :=
      (P.crossingSet.filter (fun p =>
        ∃ e₁ e₂ : G.edgeFinset,
          e₁ ≠ e₂ ∧
            (∃ v : V, v ∈ e₁.1 ∧ v ∈ e₂.1) ∧
              p ∈ (P.edgeArc (toDrawn e₁)).relativeInterior ∧
                p ∈ (P.edgeArc (toDrawn e₂)).relativeInterior)).card
    adjacentEdgeCrossingCount_eq := rfl }
  · intro e
    simpa [toDrawn] using P.edgeArc_endpoints (toDrawn e)
  · intro v e
    simpa [toDrawn] using P.no_vertex_in_edge_interior v (toDrawn e)
  · intro e₁ e₂ e₃ p h₁₂ h₁₃ h₂₃ hp₁ hp₂ hp₃
    have h₁₂' : toDrawn e₁ ≠ toDrawn e₂ := by
      intro h
      exact h₁₂ (congrArg Subtype.val h)
    have h₁₃' : toDrawn e₁ ≠ toDrawn e₃ := by
      intro h
      exact h₁₃ (congrArg Subtype.val h)
    have h₂₃' : toDrawn e₂ ≠ toDrawn e₃ := by
      intro h
      exact h₂₃ (congrArg Subtype.val h)
    exact P.no_three_edge_interiors_meet h₁₂' h₁₃' h₂₃' hp₁ hp₂ hp₃
  · intro e₁ e₂ p h₁₂ hp₁ hp₂
    have h₁₂' : toDrawn e₁ ≠ toDrawn e₂ := by
      intro h
      exact h₁₂ (congrArg Subtype.val h)
    exact P.transverse_intersections h₁₂' hp₁ hp₂
  · intro e₁ e₂ h₁₂
    have h₁₂' : toDrawn e₁ ≠ toDrawn e₂ := by
      intro h
      exact h₁₂ (congrArg Subtype.val h)
    exact P.no_shared_nondegenerate_subarc h₁₂'
  · intro p
    constructor
    · intro hp
      rcases (P.crossingSet_spec p).mp hp with ⟨e₁, e₂, h₁₂, hp₁, hp₂⟩
      refine ⟨e₁.1, e₂.1, ?_, ?_, ?_⟩
      · intro h
        exact h₁₂ (Subtype.ext h)
      · have he₁ : toDrawn e₁.1 = e₁ := by
          ext
          rfl
        simpa [he₁]
      · have he₂ : toDrawn e₂.1 = e₂ := by
          ext
          rfl
        simpa [he₂]
    · rintro ⟨e₁, e₂, h₁₂, hp₁, hp₂⟩
      apply (P.crossingSet_spec p).mpr
      refine ⟨toDrawn e₁, toDrawn e₂, ?_, hp₁, hp₂⟩
      intro h
      exact h₁₂ (congrArg Subtype.val h)
