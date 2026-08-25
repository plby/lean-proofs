import Util.IncidenceGeometry.OrdinaryDrawingPartialData
import Util.IncidenceGeometry.OrdinaryDrawingVertexPlacementExists

open Classical
noncomputable section

lemma OrdinaryDrawingEmptyPartialData {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] :
    Nonempty (OrdinaryDrawingPartialData G (∅ : Finset G.edgeFinset)) := by
  classical
  obtain ⟨placement, hplacement⟩ := OrdinaryDrawingVertexPlacementExists V
  let noDrawnEdge : {e : G.edgeFinset // e ∈ (∅ : Finset G.edgeFinset)} → False :=
    fun e => Finset.notMem_empty e.1 e.2
  refine ⟨({
    vertexPlacement := placement
    vertexPlacement_injective := hplacement
    edgeArc := fun e => False.elim (noDrawnEdge e)
    edgeArc_endpoints := by
      intro e
      exact False.elim (noDrawnEdge e)
    crossingSet := ∅
    no_vertex_in_edge_interior := by
      intro v e
      exact False.elim (noDrawnEdge e)
    no_three_edge_interiors_meet := by
      intro e₁ e₂ e₃ p h₁₂ h₁₃ h₂₃ hp₁ hp₂ hp₃
      exact False.elim (noDrawnEdge e₁)
    transverse_intersections := by
      intro e₁ e₂ p h₁₂ hp₁ hp₂
      exact False.elim (noDrawnEdge e₁)
    no_shared_nondegenerate_subarc := by
      intro e₁ e₂ h₁₂
      exact False.elim (noDrawnEdge e₁)
    crossingSet_spec := by
      intro p
      constructor
      · intro hp
        simp at hp
      · rintro ⟨e₁, e₂, h₁₂, hp₁, hp₂⟩
        exact False.elim (noDrawnEdge e₁) } :
    OrdinaryDrawingPartialData G (∅ : Finset G.edgeFinset))⟩
