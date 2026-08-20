import ErdosProblems.Erdos733.ST.PolygonalReplacementEdgeBoundaryEndpointData

open Classical
noncomputable section

universe u

-- [TABLET NODE: PolygonalReplacementEdgeBoundaryEndpointDataExists]
lemma PolygonalReplacementEdgeBoundaryEndpointDataExists {V : Type u} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (boundaryPoints : PolygonalReplacementBoundaryPointData.{u, u} G D controlDisks) :
    Nonempty
      (PolygonalReplacementEdgeBoundaryEndpointData G D controlDisks boundaryPoints) := by
-- BODY
  classical
  have edgeSource_vertex :
      ∀ e : G.edgeFinset, ∃ v : V, v ∈ e.1 ∧ D.edgeSource e = D.vertexPlacement v := by
    intro e
    rcases D.edgeArc_endpoints e with ⟨a, b, _hadj, heq, hend⟩
    rcases hend with hend | hend
    · exact ⟨a, by simp [heq], hend.1⟩
    · exact ⟨b, by simp [heq], hend.1⟩
  have edgeTarget_vertex :
      ∀ e : G.edgeFinset, ∃ v : V, v ∈ e.1 ∧ D.edgeTarget e = D.vertexPlacement v := by
    intro e
    rcases D.edgeArc_endpoints e with ⟨a, b, _hadj, heq, hend⟩
    rcases hend with hend | hend
    · exact ⟨b, by simp [heq], hend.2⟩
    · exact ⟨a, by simp [heq], hend.2⟩
  let sourceVertex : G.edgeFinset → V := fun e => Classical.choose (edgeSource_vertex e)
  let targetVertex : G.edgeFinset → V := fun e => Classical.choose (edgeTarget_vertex e)
  have sourceVertex_spec :
      ∀ e, sourceVertex e ∈ e.1 ∧ D.edgeSource e = D.vertexPlacement (sourceVertex e) := by
    intro e
    exact Classical.choose_spec (edgeSource_vertex e)
  have targetVertex_spec :
      ∀ e, targetVertex e ∈ e.1 ∧ D.edgeTarget e = D.vertexPlacement (targetVertex e) := by
    intro e
    exact Classical.choose_spec (edgeTarget_vertex e)
  let sourceIndex : G.edgeFinset → boundaryPoints.boundaryIndex := fun e =>
    boundaryPoints.vertexBoundaryIndex (sourceVertex_spec e).1
  let targetIndex : G.edgeFinset → boundaryPoints.boundaryIndex := fun e =>
    boundaryPoints.vertexBoundaryIndex (targetVertex_spec e).1
  refine ⟨{
    edgeSourceVertex := sourceVertex
    edgeTargetVertex := targetVertex
    edgeSourceVertex_mem := fun e => (sourceVertex_spec e).1
    edgeTargetVertex_mem := fun e => (targetVertex_spec e).1
    edgeSource_eq_vertexPlacement := fun e => (sourceVertex_spec e).2
    edgeTarget_eq_vertexPlacement := fun e => (targetVertex_spec e).2
    sourceBoundaryIndex := sourceIndex
    targetBoundaryIndex := targetIndex
    sourceBoundaryPoint := fun e => boundaryPoints.point (sourceIndex e)
    targetBoundaryPoint := fun e => boundaryPoints.point (targetIndex e)
    sourceBoundaryPoint_eq := by
      intro e
      rfl
    targetBoundaryPoint_eq := by
      intro e
      rfl
    sourceBoundaryIndex_owner := by
      intro e
      dsimp [sourceIndex]
      exact boundaryPoints.vertexBoundaryIndex_owner (sourceVertex_spec e).1
    targetBoundaryIndex_owner := by
      intro e
      dsimp [targetIndex]
      exact boundaryPoints.vertexBoundaryIndex_owner (targetVertex_spec e).1
    sourceBoundary_on_control_boundary := by
      intro e
      dsimp [sourceIndex]
      exact boundaryPoints.vertexBoundaryIndex_boundary (sourceVertex_spec e).1
    targetBoundary_on_control_boundary := by
      intro e
      dsimp [targetIndex]
      exact boundaryPoints.vertexBoundaryIndex_boundary (targetVertex_spec e).1
    sourceBoundary_unique := by
      intro e p hpSphere hpCarrier
      dsimp [sourceIndex]
      exact boundaryPoints.vertex_boundary_point_eq (sourceVertex_spec e).1 hpSphere hpCarrier
    targetBoundary_unique := by
      intro e p hpSphere hpCarrier
      dsimp [targetIndex]
      exact boundaryPoints.vertex_boundary_point_eq (targetVertex_spec e).1 hpSphere hpCarrier }⟩
