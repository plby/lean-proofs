import ErdosProblems.Erdos733.ST.PolygonalArcCollarCompatibleOrientedTubeData
import ErdosProblems.Erdos733.ST.PolygonalArcCollarVertexLocalPieceData

-- [TABLET NODE: PolygonalArcCollarLocalTopologyData]
structure PolygonalArcCollarLocalTopologyData (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (compatibleTubes :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (vertexLocalPieces :
      PolygonalArcCollarVertexLocalPieceData γ controlRadii middleSegments
        forbiddenMargins
        compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData) where
-- BODY
  vertexCollar : Fin γ.vertices.length → Set (EuclideanSpace ℝ (Fin 2))
  leftSidePiece : Fin γ.vertices.length → Set (EuclideanSpace ℝ (Fin 2))
  rightSidePiece : Fin γ.vertices.length → Set (EuclideanSpace ℝ (Fin 2))
  vertexCollar_open : ∀ i, IsOpen (vertexCollar i)
  leftSidePiece_open : ∀ i, IsOpen (leftSidePiece i)
  rightSidePiece_open : ∀ i, IsOpen (rightSidePiece i)
  vertexCollar_subset_vertexDisk :
    ∀ i, vertexCollar i ⊆ vertexLocalPieces.vertexDisk i
  interior_vertexCollar_eq_vertexDisk :
    ∀ i, 0 < i.1 → i.1 + 1 < γ.vertices.length →
      vertexCollar i = vertexLocalPieces.vertexDisk i
  endpoint_vertexCollar_omits_vertex :
    ∀ i, (i.1 = 0 ∨ i.1 + 1 = γ.vertices.length) →
      γ.vertices[i.1] ∉ vertexCollar i
  vertexCollar_subset_eta_neighborhood :
    ∀ i, ∀ z ∈ vertexCollar i, ∃ p ∈ γ.carrier, dist z p < η
  vertexCollar_carrier_subset_incident_segments :
    ∀ i, ∀ z ∈ vertexCollar i, z ∈ γ.carrier →
      ∃ j : ℕ, ∃ hj : j + 1 < γ.vertices.length,
        z ∈ segment ℝ γ.vertices[j] γ.vertices[j + 1] ∧
          (i.1 = j ∨ i.1 = j + 1)
  outgoing_germ_subset_vertexCollar :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
          Set.Ioo (0 : ℝ)
            (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
              dist γ.vertices[j] γ.vertices[j + 1]) ⊆
        vertexCollar ⟨j, Nat.lt_of_succ_lt hj⟩
  incoming_germ_subset_vertexCollar :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
          Set.Ioo
            (1 - controlRadii.radius ⟨j + 1, hj⟩ /
              dist γ.vertices[j] γ.vertices[j + 1]) (1 : ℝ) ⊆
        vertexCollar ⟨j + 1, hj⟩
  outgoing_germ_subset_closure_leftSidePiece :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
          Set.Ioo (0 : ℝ)
            (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
              dist γ.vertices[j] γ.vertices[j + 1]) ⊆
        closure (leftSidePiece ⟨j, Nat.lt_of_succ_lt hj⟩)
  outgoing_germ_subset_closure_rightSidePiece :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
          Set.Ioo (0 : ℝ)
            (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
              dist γ.vertices[j] γ.vertices[j + 1]) ⊆
        closure (rightSidePiece ⟨j, Nat.lt_of_succ_lt hj⟩)
  incoming_germ_subset_closure_leftSidePiece :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
          Set.Ioo
            (1 - controlRadii.radius ⟨j + 1, hj⟩ /
              dist γ.vertices[j] γ.vertices[j + 1]) (1 : ℝ) ⊆
        closure (leftSidePiece ⟨j + 1, hj⟩)
  incoming_germ_subset_closure_rightSidePiece :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
          Set.Ioo
            (1 - controlRadii.radius ⟨j + 1, hj⟩ /
              dist γ.vertices[j] γ.vertices[j + 1]) (1 : ℝ) ⊆
        closure (rightSidePiece ⟨j + 1, hj⟩)
  interior_vertex_mem_closure_leftSidePiece :
    ∀ i, 0 < i.1 → i.1 + 1 < γ.vertices.length →
      γ.vertices[i.1] ∈ closure (leftSidePiece i)
  interior_vertex_mem_closure_rightSidePiece :
    ∀ i, 0 < i.1 → i.1 + 1 < γ.vertices.length →
      γ.vertices[i.1] ∈ closure (rightSidePiece i)
  leftSidePiece_subset_vertexCollar :
    ∀ i, leftSidePiece i ⊆ vertexCollar i
  rightSidePiece_subset_vertexCollar :
    ∀ i, rightSidePiece i ⊆ vertexCollar i
  leftSidePiece_connected : ∀ i, IsConnected (leftSidePiece i)
  rightSidePiece_connected : ∀ i, IsConnected (rightSidePiece i)
  leftSidePiece_disjoint_carrier :
    ∀ i, Disjoint (leftSidePiece i) γ.carrier
  rightSidePiece_disjoint_carrier :
    ∀ i, Disjoint (rightSidePiece i) γ.carrier
  local_sidePieces_disjoint :
    ∀ i, Disjoint (leftSidePiece i) (rightSidePiece i)
  leftHalf_inter_vertexCollar_subset_leftSidePiece :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (i : Fin γ.vertices.length),
        compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf
            j hj ∩
          vertexCollar i ⊆ leftSidePiece i
  rightHalf_inter_vertexCollar_subset_rightSidePiece :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (i : Fin γ.vertices.length),
        compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf
            j hj ∩
          vertexCollar i ⊆ rightSidePiece i
  vertexCollar_without_arc :
    ∀ i, vertexCollar i \ γ.relativeInterior =
      leftSidePiece i ∪ rightSidePiece i
  outgoingLeftAttachment_subset_leftSidePiece :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      vertexLocalPieces.outgoingLeftAttachment j hj ⊆
        leftSidePiece ⟨j, Nat.lt_of_succ_lt hj⟩
  outgoingRightAttachment_subset_rightSidePiece :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      vertexLocalPieces.outgoingRightAttachment j hj ⊆
        rightSidePiece ⟨j, Nat.lt_of_succ_lt hj⟩
  incomingLeftAttachment_subset_leftSidePiece :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      vertexLocalPieces.incomingLeftAttachment j hj ⊆ leftSidePiece ⟨j + 1, hj⟩
  incomingRightAttachment_subset_rightSidePiece :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      vertexLocalPieces.incomingRightAttachment j hj ⊆
        rightSidePiece ⟨j + 1, hj⟩
