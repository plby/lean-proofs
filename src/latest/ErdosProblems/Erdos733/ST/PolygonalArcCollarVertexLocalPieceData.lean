import ErdosProblems.Erdos733.ST.PolygonalArcCollarSeparatedTubeData

-- [TABLET NODE: PolygonalArcCollarVertexLocalPieceData]
structure PolygonalArcCollarVertexLocalPieceData (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (separatedTubes :
      PolygonalArcCollarSeparatedTubeData γ controlRadii middleSegments
        forbiddenMargins) where
-- BODY
  vertexDisk : Fin γ.vertices.length → Set (EuclideanSpace ℝ (Fin 2))
  endpointPiece : Fin γ.vertices.length → Set (EuclideanSpace ℝ (Fin 2))
  leftLocalPiece : Fin γ.vertices.length → Set (EuclideanSpace ℝ (Fin 2))
  rightLocalPiece : Fin γ.vertices.length → Set (EuclideanSpace ℝ (Fin 2))
  outgoingLeftAttachment :
    (j : ℕ) → j + 1 < γ.vertices.length → Set (EuclideanSpace ℝ (Fin 2))
  outgoingRightAttachment :
    (j : ℕ) → j + 1 < γ.vertices.length → Set (EuclideanSpace ℝ (Fin 2))
  incomingLeftAttachment :
    (j : ℕ) → j + 1 < γ.vertices.length → Set (EuclideanSpace ℝ (Fin 2))
  incomingRightAttachment :
    (j : ℕ) → j + 1 < γ.vertices.length → Set (EuclideanSpace ℝ (Fin 2))
  vertexDisk_eq :
    ∀ i,
      vertexDisk i = Metric.ball γ.vertices[i.1] (controlRadii.radius i)
  endpointPiece_eq :
    ∀ i,
      endpointPiece i =
        vertexDisk i \ ({γ.vertices[i.1]} : Set (EuclideanSpace ℝ (Fin 2)))
  vertexDisk_open : ∀ i, IsOpen (vertexDisk i)
  endpointPiece_open : ∀ i, IsOpen (endpointPiece i)
  endpointPiece_omits_vertex :
    ∀ i, γ.vertices[i.1] ∉ endpointPiece i
  vertexDisk_subset_closed_control_disk :
    ∀ i,
      vertexDisk i ⊆
        Metric.closedBall γ.vertices[i.1] (controlRadii.radius i)
  vertexDisk_subset_eta_neighborhood :
    ∀ i, ∀ z ∈ vertexDisk i, ∃ p ∈ γ.carrier, dist z p < η
  vertexDisk_disjoint_nonincident_segments :
    ∀ (i : Fin γ.vertices.length) (j : ℕ)
      (hj : j + 1 < γ.vertices.length),
        i.1 ≠ j → i.1 ≠ j + 1 →
          Disjoint (vertexDisk i)
            (segment ℝ γ.vertices[j] γ.vertices[j + 1])
  vertexDisk_carrier_subset_incident_segments :
    ∀ (i : Fin γ.vertices.length), ∀ z ∈ vertexDisk i, z ∈ γ.carrier →
      ∃ j : ℕ, ∃ hj : j + 1 < γ.vertices.length,
        z ∈ segment ℝ γ.vertices[j] γ.vertices[j + 1] ∧
          (i.1 = j ∨ i.1 = j + 1)
  vertexDisk_disjoint_other_control_disks :
    ∀ ⦃i k : Fin γ.vertices.length⦄, i ≠ k →
      Disjoint (vertexDisk i)
        (Metric.closedBall γ.vertices[k.1] (controlRadii.radius k))
  vertexDisk_disjoint_nonincident_tubes :
    ∀ (i : Fin γ.vertices.length) (j : ℕ)
      (hj : j + 1 < γ.vertices.length),
        i.1 ≠ j → i.1 ≠ j + 1 →
          Disjoint (vertexDisk i) (separatedTubes.tube j hj)
  outgoing_germ_subset_endpointPiece :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
          Set.Ioo (0 : ℝ)
            (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
              dist γ.vertices[j] γ.vertices[j + 1]) ⊆
        endpointPiece ⟨j, Nat.lt_of_succ_lt hj⟩
  incoming_germ_subset_endpointPiece :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
          Set.Ioo
            (1 - controlRadii.radius ⟨j + 1, hj⟩ /
              dist γ.vertices[j] γ.vertices[j + 1]) (1 : ℝ) ⊆
        endpointPiece ⟨j + 1, hj⟩
  leftLocalPiece_eq :
    ∀ i,
      leftLocalPiece i =
        {z | (∃ hj : i.1 + 1 < γ.vertices.length,
              z ∈ vertexDisk i ∧ z ∈ separatedTubes.leftHalf i.1 hj) ∨
            (∃ (j : ℕ) (hj : j + 1 < γ.vertices.length),
              j + 1 = i.1 ∧ z ∈ vertexDisk i ∧
                z ∈ separatedTubes.leftHalf j hj)}
  rightLocalPiece_eq :
    ∀ i,
      rightLocalPiece i =
        {z | (∃ hj : i.1 + 1 < γ.vertices.length,
              z ∈ vertexDisk i ∧ z ∈ separatedTubes.rightHalf i.1 hj) ∨
            (∃ (j : ℕ) (hj : j + 1 < γ.vertices.length),
              j + 1 = i.1 ∧ z ∈ vertexDisk i ∧
                z ∈ separatedTubes.rightHalf j hj)}
  leftLocalPiece_subset_disk :
    ∀ i, leftLocalPiece i ⊆ vertexDisk i
  rightLocalPiece_subset_disk :
    ∀ i, rightLocalPiece i ⊆ vertexDisk i
  outgoingLeftAttachment_eq :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      outgoingLeftAttachment j hj =
        vertexDisk ⟨j, Nat.lt_of_succ_lt hj⟩ ∩
          separatedTubes.leftHalf j hj
  outgoingRightAttachment_eq :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      outgoingRightAttachment j hj =
        vertexDisk ⟨j, Nat.lt_of_succ_lt hj⟩ ∩
          separatedTubes.rightHalf j hj
  incomingLeftAttachment_eq :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      incomingLeftAttachment j hj =
        vertexDisk ⟨j + 1, hj⟩ ∩ separatedTubes.leftHalf j hj
  incomingRightAttachment_eq :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      incomingRightAttachment j hj =
        vertexDisk ⟨j + 1, hj⟩ ∩ separatedTubes.rightHalf j hj
  outgoingLeftAttachment_nonempty :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      (outgoingLeftAttachment j hj).Nonempty
  outgoingRightAttachment_nonempty :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      (outgoingRightAttachment j hj).Nonempty
  incomingLeftAttachment_nonempty :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      (incomingLeftAttachment j hj).Nonempty
  incomingRightAttachment_nonempty :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      (incomingRightAttachment j hj).Nonempty
  outgoingLeftAttachment_subset_leftLocalPiece :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      outgoingLeftAttachment j hj ⊆
        leftLocalPiece ⟨j, Nat.lt_of_succ_lt hj⟩
  outgoingRightAttachment_subset_rightLocalPiece :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      outgoingRightAttachment j hj ⊆
        rightLocalPiece ⟨j, Nat.lt_of_succ_lt hj⟩
  incomingLeftAttachment_subset_leftLocalPiece :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      incomingLeftAttachment j hj ⊆ leftLocalPiece ⟨j + 1, hj⟩
  incomingRightAttachment_subset_rightLocalPiece :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      incomingRightAttachment j hj ⊆ rightLocalPiece ⟨j + 1, hj⟩
