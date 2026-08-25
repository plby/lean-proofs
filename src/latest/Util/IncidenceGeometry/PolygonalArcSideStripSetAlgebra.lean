import Util.IncidenceGeometry.PolygonalArcMiddleTubeWithoutRelativeInterior

open Classical
noncomputable section

lemma PolygonalArcSideStripSetAlgebra
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (orientedTubes :
      PolygonalArcCollarOrientedSeparatedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (vertexLocalPieces :
      PolygonalArcCollarVertexLocalPieceData γ controlRadii middleSegments
        forbiddenMargins orientedTubes.toPolygonalArcCollarSeparatedTubeData)
    (localSideData :
      PolygonalArcCollarLocalSideData γ controlRadii middleSegments
        forbiddenMargins orientedTubes vertexLocalPieces) :
    let sep := orientedTubes.toPolygonalArcCollarSeparatedTubeData
    let C : Set (EuclideanSpace ℝ (Fin 2)) :=
      ((⋃ (j : ℕ), ⋃ (hj : j + 1 < γ.vertices.length), sep.tube j hj) ∪
        (⋃ i : Fin γ.vertices.length, localSideData.vertexCollar i))
    let L : Set (EuclideanSpace ℝ (Fin 2)) :=
      ((⋃ (j : ℕ), ⋃ (hj : j + 1 < γ.vertices.length), sep.leftHalf j hj) ∪
        (⋃ i : Fin γ.vertices.length, localSideData.leftSidePiece i))
    let R : Set (EuclideanSpace ℝ (Fin 2)) :=
      ((⋃ (j : ℕ), ⋃ (hj : j + 1 < γ.vertices.length), sep.rightHalf j hj) ∪
        (⋃ i : Fin γ.vertices.length, localSideData.rightSidePiece i))
    Disjoint L γ.carrier ∧ Disjoint R γ.carrier ∧ Disjoint L R ∧
      C \ γ.relativeInterior = L ∪ R := by
  let sep := orientedTubes.toPolygonalArcCollarSeparatedTubeData
  let C : Set (EuclideanSpace ℝ (Fin 2)) :=
    ((⋃ (j : ℕ), ⋃ (hj : j + 1 < γ.vertices.length), sep.tube j hj) ∪
      (⋃ i : Fin γ.vertices.length, localSideData.vertexCollar i))
  let L : Set (EuclideanSpace ℝ (Fin 2)) :=
    ((⋃ (j : ℕ), ⋃ (hj : j + 1 < γ.vertices.length), sep.leftHalf j hj) ∪
      (⋃ i : Fin γ.vertices.length, localSideData.leftSidePiece i))
  let R : Set (EuclideanSpace ℝ (Fin 2)) :=
    ((⋃ (j : ℕ), ⋃ (hj : j + 1 < γ.vertices.length), sep.rightHalf j hj) ∪
      (⋃ i : Fin γ.vertices.length, localSideData.rightSidePiece i))
  change Disjoint L γ.carrier ∧ Disjoint R γ.carrier ∧ Disjoint L R ∧
    C \ γ.relativeInterior = L ∪ R
  have hL_subset_C : L ⊆ C := by
    intro z hz
    dsimp [L, C] at hz ⊢
    rcases hz with hzHalf | hzPiece
    · left
      rcases Set.mem_iUnion.1 hzHalf with ⟨j, hzj⟩
      rcases Set.mem_iUnion.1 hzj with ⟨hj, hzLeft⟩
      exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hj,
        sep.leftHalf_subset_tube j hj hzLeft⟩⟩
    · right
      rcases Set.mem_iUnion.1 hzPiece with ⟨i, hzi⟩
      exact Set.mem_iUnion.2 ⟨i,
        localSideData.leftSidePiece_subset_vertexCollar i hzi⟩
  have hR_subset_C : R ⊆ C := by
    intro z hz
    dsimp [R, C] at hz ⊢
    rcases hz with hzHalf | hzPiece
    · left
      rcases Set.mem_iUnion.1 hzHalf with ⟨j, hzj⟩
      rcases Set.mem_iUnion.1 hzj with ⟨hj, hzRight⟩
      exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hj,
        sep.rightHalf_subset_tube j hj hzRight⟩⟩
    · right
      rcases Set.mem_iUnion.1 hzPiece with ⟨i, hzi⟩
      exact Set.mem_iUnion.2 ⟨i,
        localSideData.rightSidePiece_subset_vertexCollar i hzi⟩
  have hL_disjoint_carrier : Disjoint L γ.carrier := by
    refine Set.disjoint_left.2 ?_
    intro z hzL hzCarrier
    dsimp [L] at hzL
    rcases hzL with hzHalf | hzPiece
    · rcases Set.mem_iUnion.1 hzHalf with ⟨j, hzj⟩
      rcases Set.mem_iUnion.1 hzj with ⟨hj, hzLeft⟩
      exact Set.disjoint_left.mp
        (localSideData.leftHalf_disjoint_carrier j hj) hzLeft hzCarrier
    · rcases Set.mem_iUnion.1 hzPiece with ⟨i, hzLeftPiece⟩
      exact Set.disjoint_left.mp
        (localSideData.leftSidePiece_disjoint_carrier i) hzLeftPiece hzCarrier
  have hR_disjoint_carrier : Disjoint R γ.carrier := by
    refine Set.disjoint_left.2 ?_
    intro z hzR hzCarrier
    dsimp [R] at hzR
    rcases hzR with hzHalf | hzPiece
    · rcases Set.mem_iUnion.1 hzHalf with ⟨j, hzj⟩
      rcases Set.mem_iUnion.1 hzj with ⟨hj, hzRight⟩
      exact Set.disjoint_left.mp
        (localSideData.rightHalf_disjoint_carrier j hj) hzRight hzCarrier
    · rcases Set.mem_iUnion.1 hzPiece with ⟨i, hzRightPiece⟩
      exact Set.disjoint_left.mp
        (localSideData.rightSidePiece_disjoint_carrier i) hzRightPiece hzCarrier
  have hLR_disjoint : Disjoint L R := by
    refine Set.disjoint_left.2 ?_
    intro z hzL hzR
    dsimp [L, R] at hzL hzR
    rcases hzL with hzLeftHalfUnion | hzLeftPieceUnion
    · rcases Set.mem_iUnion.1 hzLeftHalfUnion with ⟨j, hzj⟩
      rcases Set.mem_iUnion.1 hzj with ⟨hj, hzLeftHalf⟩
      rcases hzR with hzRightHalfUnion | hzRightPieceUnion
      · rcases Set.mem_iUnion.1 hzRightHalfUnion with ⟨k, hzk⟩
        rcases Set.mem_iUnion.1 hzk with ⟨hk, hzRightHalf⟩
        exact Set.disjoint_left.mp
          (localSideData.leftHalf_disjoint_rightHalf j hj k hk)
          hzLeftHalf hzRightHalf
      · rcases Set.mem_iUnion.1 hzRightPieceUnion with ⟨i, hzRightPiece⟩
        have hzRightCollar :
            z ∈ localSideData.vertexCollar i :=
          localSideData.rightSidePiece_subset_vertexCollar i hzRightPiece
        have hzLeftPiece :
            z ∈ localSideData.leftSidePiece i :=
          localSideData.leftHalf_inter_vertexCollar_subset_leftSidePiece
            j hj i ⟨hzLeftHalf, hzRightCollar⟩
        exact Set.disjoint_left.mp
          (localSideData.local_sidePieces_disjoint i)
          hzLeftPiece hzRightPiece
    · rcases Set.mem_iUnion.1 hzLeftPieceUnion with ⟨i, hzLeftPiece⟩
      rcases hzR with hzRightHalfUnion | hzRightPieceUnion
      · rcases Set.mem_iUnion.1 hzRightHalfUnion with ⟨k, hzk⟩
        rcases Set.mem_iUnion.1 hzk with ⟨hk, hzRightHalf⟩
        have hzLeftCollar :
            z ∈ localSideData.vertexCollar i :=
          localSideData.leftSidePiece_subset_vertexCollar i hzLeftPiece
        have hzRightPiece :
            z ∈ localSideData.rightSidePiece i :=
          localSideData.rightHalf_inter_vertexCollar_subset_rightSidePiece
            k hk i ⟨hzRightHalf, hzLeftCollar⟩
        exact Set.disjoint_left.mp
          (localSideData.local_sidePieces_disjoint i)
          hzLeftPiece hzRightPiece
      · rcases Set.mem_iUnion.1 hzRightPieceUnion with ⟨k, hzRightPiece⟩
        by_cases hik : i = k
        · subst k
          exact Set.disjoint_left.mp
            (localSideData.local_sidePieces_disjoint i)
            hzLeftPiece hzRightPiece
        · have hzLeftCollar :
              z ∈ localSideData.vertexCollar i :=
            localSideData.leftSidePiece_subset_vertexCollar i hzLeftPiece
          have hzRightCollar :
              z ∈ localSideData.vertexCollar k :=
            localSideData.rightSidePiece_subset_vertexCollar k hzRightPiece
          have hzLeftDisk :
              z ∈ vertexLocalPieces.vertexDisk i :=
            localSideData.vertexCollar_subset_vertexDisk i hzLeftCollar
          have hzRightDisk :
              z ∈ vertexLocalPieces.vertexDisk k :=
            localSideData.vertexCollar_subset_vertexDisk k hzRightCollar
          have hzRightClosed :
              z ∈
                Metric.closedBall γ.vertices[k.1] (controlRadii.radius k) :=
            vertexLocalPieces.vertexDisk_subset_closed_control_disk k hzRightDisk
          exact Set.disjoint_left.mp
            (vertexLocalPieces.vertexDisk_disjoint_other_control_disks
              (i := i) (k := k) hik)
            hzLeftDisk hzRightClosed
  have hCollar_without_arc : C \ γ.relativeInterior = L ∪ R := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨hzC, hzNotRel⟩
      dsimp [C, L, R] at hzC ⊢
      rcases hzC with hzTubeUnion | hzVertexUnion
      · rcases Set.mem_iUnion.1 hzTubeUnion with ⟨j, hzj⟩
        rcases Set.mem_iUnion.1 hzj with ⟨hj, hzTube⟩
        have hzTubeWithout :
            z ∈ sep.tube j hj \ γ.relativeInterior := ⟨hzTube, hzNotRel⟩
        have hTubeWithout :=
          PolygonalArcMiddleTubeWithoutRelativeInterior γ controlRadii middleSegments
            forbiddenMargins orientedTubes vertexLocalPieces localSideData j hj
        rw [hTubeWithout] at hzTubeWithout
        rcases hzTubeWithout with hzLeftHalf | hzRightHalf
        · left
          left
          exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hj, hzLeftHalf⟩⟩
        · right
          left
          exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hj, hzRightHalf⟩⟩
      · rcases Set.mem_iUnion.1 hzVertexUnion with ⟨i, hzCollar⟩
        have hzVertexWithout :
            z ∈ localSideData.vertexCollar i \ γ.relativeInterior :=
          ⟨hzCollar, hzNotRel⟩
        rw [localSideData.vertexCollar_without_arc i] at hzVertexWithout
        rcases hzVertexWithout with hzLeftPiece | hzRightPiece
        · left
          right
          exact Set.mem_iUnion.2 ⟨i, hzLeftPiece⟩
        · right
          right
          exact Set.mem_iUnion.2 ⟨i, hzRightPiece⟩
    · intro hz
      rcases hz with hzL | hzR
      · refine ⟨hL_subset_C hzL, ?_⟩
        intro hzRel
        have hzCarrier : z ∈ γ.carrier := by
          rw [γ.relativeInterior_eq] at hzRel
          exact hzRel.1
        exact Set.disjoint_left.mp hL_disjoint_carrier hzL hzCarrier
      · refine ⟨hR_subset_C hzR, ?_⟩
        intro hzRel
        have hzCarrier : z ∈ γ.carrier := by
          rw [γ.relativeInterior_eq] at hzRel
          exact hzRel.1
        exact Set.disjoint_left.mp hR_disjoint_carrier hzR hzCarrier
  exact ⟨hL_disjoint_carrier, hR_disjoint_carrier, hLR_disjoint,
    hCollar_without_arc⟩
