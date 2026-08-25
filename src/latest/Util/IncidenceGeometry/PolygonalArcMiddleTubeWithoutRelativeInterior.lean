import Util.IncidenceGeometry.PolygonalArcCollarLocalSideData
import Util.IncidenceGeometry.PolygonalArcOpenSegmentSubsetRelativeInterior

open Classical
noncomputable section

lemma PolygonalArcMiddleTubeWithoutRelativeInterior
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
        forbiddenMargins orientedTubes vertexLocalPieces)
    (j : ℕ) (hj : j + 1 < γ.vertices.length) :
    orientedTubes.toPolygonalArcCollarSeparatedTubeData.tube j hj \ γ.relativeInterior =
      orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf j hj ∪
        orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf j hj := by
  let sep := orientedTubes.toPolygonalArcCollarSeparatedTubeData
  change sep.tube j hj \ γ.relativeInterior = sep.leftHalf j hj ∪ sep.rightHalf j hj
  ext z
  constructor
  · intro hz
    rcases hz with ⟨hzTube, hzNotRel⟩
    rw [sep.tube_eq j hj] at hzTube
    rcases hzTube with ⟨t, ht, s, hs, rfl⟩
    have hs_ne : s ≠ 0 := by
      intro hs0
      apply hzNotRel
      have htOpen :
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t ∈
            openSegment ℝ γ.vertices[j] γ.vertices[j + 1] := by
        rw [openSegment_eq_image_lineMap]
        refine ⟨t, ?_, rfl⟩
        exact ⟨(sep.lowerParam_pos j hj).trans ht.1,
          ht.2.trans (sep.upperParam_lt_one j hj)⟩
      have hrel :=
        PolygonalArcOpenSegmentSubsetRelativeInterior γ j hj htOpen
      simpa [hs0] using hrel
    rcases lt_or_gt_of_ne hs_ne with hs_neg | hs_pos
    · right
      rw [sep.rightHalf_eq j hj]
      exact ⟨t, ht, s, ⟨hs.1, hs_neg⟩, rfl⟩
    · left
      rw [sep.leftHalf_eq j hj]
      exact ⟨t, ht, s, ⟨hs_pos, hs.2⟩, rfl⟩
  · intro hz
    rcases hz with hzLeft | hzRight
    · refine ⟨sep.leftHalf_subset_tube j hj hzLeft, ?_⟩
      intro hzRel
      have hzCarrier : z ∈ γ.carrier := by
        rw [γ.relativeInterior_eq] at hzRel
        exact hzRel.1
      exact Set.disjoint_left.mp (localSideData.leftHalf_disjoint_carrier j hj)
        hzLeft hzCarrier
    · refine ⟨sep.rightHalf_subset_tube j hj hzRight, ?_⟩
      intro hzRel
      have hzCarrier : z ∈ γ.carrier := by
        rw [γ.relativeInterior_eq] at hzRel
        exact hzRel.1
      exact Set.disjoint_left.mp (localSideData.rightHalf_disjoint_carrier j hj)
        hzRight hzCarrier
