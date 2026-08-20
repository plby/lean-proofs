import ErdosProblems.Erdos733.ST.PlaneFaceData

open Classical
noncomputable section

-- [TABLET NODE: PlaneFaceDataEdgeInteriorLocalSideIncidentFace]
lemma PlaneFaceDataEdgeInteriorLocalSideIncidentFace {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (A : PlaneFaceData G D) :
    ∀ (F : A.Face) (d : G.Dart) (x : EuclideanSpace ℝ (Fin 2)),
      x ∈ (A.dartArc d).relativeInterior →
        ∃ U : Set (EuclideanSpace ℝ (Fin 2)),
          IsOpen U ∧ x ∈ U ∧
            ∀ y : EuclideanSpace ℝ (Fin 2),
              y ∈ A.faceSet F →
                y ∈ U →
                  y ∈ (OrdinaryDrawingImage G D)ᶜ →
                    ∃ a : G.Dart, A.leftFace a = F := by
-- BODY
  intro F d x hx
  rcases A.localComplement_subset_sideStrips d x hx with
    ⟨U, hUopen, hxU, hUsubset⟩
  refine ⟨U, hUopen, hxU, ?_⟩
  intro y hyF hyU hyCompl
  have hySide : y ∈ A.leftSideStrip d ∪ A.leftSideStrip d.symm :=
    hUsubset ⟨hyU, hyCompl⟩
  rcases hySide with hyLeft | hyRight
  · have hyLeftFace : y ∈ A.faceSet (A.leftFace d) :=
      A.leftFace_contains d hyLeft
    rcases A.complement_point_face y hyCompl with ⟨F0, _hyF0, huniq⟩
    have hleft : A.leftFace d = F0 := huniq (A.leftFace d) hyLeftFace
    have hF : F = F0 := huniq F hyF
    exact ⟨d, hleft.trans hF.symm⟩
  · have hyRightFace : y ∈ A.faceSet (A.leftFace d.symm) :=
      A.leftFace_contains d.symm hyRight
    rcases A.complement_point_face y hyCompl with ⟨F0, _hyF0, huniq⟩
    have hright : A.leftFace d.symm = F0 := huniq (A.leftFace d.symm) hyRightFace
    have hF : F = F0 := huniq F hyF
    exact ⟨d.symm, hright.trans hF.symm⟩
