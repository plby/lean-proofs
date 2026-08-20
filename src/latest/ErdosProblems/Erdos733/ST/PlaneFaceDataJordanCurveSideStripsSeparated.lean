import ErdosProblems.Erdos733.ST.ComplementComponent
import ErdosProblems.Erdos733.ST.ComplementComponentAbsorbsConnectedSubset
import ErdosProblems.Erdos733.ST.DrawingFaceComponent
import ErdosProblems.Erdos733.ST.OrdinaryDrawingImage
import ErdosProblems.Erdos733.ST.PlaneFaceData
import ErdosProblems.Erdos733.ST.PolygonalArc
import ErdosProblems.Erdos733.ST.PolygonalArcOpenSegmentSubsetRelativeInterior
import ErdosProblems.Erdos733.ST.PolygonalJordanSeparation
import ErdosProblems.Erdos733.ST.PolygonalSideStrips
import ErdosProblems.Erdos733.ST.SimpleClosedPolygonalCurve

open Classical
noncomputable section

-- [TABLET NODE: PlaneFaceDataJordanCurveSideStripsSeparated]
lemma PlaneFaceDataJordanCurveSideStripsSeparated {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (A : PlaneFaceData G D)
    (J : SimpleClosedPolygonalCurve) (d : G.Dart)
    (hJsubset : J.carrier ⊆ OrdinaryDrawingImage G D)
    (hedge :
      ∃ γ : {γ : PolygonalArc // γ ∈ J.edgeArcs},
        γ.1.carrier = (A.dartArc d).carrier ∧
          γ.1.source = (A.dartArc d).source ∧
            γ.1.target = (A.dartArc d).target) :
    ∃ Cleft Cright : Set (EuclideanSpace ℝ (Fin 2)),
      ComplementComponent J.carrier Cleft ∧
        ComplementComponent J.carrier Cright ∧
          Cleft ≠ Cright ∧
            (A.leftSideStrip d).Nonempty ∧
              (A.leftSideStrip d.symm).Nonempty ∧
                A.leftSideStrip d ⊆ Cleft ∧
                  A.leftSideStrip d.symm ⊆ Cright := by
-- BODY
  classical
  rcases hedge with ⟨γJ, hγcarrier, hγsource, hγtarget⟩
  rcases A.sideStripData d with ⟨S, hSleft, hSright⟩
  have hSrightStored : A.leftSideStrip d.symm = S.rightStrip := by
    exact (A.rightSideStrip_eq_leftSideStrip_symm d).symm.trans hSright
  have hrel :
      γJ.1.relativeInterior = (A.dartArc d).relativeInterior := by
    rw [γJ.1.relativeInterior_eq, (A.dartArc d).relativeInterior_eq,
      hγcarrier, hγsource, hγtarget]
  have hγJRel_subset_J : γJ.1.relativeInterior ⊆ J.carrier := by
    intro y hy
    have hyCarrier : y ∈ γJ.1.carrier := by
      rw [γJ.1.relativeInterior_eq] at hy
      exact hy.1
    rw [J.carrier_eq]
    exact Set.mem_iUnion.2 ⟨γJ, hyCarrier⟩
  have h01 : 0 + 1 < γJ.1.vertices.length := by
    have hlen : 2 ≤ γJ.1.vertices.length := γJ.1.length_ge_two
    omega
  let x : EuclideanSpace ℝ (Fin 2) :=
    midpoint ℝ γJ.1.vertices[0] γJ.1.vertices[0 + 1]
  have hxOpen :
      x ∈ openSegment ℝ γJ.1.vertices[0] γJ.1.vertices[0 + 1] := by
    simpa [x] using
      (midpoint_mem_openSegment (𝕜 := ℝ) γJ.1.vertices[0]
        γJ.1.vertices[0 + 1])
  have hxJ : x ∈ γJ.1.relativeInterior :=
    PolygonalArcOpenSegmentSubsetRelativeInterior γJ.1 0 h01 hxOpen
  have hxA : x ∈ (A.dartArc d).relativeInterior := by
    simpa [hrel] using hxJ
  have hxCollar : x ∈ S.collar := S.relativeInterior_subset_collar hxA
  have meet_collar_of_closure :
      ∀ {T : Set (EuclideanSpace ℝ (Fin 2))},
        x ∈ closure T → (S.collar ∩ T).Nonempty := by
    intro T hxClosure
    exact (mem_closure_iff_nhds.mp hxClosure) S.collar
      (S.collar_open.mem_nhds hxCollar)
  have hSleftNonempty : S.leftStrip.Nonempty := by
    rcases meet_collar_of_closure (S.relativeInterior_subset_closure_left hxA) with
      ⟨y, _hyCollar, hyLeft⟩
    exact ⟨y, hyLeft⟩
  have hSrightNonempty : S.rightStrip.Nonempty := by
    rcases meet_collar_of_closure (S.relativeInterior_subset_closure_right hxA) with
      ⟨y, _hyCollar, hyRight⟩
    exact ⟨y, hyRight⟩
  have hFaceComponent :
      ∀ F : A.Face,
        ComplementComponent (OrdinaryDrawingImage G D) (A.faceSet F) := by
    intro F
    simpa [DrawingFaceComponent] using A.face_component F
  have hSleftSubsetJ : S.leftStrip ⊆ J.carrierᶜ := by
    intro y hyLeft
    have hyStored : y ∈ A.leftSideStrip d := by
      simpa [hSleft] using hyLeft
    have hyFace : y ∈ A.faceSet (A.leftFace d) :=
      A.leftFace_contains d hyStored
    have hyImageCompl : y ∈ (OrdinaryDrawingImage G D)ᶜ :=
      (hFaceComponent (A.leftFace d)).2.1 hyFace
    intro hyJ
    exact hyImageCompl (hJsubset hyJ)
  have hSrightSubsetJ : S.rightStrip ⊆ J.carrierᶜ := by
    intro y hyRight
    have hyStored : y ∈ A.leftSideStrip d.symm := by
      simpa [hSrightStored] using hyRight
    have hyFace : y ∈ A.faceSet (A.leftFace d.symm) :=
      A.leftFace_contains d.symm hyStored
    have hyImageCompl : y ∈ (OrdinaryDrawingImage G D)ᶜ :=
      (hFaceComponent (A.leftFace d.symm)).2.1 hyFace
    intro hyJ
    exact hyImageCompl (hJsubset hyJ)
  rcases PolygonalJordanSeparation J with
    ⟨inside, outside, hinside_ne_outside, hinsideComp, houtsideComp,
      _hcomponent_cases, _hpoint_cases, _hinsideBounded, _houtsideUnbounded,
      _hinsidePath, _houtsidePath, _hfrontierInside, _hfrontierOutside,
      hlocalSides⟩
  have hnot_both_inside_outside :
      ∀ y : EuclideanSpace ℝ (Fin 2), y ∈ inside → y ∈ outside → False := by
    intro y hyInside hyOutside
    have houtside_subset_inside : outside ⊆ inside :=
      ComplementComponentAbsorbsConnectedSubset J.carrier inside outside
        hinsideComp houtsideComp.1 houtsideComp.2.1 houtsideComp.2.2.1
        ⟨y, hyInside, hyOutside⟩
    have hinside_subset_outside : inside ⊆ outside :=
      ComplementComponentAbsorbsConnectedSubset J.carrier outside inside
        houtsideComp hinsideComp.1 hinsideComp.2.1 hinsideComp.2.2.1
        ⟨y, hyOutside, hyInside⟩
    exact hinside_ne_outside
      (Set.Subset.antisymm hinside_subset_outside houtside_subset_inside)
  have hSleft_subset_inside_of_mem :
      ∀ ⦃y : EuclideanSpace ℝ (Fin 2)⦄,
        y ∈ S.leftStrip → y ∈ inside → S.leftStrip ⊆ inside := by
    intro y hyLeft hyInside
    exact ComplementComponentAbsorbsConnectedSubset J.carrier inside S.leftStrip
      hinsideComp hSleftNonempty hSleftSubsetJ S.left_connected
      ⟨y, hyInside, hyLeft⟩
  have hSleft_subset_outside_of_mem :
      ∀ ⦃y : EuclideanSpace ℝ (Fin 2)⦄,
        y ∈ S.leftStrip → y ∈ outside → S.leftStrip ⊆ outside := by
    intro y hyLeft hyOutside
    exact ComplementComponentAbsorbsConnectedSubset J.carrier outside S.leftStrip
      houtsideComp hSleftNonempty hSleftSubsetJ S.left_connected
      ⟨y, hyOutside, hyLeft⟩
  have hSright_subset_inside_of_mem :
      ∀ ⦃y : EuclideanSpace ℝ (Fin 2)⦄,
        y ∈ S.rightStrip → y ∈ inside → S.rightStrip ⊆ inside := by
    intro y hyRight hyInside
    exact ComplementComponentAbsorbsConnectedSubset J.carrier inside S.rightStrip
      hinsideComp hSrightNonempty hSrightSubsetJ S.right_connected
      ⟨y, hyInside, hyRight⟩
  have hSright_subset_outside_of_mem :
      ∀ ⦃y : EuclideanSpace ℝ (Fin 2)⦄,
        y ∈ S.rightStrip → y ∈ outside → S.rightStrip ⊆ outside := by
    intro y hyRight hyOutside
    exact ComplementComponentAbsorbsConnectedSubset J.carrier outside S.rightStrip
      houtsideComp hSrightNonempty hSrightSubsetJ S.right_connected
      ⟨y, hyOutside, hyRight⟩
  have collar_point_in_strips_of_J_compl :
      ∀ ⦃y : EuclideanSpace ℝ (Fin 2)⦄,
        y ∈ S.collar → y ∈ J.carrierᶜ → y ∈ S.leftStrip ∪ S.rightStrip := by
    intro y hyCollar hyJcompl
    have hyNotRel : y ∉ (A.dartArc d).relativeInterior := by
      intro hyRel
      have hyJRel : y ∈ γJ.1.relativeInterior := by
        simpa [hrel] using hyRel
      exact hyJcompl (hγJRel_subset_J hyJRel)
    have hyDiff : y ∈ S.collar \ (A.dartArc d).relativeInterior :=
      ⟨hyCollar, hyNotRel⟩
    simpa [S.collar_without_arc] using hyDiff
  have finish :
      (∃ y : EuclideanSpace ℝ (Fin 2), y ∈ S.collar ∧ y ∈ inside) →
        (∃ y : EuclideanSpace ℝ (Fin 2), y ∈ S.collar ∧ y ∈ outside) →
          ∃ Cleft Cright : Set (EuclideanSpace ℝ (Fin 2)),
            ComplementComponent J.carrier Cleft ∧
              ComplementComponent J.carrier Cright ∧
                Cleft ≠ Cright ∧
                  (A.leftSideStrip d).Nonempty ∧
                    (A.leftSideStrip d.symm).Nonempty ∧
                      A.leftSideStrip d ⊆ Cleft ∧
                        A.leftSideStrip d.symm ⊆ Cright := by
    rintro ⟨yI, hyICollar, hyIinside⟩ ⟨yO, hyOCollar, hyOoutside⟩
    have hyIUnion : yI ∈ S.leftStrip ∪ S.rightStrip :=
      collar_point_in_strips_of_J_compl hyICollar (hinsideComp.2.1 hyIinside)
    have hyOUnion : yO ∈ S.leftStrip ∪ S.rightStrip :=
      collar_point_in_strips_of_J_compl hyOCollar (houtsideComp.2.1 hyOoutside)
    have hLeftStoredNonempty : (A.leftSideStrip d).Nonempty := by
      simpa [hSleft] using hSleftNonempty
    have hRightStoredNonempty : (A.leftSideStrip d.symm).Nonempty := by
      simpa [hSrightStored] using hSrightNonempty
    rcases hyIUnion with hyILeft | hyIRight
    · have hLeftInside : S.leftStrip ⊆ inside :=
        hSleft_subset_inside_of_mem hyILeft hyIinside
      rcases hyOUnion with hyOLeft | hyORight
      · exact False.elim
          (hnot_both_inside_outside yO (hLeftInside hyOLeft) hyOoutside)
      · have hRightOutside : S.rightStrip ⊆ outside :=
          hSright_subset_outside_of_mem hyORight hyOoutside
        refine ⟨inside, outside, hinsideComp, houtsideComp, hinside_ne_outside,
          hLeftStoredNonempty, hRightStoredNonempty, ?_, ?_⟩
        · intro y hy
          exact hLeftInside (by simpa [hSleft] using hy)
        · intro y hy
          exact hRightOutside (by simpa [hSrightStored] using hy)
    · have hRightInside : S.rightStrip ⊆ inside :=
        hSright_subset_inside_of_mem hyIRight hyIinside
      rcases hyOUnion with hyOLeft | hyORight
      · have hLeftOutside : S.leftStrip ⊆ outside :=
          hSleft_subset_outside_of_mem hyOLeft hyOoutside
        refine ⟨outside, inside, houtsideComp, hinsideComp, hinside_ne_outside.symm,
          hLeftStoredNonempty, hRightStoredNonempty, ?_, ?_⟩
        · intro y hy
          exact hLeftOutside (by simpa [hSleft] using hy)
        · intro y hy
          exact hRightInside (by simpa [hSrightStored] using hy)
      · exact False.elim
          (hnot_both_inside_outside yO (hRightInside hyORight) hyOoutside)
  rcases hlocalSides γJ with ⟨SJ, hSJ⟩
  rcases hSJ with hSJ | hSJ
  · rcases hSJ with ⟨hSJleftInside, hSJrightOutside⟩
    apply finish
    · rcases meet_collar_of_closure (SJ.relativeInterior_subset_closure_left hxJ) with
        ⟨y, hyCollar, hySJLeft⟩
      exact ⟨y, hyCollar, hSJleftInside hySJLeft⟩
    · rcases meet_collar_of_closure (SJ.relativeInterior_subset_closure_right hxJ) with
        ⟨y, hyCollar, hySJRight⟩
      exact ⟨y, hyCollar, hSJrightOutside hySJRight⟩
  · rcases hSJ with ⟨hSJleftOutside, hSJrightInside⟩
    apply finish
    · rcases meet_collar_of_closure (SJ.relativeInterior_subset_closure_right hxJ) with
        ⟨y, hyCollar, hySJRight⟩
      exact ⟨y, hyCollar, hSJrightInside hySJRight⟩
    · rcases meet_collar_of_closure (SJ.relativeInterior_subset_closure_left hxJ) with
        ⟨y, hyCollar, hySJLeft⟩
      exact ⟨y, hyCollar, hSJleftOutside hySJLeft⟩
