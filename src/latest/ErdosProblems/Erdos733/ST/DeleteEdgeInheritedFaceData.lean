import ErdosProblems.Erdos733.ST.DeletedEdgeComplementComponents
import ErdosProblems.Erdos733.ST.PlaneFaceData
import ErdosProblems.Erdos733.ST.DrawingFaceComponent
import ErdosProblems.Erdos733.ST.ComplementComponent
import ErdosProblems.Erdos733.ST.OrdinaryDrawingImage
import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawing
import ErdosProblems.Erdos733.ST.PolygonalArc
import ErdosProblems.Erdos733.ST.PolygonalArcCollar
import ErdosProblems.Erdos733.ST.PolygonalSideStrips
import ErdosProblems.Erdos733.ST.PlaneDrawingDartSectorCompatibility
import ErdosProblems.Erdos733.ST.PlaneDrawingDartSectorData
import ErdosProblems.Erdos733.ST.OrdinaryDrawingImageCompact
import ErdosProblems.Erdos733.ST.OpenConnectedComponentPolygonallyConnected
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Classical
noncomputable section

-- [TABLET NODE: DeleteEdgeInheritedFaceData]
lemma DeleteEdgeInheritedFaceData {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (hD : D.crossingSet.card = 0) (A : PlaneFaceData G D) (e : G.edgeFinset) :
    let Gdel : SimpleGraph V := G.deleteEdges {e.1}
    ∃ Ddel : OrdinaryPolygonalDrawing Gdel,
      ∃ Adel : PlaneFaceData Gdel Ddel,
        Ddel.crossingSet.card = 0 ∧
          Ddel.vertexPlacement = D.vertexPlacement ∧
            ∀ ed : Gdel.edgeFinset,
              ∃ eG : G.edgeFinset, eG.1 = ed.1 ∧ eG.1 ≠ e.1 ∧
                Ddel.edgeArc ed = D.edgeArc eG := by
-- BODY
  classical
  let Gdel : SimpleGraph V := G.deleteEdges {e.1}
  change
    ∃ Ddel : OrdinaryPolygonalDrawing Gdel,
      ∃ Adel : PlaneFaceData Gdel Ddel,
        Ddel.crossingSet.card = 0 ∧
          Ddel.vertexPlacement = D.vertexPlacement ∧
            ∀ ed : Gdel.edgeFinset,
              ∃ eG : G.edgeFinset, eG.1 = ed.1 ∧ eG.1 ≠ e.1 ∧
                Ddel.edgeArc ed = D.edgeArc eG
  let oldEdge : Gdel.edgeFinset → G.edgeFinset := fun ed =>
    ⟨ed.1, by
      have hedSet : ed.1 ∈ Gdel.edgeSet := SimpleGraph.mem_edgeFinset.mp ed.2
      have hedOld : ed.1 ∈ G.edgeSet ∧ ed.1 ∉ ({e.1} : Set (Sym2 V)) := by
        simpa [Gdel, SimpleGraph.edgeSet_deleteEdges] using hedSet
      exact SimpleGraph.mem_edgeFinset.mpr hedOld.1⟩
  have oldEdge_val : ∀ ed : Gdel.edgeFinset, (oldEdge ed).1 = ed.1 := by
    intro ed
    rfl
  have oldEdge_ne_deleted : ∀ ed : Gdel.edgeFinset, (oldEdge ed).1 ≠ e.1 := by
    intro ed hdel
    have hedSet : ed.1 ∈ Gdel.edgeSet := SimpleGraph.mem_edgeFinset.mp ed.2
    have hedOld : ed.1 ∈ G.edgeSet ∧ ed.1 ∉ ({e.1} : Set (Sym2 V)) := by
      simpa [Gdel, SimpleGraph.edgeSet_deleteEdges] using hedSet
    exact hedOld.2 (by simpa [oldEdge_val ed, hdel])
  have oldEdge_injective : Function.Injective oldEdge := by
    intro ed₁ ed₂ h
    apply Subtype.ext
    simpa [oldEdge_val] using (congrArg Subtype.val h)
  let Ddel : OrdinaryPolygonalDrawing Gdel :=
    { vertexPlacement := D.vertexPlacement
      vertexPlacement_injective := D.vertexPlacement_injective
      edgeArc := fun ed => D.edgeArc (oldEdge ed)
      edgeArc_endpoints := by
        intro ed
        rcases D.edgeArc_endpoints (oldEdge ed) with
          ⟨u, v, huv, hedge, hends⟩
        refine ⟨u, v, ?_, ?_, hends⟩
        · have hnot : s(u, v) ∉ ({e.1} : Set (Sym2 V)) := by
            intro hs
            exact oldEdge_ne_deleted ed (hedge.trans (by simpa using hs))
          simpa [Gdel, hnot] using huv
        · simpa [oldEdge_val ed] using hedge
      crossingSet := ∅
      no_vertex_in_edge_interior := by
        intro v ed
        exact D.no_vertex_in_edge_interior v (oldEdge ed)
      no_three_edge_interiors_meet := by
        intro ed₁ ed₂ ed₃ p h₁₂ h₁₃ h₂₃ hp₁ hp₂ hp₃
        exact D.no_three_edge_interiors_meet
          (oldEdge_injective.ne h₁₂) (oldEdge_injective.ne h₁₃)
          (oldEdge_injective.ne h₂₃) hp₁ hp₂ hp₃
      transverse_intersections := by
        intro ed₁ ed₂ p h₁₂ hp₁ hp₂
        exact D.transverse_intersections (oldEdge_injective.ne h₁₂) hp₁ hp₂
      no_shared_nondegenerate_subarc := by
        intro ed₁ ed₂ h₁₂
        exact D.no_shared_nondegenerate_subarc (oldEdge_injective.ne h₁₂)
      crossingSet_spec := by
        intro p
        constructor
        · intro hp
          simpa using hp
        · rintro ⟨ed₁, ed₂, h₁₂, hp₁, hp₂⟩
          have hpOld : p ∈ D.crossingSet :=
            (D.crossingSet_spec p).2
              ⟨oldEdge ed₁, oldEdge ed₂, oldEdge_injective.ne h₁₂, hp₁, hp₂⟩
          have hDempty : D.crossingSet = ∅ := Finset.card_eq_zero.mp hD
          exfalso
          simpa [hDempty] using hpOld
      adjacentEdgeCrossingCount := 0
      adjacentEdgeCrossingCount_eq := by
        simp }
  have hDdel_crossing : Ddel.crossingSet.card = 0 := by
    simp [Ddel]
  have hvertex : Ddel.vertexPlacement = D.vertexPlacement := by
    rfl
  have hedges :
      ∀ ed : Gdel.edgeFinset,
        ∃ eG : G.edgeFinset, eG.1 = ed.1 ∧ eG.1 ≠ e.1 ∧
          Ddel.edgeArc ed = D.edgeArc eG := by
    intro ed
    exact ⟨oldEdge ed, oldEdge_val ed, oldEdge_ne_deleted ed, rfl⟩
  rcases D.edgeArc_endpoints e with ⟨u, v, huv, hedge, _hends⟩
  let d : G.Dart := ⟨(u, v), huv⟩
  have hd : d.edge = e.1 := by
    simpa [d, SimpleGraph.Dart.edge] using hedge.symm
  rcases
      DeletedEdgeComplementComponents G D hD A e Ddel hvertex hedges d hd with
    ⟨FaceDel, faceDelFintype, faceSetDel, componentOf, hcomplement,
      hcomponent_surj, hcomponent_eq, hfaceSetDel, hface_component,
      hfaces_complete, hcomplement_point_face⟩
  rcases PlaneDrawingDartSectorCompatibility Gdel Ddel hDdel_crossing with ⟨B⟩
  let leftComponent : Gdel.Dart → Set (EuclideanSpace ℝ (Fin 2)) := fun a =>
    Classical.choose (B.leftSide_unique_face_component a).exists
  have leftComponent_spec :
      ∀ a : Gdel.Dart,
        DrawingFaceComponent Gdel Ddel (leftComponent a) ∧
          B.leftSideStrip a ⊆ leftComponent a := by
    intro a
    exact (Classical.choose_spec
      (B.leftSide_unique_face_component a).exists)
  let leftFace : Gdel.Dart → FaceDel := fun a =>
    Classical.choose
      (hfaces_complete (leftComponent a) (leftComponent_spec a).1).exists
  have leftFace_component :
      ∀ a : Gdel.Dart, faceSetDel (leftFace a) = leftComponent a := by
    intro a
    exact (Classical.choose_spec
      (hfaces_complete (leftComponent a) (leftComponent_spec a).1).exists)
  have leftFace_contains :
      ∀ a : Gdel.Dart, B.leftSideStrip a ⊆ faceSetDel (leftFace a) := by
    intro a x hx
    rw [leftFace_component a]
    exact (leftComponent_spec a).2 hx
  let Adel : PlaneFaceData Gdel Ddel :=
    { isPlane := hDdel_crossing
      Face := FaceDel
      faceFintype := faceDelFintype
      faceSet := faceSetDel
      face_component := hface_component
      faces_complete := hfaces_complete
      complement_point_face := hcomplement_point_face
      dartEdge := B.dartEdge
      dartEdge_eq := B.dartEdge_eq
      dartArc := B.dartArc
      dartArc_carrier := B.dartArc_carrier
      dartArc_source := B.dartArc_source
      dartArc_target := B.dartArc_target
      leftSideStrip := B.leftSideStrip
      rightSideStrip := B.rightSideStrip
      sideStripData := B.sideStripData
      rightSideStrip_eq_leftSideStrip_symm := B.rightSideStrip_eq_leftSideStrip_symm
      localComplement_subset_sideStrips := B.localComplement_subset_sideStrips
      leftFace := leftFace
      leftFace_contains := leftFace_contains
      localDiskRadius := B.localDiskRadius
      localDiskRadius_pos := B.localDiskRadius_pos
      germDirection := B.germDirection
      germDirection_ne_zero := B.germDirection_ne_zero
      radialGerm := B.radialGerm
      radialGerm_eq_openSegment := B.radialGerm_eq_openSegment
      radialGerm_subset_dartArc := B.radialGerm_subset_dartArc
      localDisk_meets_drawing_only_incident_germs :=
        B.localDisk_meets_drawing_only_incident_germs
      clockwiseNext := B.clockwiseNext
      fullClockwiseTurn := B.fullClockwiseTurn
      fullClockwiseTurn_pos := B.fullClockwiseTurn_pos
      clockwiseTurn := B.clockwiseTurn
      clockwiseTurn_pos := B.clockwiseTurn_pos
      clockwiseTurn_le_full := B.clockwiseTurn_le_full
      clockwiseTurn_full_iff_same := B.clockwiseTurn_full_iff_same
      clockwiseNext_first_after := B.clockwiseNext_first_after
      clockwiseNext_eq_self_iff_isolated := B.clockwiseNext_eq_self_iff_isolated
      successor := B.successor
      successor_tail := B.successor_tail
      successor_eq_clockwiseNext := B.successor_eq_clockwiseNext
      successor_single_incident := B.successor_single_incident
      successor_clockwise_sector := B.successor_clockwise_sector
      vertex_sector_coverage := B.vertex_sector_coverage
      faceDegree := fun F => Fintype.card {a : Gdel.Dart // leftFace a = F}
      faceDegree_eq := by
        intro F
        rfl }
  exact ⟨Ddel, Adel, hDdel_crossing, hvertex, hedges⟩
