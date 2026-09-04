import Util.IncidenceGeometry.ComplementComponent
import Util.IncidenceGeometry.DrawingFaceComponent
import Util.IncidenceGeometry.FinitePolygonalSetComplementComponents
import Util.IncidenceGeometry.OrdinaryDrawingImage
import Util.IncidenceGeometry.OrdinaryDrawingImageFinitePolygonalSet
import Util.IncidenceGeometry.OrdinaryPolygonalDrawing
import Util.IncidenceGeometry.PlaneDrawingDartSectorCompatibility
import Util.IncidenceGeometry.PlaneDrawingDartSectorData
import Util.IncidenceGeometry.PlaneFaceData

open Classical
noncomputable section

lemma PlaneFaceDataExists {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (hD : D.crossingSet.card = 0) :
    Nonempty (PlaneFaceData G D) := by
  classical
  rcases OrdinaryDrawingImageFinitePolygonalSet G D with ⟨K, hK⟩
  rcases FinitePolygonalSetComplementComponents K with
    ⟨Face, faceFintype, faceSet, hface_component_K, hfaces_complete_K,
      hcomplement_point_face_K⟩
  let : Fintype Face := faceFintype
  let FaceLift := ULift Face
  let : Fintype FaceLift := inferInstance
  let liftedFaceSet : FaceLift → Set (EuclideanSpace ℝ (Fin 2)) :=
    fun F => faceSet F.down
  have face_component :
      ∀ F : FaceLift, DrawingFaceComponent G D (liftedFaceSet F) := by
    intro F
    simpa [liftedFaceSet, DrawingFaceComponent, hK] using hface_component_K F.down
  have faces_complete :
      ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
        DrawingFaceComponent G D C → ∃! F : FaceLift, liftedFaceSet F = C := by
    intro C hC
    rcases hfaces_complete_K C (by simpa [DrawingFaceComponent, hK] using hC) with
      ⟨F, hF, hF_unique⟩
    refine ⟨ULift.up F, by simpa [liftedFaceSet] using hF, ?_⟩
    intro F' hF'
    apply ULift.ext
    exact hF_unique F'.down (by simpa [liftedFaceSet] using hF')
  have complement_point_face :
      ∀ p : EuclideanSpace ℝ (Fin 2),
        p ∈ (OrdinaryDrawingImage G D)ᶜ → ∃! F : FaceLift, p ∈ liftedFaceSet F := by
    intro p hp
    rcases hcomplement_point_face_K p (by simpa [hK] using hp) with
      ⟨F, hF, hF_unique⟩
    refine ⟨ULift.up F, by simpa [liftedFaceSet] using hF, ?_⟩
    intro F' hF'
    apply ULift.ext
    exact hF_unique F'.down (by simpa [liftedFaceSet] using hF')
  rcases PlaneDrawingDartSectorCompatibility G D hD with ⟨B⟩
  let leftComponent : G.Dart → Set (EuclideanSpace ℝ (Fin 2)) :=
    fun d => Classical.choose (ExistsUnique.exists (B.leftSide_unique_face_component d))
  have leftComponent_spec :
      ∀ d : G.Dart,
        DrawingFaceComponent G D (leftComponent d) ∧
          B.leftSideStrip d ⊆ leftComponent d := by
    intro d
    exact Classical.choose_spec (ExistsUnique.exists (B.leftSide_unique_face_component d))
  let leftFace : G.Dart → FaceLift :=
    fun d =>
      Classical.choose
        (ExistsUnique.exists
          (faces_complete (leftComponent d) (leftComponent_spec d).1))
  have leftFace_eq_component :
      ∀ d : G.Dart, liftedFaceSet (leftFace d) = leftComponent d := by
    intro d
    exact
      (Classical.choose_spec
        (ExistsUnique.exists
          (faces_complete (leftComponent d) (leftComponent_spec d).1)))
  have leftFace_contains :
      ∀ d : G.Dart, B.leftSideStrip d ⊆ liftedFaceSet (leftFace d) := by
    intro d x hx
    have hx_component : x ∈ leftComponent d := (leftComponent_spec d).2 hx
    simpa [leftFace_eq_component d] using hx_component
  refine ⟨{
    isPlane := hD
    Face := FaceLift
    faceFintype := inferInstance
    faceSet := liftedFaceSet
    face_component := face_component
    faces_complete := faces_complete
    complement_point_face := complement_point_face
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
    faceDegree := fun F =>
      letI : DecidablePred (fun d : G.Dart => leftFace d = F) :=
        fun d => Classical.propDecidable (leftFace d = F)
      (Finset.univ.filter (fun d : G.Dart => leftFace d = F)).card
    faceDegree_eq := by
      intro F
      exact
        (@Fintype.card_subtype G.Dart inferInstance
          (fun d : G.Dart => leftFace d = F)
          (@Subtype.fintype G.Dart (fun d : G.Dart => leftFace d = F)
            (fun d => Classical.propDecidable (leftFace d = F)) inferInstance)
          (fun d => Classical.propDecidable (leftFace d = F))).symm
  }⟩
