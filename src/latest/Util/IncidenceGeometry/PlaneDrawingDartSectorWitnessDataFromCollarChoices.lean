import Util.IncidenceGeometry.PlaneDrawingDartCollarChoiceData
import Util.IncidenceGeometry.PlaneDrawingDartSectorWitnessData
import Util.IncidenceGeometry.PlaneDrawingDartSideStripData
import Util.IncidenceGeometry.PlaneDrawingDartVertexStarData
import Util.IncidenceGeometry.PlaneDrawingDartVertexSectorGeometry
import Util.IncidenceGeometry.PolygonalArcCollarLocalSideData
import Util.IncidenceGeometry.PolygonalArcCollarVertexLocalPieceData
import Util.IncidenceGeometry.PolygonalArcInitialEndpointDiskCappedTaperAttachmentStrengthening
import Util.IncidenceGeometry.PolygonalArcInitialEndpointLeftCone
import Util.IncidenceGeometry.PolygonalArcTerminalEndpointDiskCappedTaperAttachmentStrengthening
import Util.IncidenceGeometry.PolygonalArcTerminalEndpointLeftCone
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open Classical
noncomputable section

lemma PlaneDrawingDartSectorWitnessDataFromCollarChoices {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (A : PlaneDrawingDartArcData G D)
    (C : PlaneDrawingDartVertexSectorGeometry G D A)
    (P : PlaneDrawingDartCollarChoiceData G D A C)
    (S : PlaneDrawingDartSideStripData G D A C.star)
    (hleft : ∀ d : G.Dart, S.leftSideStrip d = (P.sideStrips d).leftStrip) :
    Nonempty (PlaneDrawingDartSectorWitnessData G D A C.star S) := by
  refine ⟨?_⟩
  refine
    { successor_clockwise_sector := ?_
      vertex_sector_coverage := ?_ }
  · intro d
    refine ⟨C.successorSector d, C.successorSector_isOpen d,
      C.successorSector_isConnected d, C.successorSector_subset_localDisk d,
      C.successorSector_subset_complement d, ?_, ?_,
      C.successorSector_disjoint_radialGerm d⟩
    · simpa [hleft d] using P.successorSector_meets_leftStrip d
    · simpa [hleft (C.star.successor d)] using
        P.successorSector_meets_successor_leftStrip d
  · intro v y hv hyball hyne hycomp
    obtain ⟨d, hdv, hysector⟩ :=
      C.vertex_sector_coverage v y hv hyball hyne hycomp
    subst v
    refine ⟨d, rfl, C.successorSector d, hysector, C.successorSector_isOpen d,
      C.successorSector_isConnected d, C.successorSector_subset_localDisk d,
      C.successorSector_subset_complement d, ?_, ?_,
      C.successorSector_disjoint_radialGerm d⟩
    · simpa [hleft d] using P.successorSector_meets_leftStrip d
    · simpa [hleft (C.star.successor d)] using
        P.successorSector_meets_successor_leftStrip d
