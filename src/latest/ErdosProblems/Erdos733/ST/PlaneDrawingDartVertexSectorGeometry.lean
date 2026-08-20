import ErdosProblems.Erdos733.ST.OrdinaryDrawingImage
import ErdosProblems.Erdos733.ST.PlaneDrawingDartVertexStarData
import ErdosProblems.Erdos733.ST.PolygonalArcInitialEndpointLeftCone
import ErdosProblems.Erdos733.ST.PolygonalArcTerminalEndpointLeftCone
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open Classical
noncomputable section

-- [TABLET NODE: PlaneDrawingDartVertexSectorGeometry]
structure PlaneDrawingDartVertexSectorGeometry {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (A : PlaneDrawingDartArcData G D) where
-- BODY
  star : PlaneDrawingDartVertexStarData G D A
  successorSector : G.Dart → Set (EuclideanSpace ℝ (Fin 2))
  successorSector_isOpen : ∀ d : G.Dart, IsOpen (successorSector d)
  successorSector_isConnected : ∀ d : G.Dart, IsConnected (successorSector d)
  successorSector_subset_localDisk :
    ∀ d : G.Dart,
      successorSector d ⊆
        Metric.ball (D.vertexPlacement d.toProd.2) (star.localDiskRadius d.toProd.2)
  successorSector_subset_complement :
    ∀ d : G.Dart, successorSector d ⊆ (OrdinaryDrawingImage G D)ᶜ
  successorSector_disjoint_radialGerm :
    ∀ (d : G.Dart) (e : {e : G.Dart // e.toProd.1 = d.toProd.2}),
      Disjoint (successorSector d) (star.radialGerm d.toProd.2 e)
  terminal_left_endpoint_sector_access :
    ∀ d : G.Dart,
      ∃ r K : ℝ, 0 < r ∧ 0 < K ∧
        PolygonalArcTerminalEndpointLeftCone (A.dartArc d) r K ⊆ successorSector d
  successor_initial_left_endpoint_sector_access :
    ∀ d : G.Dart,
      ∃ r K : ℝ, 0 < r ∧ 0 < K ∧
        PolygonalArcInitialEndpointLeftCone (A.dartArc (star.successor d)) r K ⊆
          successorSector d
  vertex_sector_coverage :
    ∀ (v : V) (y : EuclideanSpace ℝ (Fin 2)),
      (∃ d : G.Dart, d.toProd.2 = v) →
        y ∈ Metric.ball (D.vertexPlacement v) (star.localDiskRadius v) →
          y ≠ D.vertexPlacement v →
            y ∈ (OrdinaryDrawingImage G D)ᶜ →
              ∃ d : G.Dart, d.toProd.2 = v ∧ y ∈ successorSector d
