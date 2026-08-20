import ErdosProblems.Erdos733.ST.OrdinaryDrawingImage
import ErdosProblems.Erdos733.ST.PlaneDrawingDartArcData
import ErdosProblems.Erdos733.ST.PlaneDrawingDartSideStripData
import ErdosProblems.Erdos733.ST.PlaneDrawingDartVertexStarData
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open Classical
noncomputable section

-- [TABLET NODE: PlaneDrawingDartSectorWitnessData]
structure PlaneDrawingDartSectorWitnessData {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (A : PlaneDrawingDartArcData G D)
    (B : PlaneDrawingDartVertexStarData G D A)
    (S : PlaneDrawingDartSideStripData G D A B) where
-- BODY
  successor_clockwise_sector :
    ∀ d : G.Dart,
      ∃ sector : Set (EuclideanSpace ℝ (Fin 2)),
        IsOpen sector ∧ IsConnected sector ∧
          sector ⊆ Metric.ball (D.vertexPlacement d.toProd.2)
            (B.localDiskRadius d.toProd.2) ∧
          sector ⊆ (OrdinaryDrawingImage G D)ᶜ ∧
          (sector ∩ S.leftSideStrip d ∩
            Metric.ball (D.vertexPlacement d.toProd.2)
              (B.localDiskRadius d.toProd.2)).Nonempty ∧
          (sector ∩ S.leftSideStrip (B.successor d) ∩
            Metric.ball (D.vertexPlacement d.toProd.2)
              (B.localDiskRadius d.toProd.2)).Nonempty ∧
          (∀ e : {e : G.Dart // e.toProd.1 = d.toProd.2},
            Disjoint sector (B.radialGerm d.toProd.2 e))
  vertex_sector_coverage :
    ∀ (v : V) (y : EuclideanSpace ℝ (Fin 2)),
      (∃ d : G.Dart, d.toProd.2 = v) →
        y ∈ Metric.ball (D.vertexPlacement v) (B.localDiskRadius v) →
          y ≠ D.vertexPlacement v →
            y ∈ (OrdinaryDrawingImage G D)ᶜ →
              ∃ d : G.Dart,
                d.toProd.2 = v ∧
                  ∃ sector : Set (EuclideanSpace ℝ (Fin 2)),
                    y ∈ sector ∧ IsOpen sector ∧ IsConnected sector ∧
                      sector ⊆ Metric.ball (D.vertexPlacement v)
                        (B.localDiskRadius v) ∧
                      sector ⊆ (OrdinaryDrawingImage G D)ᶜ ∧
                      (sector ∩ S.leftSideStrip d ∩
                        Metric.ball (D.vertexPlacement v)
                          (B.localDiskRadius v)).Nonempty ∧
                      (sector ∩ S.leftSideStrip (B.successor d) ∩
                        Metric.ball (D.vertexPlacement v)
                          (B.localDiskRadius v)).Nonempty ∧
                      (∀ e : {e : G.Dart // e.toProd.1 = v},
                        Disjoint sector (B.radialGerm v e))
