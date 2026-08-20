import ErdosProblems.Erdos733.ST.DrawingFaceComponent
import ErdosProblems.Erdos733.ST.OrdinaryDrawingImage
import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawing
import ErdosProblems.Erdos733.ST.PolygonalSideStrips
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open Classical
noncomputable section

-- [TABLET NODE: PlaneDrawingDartSectorData]
structure PlaneDrawingDartSectorData {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G) where
-- BODY
  dartEdge : G.Dart → G.edgeFinset
  dartEdge_eq : ∀ d : G.Dart, (dartEdge d).1 = d.edge
  dartArc : G.Dart → PolygonalArc
  dartArc_carrier :
    ∀ d : G.Dart, (dartArc d).carrier = (D.edgeArc (dartEdge d)).carrier
  dartArc_source :
    ∀ d : G.Dart, (dartArc d).source = D.vertexPlacement d.toProd.1
  dartArc_target :
    ∀ d : G.Dart, (dartArc d).target = D.vertexPlacement d.toProd.2
  leftSideStrip : G.Dart → Set (EuclideanSpace ℝ (Fin 2))
  rightSideStrip : G.Dart → Set (EuclideanSpace ℝ (Fin 2))
  sideStripData :
    ∀ d : G.Dart, ∃ S : PolygonalSideStrips (dartArc d),
      leftSideStrip d = S.leftStrip ∧ rightSideStrip d = S.rightStrip
  rightSideStrip_eq_leftSideStrip_symm :
    ∀ d : G.Dart, rightSideStrip d = leftSideStrip d.symm
  localComplement_subset_sideStrips :
    ∀ (d : G.Dart) (x : EuclideanSpace ℝ (Fin 2)),
      x ∈ (dartArc d).relativeInterior →
        ∃ U : Set (EuclideanSpace ℝ (Fin 2)),
          IsOpen U ∧ x ∈ U ∧
            U ∩ (OrdinaryDrawingImage G D)ᶜ ⊆
              leftSideStrip d ∪ leftSideStrip d.symm
  leftSide_unique_face_component :
    ∀ d : G.Dart, ∃! L : Set (EuclideanSpace ℝ (Fin 2)),
      DrawingFaceComponent G D L ∧ leftSideStrip d ⊆ L
  rightSide_unique_face_component :
    ∀ d : G.Dart, ∃! R : Set (EuclideanSpace ℝ (Fin 2)),
      DrawingFaceComponent G D R ∧ rightSideStrip d ⊆ R
  localDiskRadius : V → ℝ
  localDiskRadius_pos : ∀ v : V, 0 < localDiskRadius v
  germDirection :
    ∀ v : V, {d : G.Dart // d.toProd.1 = v} → EuclideanSpace ℝ (Fin 2)
  germDirection_ne_zero :
    ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}), germDirection v d ≠ 0
  radialGerm :
    ∀ v : V, {d : G.Dart // d.toProd.1 = v} →
      Set (EuclideanSpace ℝ (Fin 2))
  radialGerm_eq_openSegment :
    ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
      ∃ r : ℝ, 0 < r ∧ r ≤ localDiskRadius v ∧
        radialGerm v d =
          openSegment ℝ (D.vertexPlacement v)
            (D.vertexPlacement v + r • germDirection v d)
  radialGerm_subset_dartArc :
    ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
      radialGerm v d ⊆ (D.edgeArc (dartEdge d.1)).carrier
  localDisk_meets_drawing_only_incident_germs :
    ∀ v : V,
      Metric.ball (D.vertexPlacement v) (localDiskRadius v) ∩
          OrdinaryDrawingImage G D =
        {D.vertexPlacement v} ∪
          ⋃ d : {d : G.Dart // d.toProd.1 = v}, radialGerm v d
  clockwiseNext :
    ∀ v : V, Equiv.Perm {d : G.Dart // d.toProd.1 = v}
  fullClockwiseTurn : V → ℝ
  fullClockwiseTurn_pos : ∀ v : V, 0 < fullClockwiseTurn v
  clockwiseTurn :
    ∀ v : V, {d : G.Dart // d.toProd.1 = v} →
      {d : G.Dart // d.toProd.1 = v} → ℝ
  clockwiseTurn_pos :
    ∀ (v : V) (d e : {d : G.Dart // d.toProd.1 = v}), 0 < clockwiseTurn v d e
  clockwiseTurn_le_full :
    ∀ (v : V) (d e : {d : G.Dart // d.toProd.1 = v}),
      clockwiseTurn v d e ≤ fullClockwiseTurn v
  clockwiseTurn_full_iff_same :
    ∀ (v : V) (d e : {d : G.Dart // d.toProd.1 = v}),
      clockwiseTurn v d e = fullClockwiseTurn v ↔ e = d
  clockwiseNext_first_after :
    ∀ (v : V) (d e : {d : G.Dart // d.toProd.1 = v}),
      e ≠ d → clockwiseTurn v d (clockwiseNext v d) ≤ clockwiseTurn v d e
  clockwiseNext_eq_self_iff_isolated :
    ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
      clockwiseNext v d = d ↔ ∀ e : {d : G.Dart // d.toProd.1 = v}, e = d
  successor : Equiv.Perm G.Dart
  successor_tail : ∀ d : G.Dart, (successor d).toProd.1 = d.toProd.2
  successor_eq_clockwiseNext :
    ∀ d : G.Dart,
      successor d =
        (clockwiseNext d.toProd.2
          ⟨d.symm, by simp [SimpleGraph.Dart.symm]⟩).1
  successor_single_incident :
    ∀ d : G.Dart,
      (∀ e : {e : G.Dart // e.toProd.1 = d.toProd.2}, e.1 = d.symm) →
        successor d = d.symm
  successor_clockwise_sector :
    ∀ d : G.Dart,
      ∃ sector : Set (EuclideanSpace ℝ (Fin 2)),
        IsOpen sector ∧ IsConnected sector ∧
          sector ⊆ Metric.ball (D.vertexPlacement d.toProd.2)
            (localDiskRadius d.toProd.2) ∧
          sector ⊆ (OrdinaryDrawingImage G D)ᶜ ∧
          (sector ∩ leftSideStrip d ∩
            Metric.ball (D.vertexPlacement d.toProd.2)
              (localDiskRadius d.toProd.2)).Nonempty ∧
          (sector ∩ leftSideStrip (successor d) ∩
            Metric.ball (D.vertexPlacement d.toProd.2)
              (localDiskRadius d.toProd.2)).Nonempty ∧
          (∀ e : {e : G.Dart // e.toProd.1 = d.toProd.2},
            Disjoint sector (radialGerm d.toProd.2 e))
  vertex_sector_coverage :
    ∀ (v : V) (y : EuclideanSpace ℝ (Fin 2)),
      (∃ d : G.Dart, d.toProd.2 = v) →
        y ∈ Metric.ball (D.vertexPlacement v) (localDiskRadius v) →
          y ≠ D.vertexPlacement v →
            y ∈ (OrdinaryDrawingImage G D)ᶜ →
              ∃ d : G.Dart,
                d.toProd.2 = v ∧
                  ∃ sector : Set (EuclideanSpace ℝ (Fin 2)),
                    y ∈ sector ∧ IsOpen sector ∧ IsConnected sector ∧
                      sector ⊆ Metric.ball (D.vertexPlacement v)
                        (localDiskRadius v) ∧
                      sector ⊆ (OrdinaryDrawingImage G D)ᶜ ∧
                      (sector ∩ leftSideStrip d ∩
                        Metric.ball (D.vertexPlacement v)
                          (localDiskRadius v)).Nonempty ∧
                      (sector ∩ leftSideStrip (successor d) ∩
                        Metric.ball (D.vertexPlacement v)
                          (localDiskRadius v)).Nonempty ∧
                      (∀ e : {e : G.Dart // e.toProd.1 = v},
                        Disjoint sector (radialGerm v e))
