import Util.IncidenceGeometry.PlaneDrawingDartArcData
import Util.IncidenceGeometry.OrdinaryDrawingImage
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open Classical
noncomputable section

structure PlaneDrawingDartVertexStarData {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (A : PlaneDrawingDartArcData G D) where
  localDiskRadius : V → ℝ
  localDiskRadius_pos : ∀ v : V, 0 < localDiskRadius v
  germDirection :
    ∀ v : V, {d : G.Dart // d.toProd.1 = v} → EuclideanSpace ℝ (Fin 2)
  germDirection_ne_zero :
    ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}), germDirection v d ≠ 0
  germDirection_eq_normalized_firstSegment :
    ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
      germDirection v d =
        (‖(A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le
              (A.dartArc d.1).length_ge_two) - D.vertexPlacement v‖)⁻¹ •
          ((A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le
              (A.dartArc d.1).length_ge_two) - D.vertexPlacement v)
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
      radialGerm v d ⊆ (D.edgeArc (A.dartEdge d.1)).carrier
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
