import Mathlib.Tactic
import Util.IncidenceGeometry.PolygonalArc

open Classical
noncomputable section

def ArcCrossingEarlierPrefix (δ : PolygonalArc) (j : ℕ)
    (hj : j + 1 < δ.vertices.length) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  ⋃ i : {i : ℕ // i < j},
    segment ℝ
      (δ.vertices[i.1]'(by omega))
      (δ.vertices[i.1 + 1]'(by omega))

