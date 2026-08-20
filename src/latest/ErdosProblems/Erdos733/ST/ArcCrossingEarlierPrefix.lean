import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: ArcCrossingEarlierPrefix]
def ArcCrossingEarlierPrefix (δ : PolygonalArc) (j : ℕ)
    (hj : j + 1 < δ.vertices.length) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
-- BODY
  ⋃ i : {i : ℕ // i < j},
    segment ℝ
      (δ.vertices[i.1]'(by omega))
      (δ.vertices[i.1 + 1]'(by omega))

