import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawing
import ErdosProblems.Erdos733.ST.PolygonalArcReverse
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open Classical
noncomputable section

-- [TABLET NODE: PlaneDrawingDartArcData]
structure PlaneDrawingDartArcData {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G) where
-- BODY
  dartEdge : G.Dart → G.edgeFinset
  dartEdge_eq : ∀ d : G.Dart, (dartEdge d).1 = d.edge
  dartArc : G.Dart → PolygonalArc
  dartArc_orientation :
    ∀ d : G.Dart,
      (dartArc d = D.edgeArc (dartEdge d) ∧
        (D.edgeArc (dartEdge d)).source = D.vertexPlacement d.toProd.1) ∨
      (dartArc d = PolygonalArcReverse (D.edgeArc (dartEdge d)) ∧
        (D.edgeArc (dartEdge d)).target = D.vertexPlacement d.toProd.1)
  dartArc_carrier :
    ∀ d : G.Dart, (dartArc d).carrier = (D.edgeArc (dartEdge d)).carrier
  dartArc_source :
    ∀ d : G.Dart, (dartArc d).source = D.vertexPlacement d.toProd.1
  dartArc_target :
    ∀ d : G.Dart, (dartArc d).target = D.vertexPlacement d.toProd.2
  dartArc_symm_eq_reverse :
    ∀ d : G.Dart, dartArc d.symm = PolygonalArcReverse (dartArc d)
