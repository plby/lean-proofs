import ErdosProblems.Erdos733.ST.DrawingFaceComponent
import ErdosProblems.Erdos733.ST.OrdinaryDrawingImage
import ErdosProblems.Erdos733.ST.PlaneDrawingDartArcData
import ErdosProblems.Erdos733.ST.PlaneDrawingDartVertexStarData
import ErdosProblems.Erdos733.ST.PolygonalSideStrips
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open Classical
noncomputable section

-- [TABLET NODE: PlaneDrawingDartSideStripData]
structure PlaneDrawingDartSideStripData {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (A : PlaneDrawingDartArcData G D)
    (B : PlaneDrawingDartVertexStarData G D A) where
-- BODY
  leftSideStrip : G.Dart → Set (EuclideanSpace ℝ (Fin 2))
  rightSideStrip : G.Dart → Set (EuclideanSpace ℝ (Fin 2))
  sideStripData :
    ∀ d : G.Dart, ∃ S : PolygonalSideStrips (A.dartArc d),
      leftSideStrip d = S.leftStrip ∧ rightSideStrip d = S.rightStrip
  rightSideStrip_eq_leftSideStrip_symm :
    ∀ d : G.Dart, rightSideStrip d = leftSideStrip d.symm
  leftSideStrip_subset_complement :
    ∀ d : G.Dart, leftSideStrip d ⊆ (OrdinaryDrawingImage G D)ᶜ
  rightSideStrip_subset_complement :
    ∀ d : G.Dart, rightSideStrip d ⊆ (OrdinaryDrawingImage G D)ᶜ
  localComplement_subset_sideStrips :
    ∀ (d : G.Dart) (x : EuclideanSpace ℝ (Fin 2)),
      x ∈ (A.dartArc d).relativeInterior →
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
