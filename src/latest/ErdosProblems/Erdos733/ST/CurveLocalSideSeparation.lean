import ErdosProblems.Erdos733.ST.SimpleClosedPolygonalCurve
import ErdosProblems.Erdos733.ST.PolygonalSideStrips

open Classical
noncomputable section

-- [TABLET NODE: CurveLocalSideSeparation]
def CurveLocalSideSeparation (J : SimpleClosedPolygonalCurve)
    (inside outside : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
-- BODY
  ∀ γ : {γ // γ ∈ J.edgeArcs},
    ∃ S : PolygonalSideStrips γ.1,
      (S.leftStrip ⊆ inside ∧ S.rightStrip ⊆ outside) ∨
        (S.leftStrip ⊆ outside ∧ S.rightStrip ⊆ inside)
