import Util.IncidenceGeometry.SimpleClosedPolygonalCurve
import Util.IncidenceGeometry.PolygonalSideStrips

open Classical
noncomputable section

def CurveLocalSideSeparation (J : SimpleClosedPolygonalCurve)
    (inside outside : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ γ : {γ // γ ∈ J.edgeArcs},
    ∃ S : PolygonalSideStrips γ.1,
      (S.leftStrip ⊆ inside ∧ S.rightStrip ⊆ outside) ∨
        (S.leftStrip ⊆ outside ∧ S.rightStrip ⊆ inside)
