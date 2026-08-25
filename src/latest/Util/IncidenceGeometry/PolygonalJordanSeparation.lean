import Util.IncidenceGeometry.SimpleClosedPolygonalCurve
import Util.IncidenceGeometry.PolygonallyPathConnected
import Util.IncidenceGeometry.ComplementComponent
import Util.IncidenceGeometry.CurveLocalSideSeparation
import Util.IncidenceGeometry.JordanLocalSideData
import Util.IncidenceGeometry.JordanLocalSideConstruction
import Util.IncidenceGeometry.JordanRayComponentClassification
import Util.IncidenceGeometry.JordanComponentFrontiers
import Util.IncidenceGeometry.SimpleClosedPolygonalCurveComplementOpen
import Util.IncidenceGeometry.OpenConnectedComponentPolygonallyConnected

open Classical
noncomputable section

lemma PolygonalJordanSeparation (J : SimpleClosedPolygonalCurve) :
    ∃ inside outside : Set (EuclideanSpace ℝ (Fin 2)),
      inside ≠ outside ∧
        ComplementComponent J.carrier inside ∧
          ComplementComponent J.carrier outside ∧
            (∀ F : Set (EuclideanSpace ℝ (Fin 2)),
              ComplementComponent J.carrier F → F = inside ∨ F = outside) ∧
              (∀ p : EuclideanSpace ℝ (Fin 2),
                p ∈ J.carrierᶜ → p ∈ inside ∨ p ∈ outside) ∧
                Bornology.IsBounded inside ∧
                  ¬ Bornology.IsBounded outside ∧
                    PolygonallyPathConnected inside ∧
                      PolygonallyPathConnected outside ∧
                        frontier inside = J.carrier ∧
                          frontier outside = J.carrier ∧
                            CurveLocalSideSeparation J inside outside := by
  obtain ⟨S⟩ := JordanLocalSideConstruction J
  obtain ⟨inside, outside, hinside, houtside, hne, horient,
    hcomponents, hcover, hbounded, hunbounded⟩ :=
    JordanRayComponentClassification J S
  have hinside_path : PolygonallyPathConnected inside :=
    OpenConnectedComponentPolygonallyConnected J.carrierᶜ inside
      (SimpleClosedPolygonalCurveComplementOpen J) (by simpa using hinside)
  have houtside_path : PolygonallyPathConnected outside :=
    OpenConnectedComponentPolygonallyConnected J.carrierᶜ outside
      (SimpleClosedPolygonalCurveComplementOpen J) (by simpa using houtside)
  have hfrontiers :
      frontier inside = J.carrier ∧ frontier outside = J.carrier :=
    JordanComponentFrontiers J S inside outside hinside houtside hne horient hcover
  have hlocal : CurveLocalSideSeparation J inside outside := by
    intro gamma
    refine ⟨(S.edge_strips gamma).1, ?_⟩
    rcases horient with hleft_right | hright_left
    · exact Or.inl
        ⟨(S.edge_strips gamma).2.1.trans hleft_right.1,
          (S.edge_strips gamma).2.2.trans hleft_right.2⟩
    · exact Or.inr
        ⟨(S.edge_strips gamma).2.1.trans hright_left.1,
          (S.edge_strips gamma).2.2.trans hright_left.2⟩
  exact ⟨inside, outside, hne, hinside, houtside, hcomponents, hcover,
    hbounded, hunbounded, hinside_path, houtside_path,
    hfrontiers.1, hfrontiers.2, hlocal⟩
