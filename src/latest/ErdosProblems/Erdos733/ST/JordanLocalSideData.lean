import ErdosProblems.Erdos733.ST.SimpleClosedPolygonalCurve
import ErdosProblems.Erdos733.ST.PolygonalSideStrips
import ErdosProblems.Erdos733.ST.FinitePolygonalSet

open Classical
noncomputable section

-- [TABLET NODE: JordanLocalSideData]
structure JordanLocalSideData (J : SimpleClosedPolygonalCurve) where
-- BODY
  leftRegion : Set (EuclideanSpace ℝ (Fin 2))
  rightRegion : Set (EuclideanSpace ℝ (Fin 2))
  left_nonempty : leftRegion.Nonempty
  right_nonempty : rightRegion.Nonempty
  left_open : IsOpen leftRegion
  right_open : IsOpen rightRegion
  left_connected : IsConnected leftRegion
  right_connected : IsConnected rightRegion
  left_subset_complement : leftRegion ⊆ J.carrierᶜ
  right_subset_complement : rightRegion ⊆ J.carrierᶜ
  carrier_subset_left_closure : J.carrier ⊆ closure leftRegion
  carrier_subset_right_closure : J.carrier ⊆ closure rightRegion
  edge_strips :
    ∀ γ : {γ // γ ∈ J.edgeArcs},
      {S : PolygonalSideStrips γ.1 //
        S.leftStrip ⊆ leftRegion ∧ S.rightStrip ⊆ rightRegion}
  left_vertex_sector :
    ∀ γ : {γ // γ ∈ J.edgeArcs},
      ∃ U : Set (EuclideanSpace ℝ (Fin 2)),
        U.Nonempty ∧ IsOpen U ∧ IsConnected U ∧ U ⊆ J.carrierᶜ ∧
          U ⊆ leftRegion ∧
            (U ∩ (edge_strips γ).1.leftStrip).Nonempty ∧
              (U ∩ (edge_strips (J.successor γ)).1.leftStrip).Nonempty ∧
                γ.1.target ∈ closure U
  right_vertex_sector :
    ∀ γ : {γ // γ ∈ J.edgeArcs},
      ∃ U : Set (EuclideanSpace ℝ (Fin 2)),
        U.Nonempty ∧ IsOpen U ∧ IsConnected U ∧ U ⊆ J.carrierᶜ ∧
          U ⊆ rightRegion ∧
            (U ∩ (edge_strips γ).1.rightStrip).Nonempty ∧
              (U ∩ (edge_strips (J.successor γ)).1.rightStrip).Nonempty ∧
                γ.1.target ∈ closure U
  transverse_segment :
    ∃ γ : {γ // γ ∈ J.edgeArcs},
      ∃ K : FinitePolygonalSet,
        K.carrier = J.carrier ∧
          ∃ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
            s ∈ K.segments ∧
              ∃ a b x : EuclideanSpace ℝ (Fin 2),
                a ∈ leftRegion ∧ b ∈ rightRegion ∧ a ≠ b ∧
                  x ∈ γ.1.relativeInterior ∧
                    x ∈ openSegment ℝ a b ∧ x ∈ openSegment ℝ s.1 s.2 ∧
                      segment ℝ a b ∩ J.carrier = {x} ∧
                        (∀ p : EuclideanSpace ℝ (Fin 2),
                          p ∈ K.points → p ∉ segment ℝ a b) ∧
                          (∀ t : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
                            t ∈ K.segments →
                              ¬ ∃ p q : EuclideanSpace ℝ (Fin 2),
                                p ≠ q ∧
                                  segment ℝ p q ⊆
                                    segment ℝ a b ∩ segment ℝ t.1 t.2) ∧
                            (∀ t : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
                              t ∈ K.segments →
                                ∀ p : EuclideanSpace ℝ (Fin 2),
                                  p ∈ openSegment ℝ a b →
                                    p ∈ openSegment ℝ t.1 t.2 →
                                      ¬ ∃ c : ℝ, t.2 - t.1 = c • (b - a)) ∧
                          (∀ t : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
                            t ∈ K.segments →
                              Set.ncard (openSegment ℝ a b ∩ openSegment ℝ t.1 t.2) =
                                if t = s then 1 else 0)
  exterior_ray_access :
    ∃ w u : EuclideanSpace ℝ (Fin 2),
      u ≠ 0 ∧ (w ∈ leftRegion ∨ w ∈ rightRegion) ∧
        ∀ t : ℝ, 0 ≤ t → w + t • u ∈ J.carrierᶜ
