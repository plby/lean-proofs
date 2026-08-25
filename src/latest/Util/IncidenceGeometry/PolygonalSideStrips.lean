import Util.IncidenceGeometry.PolygonalArc

structure PolygonalSideStrips (γ : PolygonalArc) where
  collar : Set (EuclideanSpace ℝ (Fin 2))
  leftStrip : Set (EuclideanSpace ℝ (Fin 2))
  rightStrip : Set (EuclideanSpace ℝ (Fin 2))
  collar_open : IsOpen collar
  left_open : IsOpen leftStrip
  right_open : IsOpen rightStrip
  relativeInterior_subset_collar : γ.relativeInterior ⊆ collar
  left_subset_collar : leftStrip ⊆ collar
  right_subset_collar : rightStrip ⊆ collar
  left_connected : IsConnected leftStrip
  right_connected : IsConnected rightStrip
  left_disjoint_arc : Disjoint leftStrip γ.carrier
  right_disjoint_arc : Disjoint rightStrip γ.carrier
  side_strips_disjoint : Disjoint leftStrip rightStrip
  relativeInterior_subset_closure_left :
    γ.relativeInterior ⊆ closure leftStrip
  relativeInterior_subset_closure_right :
    γ.relativeInterior ⊆ closure rightStrip
  collar_without_arc :
    collar \ γ.relativeInterior = leftStrip ∪ rightStrip
