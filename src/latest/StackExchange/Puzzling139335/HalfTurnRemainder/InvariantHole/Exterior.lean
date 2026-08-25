import StackExchange.Puzzling139335.JordanRegion

/-!
# A complementary component containing a surrounding Jordan curve is unbounded

If a set lies strictly inside a Jordan curve, the closure of the exterior
misses that set. This connected exterior closure meets the curve, so any
complementary component containing the curve must contain the entire exterior.
No closedness, compactness, or connectedness hypothesis on the excluded set
is needed for this step.
-/

open Set

namespace Puzzling139335.HalfTurnRemainder

/-- A component containing a Jordan curve also contains its exterior closure
when the excluded set lies in the bounded Jordan region. -/
theorem closure_outside_subset_connectedComponentIn_compl
    {K C : Set Plane} {x : Plane} (hC : Schoenflies.IsJordanCurve C)
    (hK : K ⊆ Schoenflies.inside C) (hCx : C ⊆ connectedComponentIn Kᶜ x) :
    closure (Schoenflies.outside C) ⊆ connectedComponentIn Kᶜ x := by
  have hsep := Schoenflies.jordan_curve_theorem hC
  have hdis : Disjoint (closure (Schoenflies.outside C)) (Schoenflies.inside C) :=
    Schoenflies.disjoint_inside_outside.symm.closure_left hsep.isOpen_inside
  have hsub : closure (Schoenflies.outside C) ⊆ Kᶜ := by
    intro y hy hKy
    exact disjoint_left.mp hdis hy (hK hKy)
  obtain ⟨z, hz⟩ := hC.nonempty
  have hzcl : z ∈ closure (Schoenflies.outside C) :=
    (Schoenflies.IsRegionOf.outside C).subset_closure hsep hz
  calc
    closure (Schoenflies.outside C) ⊆ connectedComponentIn Kᶜ z :=
      hsep.isConnected_outside.isPreconnected.closure.subset_connectedComponentIn hzcl hsub
    _ = connectedComponentIn Kᶜ x := (connectedComponentIn_eq (hCx hz)).symm

/-- A complementary component containing a Jordan curve surrounding the
excluded set cannot be bounded. -/
theorem not_isBounded_connectedComponentIn_compl_of_subset_inside
    {K C : Set Plane} {x : Plane} (hC : Schoenflies.IsJordanCurve C)
    (hK : K ⊆ Schoenflies.inside C) (hCx : C ⊆ connectedComponentIn Kᶜ x) :
    ¬ Bornology.IsBounded (connectedComponentIn Kᶜ x) := by
  intro hb
  have hout : Schoenflies.outside C ⊆ connectedComponentIn Kᶜ x :=
    subset_closure.trans (closure_outside_subset_connectedComponentIn_compl hC hK hCx)
  exact (Schoenflies.jordan_curve_theorem hC).not_isBounded_outside (hb.subset hout)

end Puzzling139335.HalfTurnRemainder
