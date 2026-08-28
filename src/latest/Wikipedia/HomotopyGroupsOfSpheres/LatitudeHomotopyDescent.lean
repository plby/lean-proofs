import Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent
import Mathlib.Topology.Homotopy.Basic

/-! # Jointly continuous latitude descent of homotopies with fixed outside faces -/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent.DoubleFamily

open Wikipedia.HopfProblem.SphereHomology

variable {X : Type*} [TopologicalSpace X] {n : ℕ} {x : X}
variable (F G : DoubleFamily n X x) (H : F.map.Homotopy G.map)
variable (houter0 : ∀ r t z, H (r, (0, (t, z))) = x)
variable (houter1 : ∀ r t z, H (r, (1, (t, z))) = x)
variable (hinner0 : ∀ r s z, H (r, (s, (0, z))) = x)
variable (hinner1 : ∀ r s z, H (r, (s, (1, z))) = x)

def pathValuedFamily : DoubleFamily n C(I, X) (ContinuousMap.const I x) where
  map := (H.toContinuousMap.comp
    ⟨fun p : (I × (I × UnitSphere n)) × I ↦ (p.2, p.1),
      continuous_snd.prodMk continuous_fst⟩).curry
  outer_zero t z := ContinuousMap.ext (fun r ↦ houter0 r t z)
  outer_one t z := ContinuousMap.ext (fun r ↦ houter1 r t z)
  inner_zero s z := ContinuousMap.ext (fun r ↦ hinner0 r s z)
  inner_one s z := ContinuousMap.ext (fun r ↦ hinner1 r s z)

def homotopyDescent : F.toSphereMap.Homotopy G.toSphereMap where
  toContinuousMap :=
    (pathValuedFamily F G H houter0 houter1 hinner0 hinner1).toSphereMap.uncurry.comp
      ⟨fun p : I × UnitSphere (n + 2) ↦ (p.2, p.1), continuous_snd.prodMk continuous_fst⟩
  map_zero_left w := by
    obtain ⟨⟨s, v⟩, rfl⟩ := Latitude.point_surjective (n + 1) w
    obtain ⟨⟨t, z⟩, rfl⟩ := Latitude.point_surjective n v
    change (pathValuedFamily F G H houter0 houter1 hinner0 hinner1).toSphereMap
      (Latitude.point (n + 1) s (Latitude.point n t z)) 0 = _
    rw [toSphereMap_point, F.toSphereMap_point]
    exact H.apply_zero (s, (t, z))
  map_one_left w := by
    obtain ⟨⟨s, v⟩, rfl⟩ := Latitude.point_surjective (n + 1) w
    obtain ⟨⟨t, z⟩, rfl⟩ := Latitude.point_surjective n v
    change (pathValuedFamily F G H houter0 houter1 hinner0 hinner1).toSphereMap
      (Latitude.point (n + 1) s (Latitude.point n t z)) 1 = _
    rw [toSphereMap_point, G.toSphereMap_point]
    exact H.apply_one (s, (t, z))

theorem homotopyDescent_point (r s t : I) (z : UnitSphere n) :
    homotopyDescent F G H houter0 houter1 hinner0 hinner1
      (r, Latitude.point (n + 1) s (Latitude.point n t z)) = H (r, (s, (t, z))) := by
  change (pathValuedFamily F G H houter0 houter1 hinner0 hinner1).toSphereMap
    (Latitude.point (n + 1) s (Latitude.point n t z)) r = _
  rw [toSphereMap_point]
  rfl

theorem homotopyDescent_outer_zero (r : I) (w : UnitSphere (n + 1)) :
    homotopyDescent F G H houter0 houter1 hinner0 hinner1
      (r, Latitude.point (n + 1) 0 w) = x := by
  obtain ⟨⟨t, z⟩, rfl⟩ := Latitude.point_surjective n w
  rw [homotopyDescent_point]
  exact houter0 r t z

end Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent.DoubleFamily
