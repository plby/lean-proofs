import Wikipedia.HopfProblem.DegreeCollapseRadialHopfIdentification

/-!
# Original finite-suspension nullity of the orthogonal Hopf construction

Transport the actual Hopf map to literal standard spheres by supplied
linear isometries. Coordinate naturality and the proved finite-join
comparison identify its twelve original suspension iterates with the
already contracted radial map. No extra nullity premise is imposed on
the S4-to-O(4) family.
-/

noncomputable section

open scoped Topology
open NoExoticSixSphere GLOrthonormalization

namespace Wikipedia.HopfProblem.DegreeCollapse.RadialHopfStableVanishing

open HopfBlockCoordinates RadialJoinNaturality RadialHopfIdentification

variable (e : WithLp 2 (Vector 5 × Vector 4) ≃ₗᵢ[ℝ] Vector 9)
  (d : WithLp 2 (ℝ × Vector 4) ≃ₗᵢ[ℝ] Vector 5)

def standardMap (f : C(Sphere 4, OrthogonalOperators 4)) : C(Sphere 8, Sphere 4) :=
  (unitSphereCoordinates d : C(_, _)).comp
    ((OrthogonalHopfMap.sphereMap f).comp ((unitSphereCoordinates e).symm : C(_, _)))

theorem standardMap_square (f : C(Sphere 4, OrthogonalOperators 4))
    (x : UnitSphere (WithLp 2 (Vector 5 × Vector 4))) :
    standardMap e d f (unitSphereCoordinates e x) =
      unitSphereCoordinates d (OrthogonalHopfMap.sphereMap f x) := by
  change unitSphereCoordinates d (OrthogonalHopfMap.sphereMap f
    ((unitSphereCoordinates e).symm (unitSphereCoordinates e x))) = _
  rw [Homeomorph.symm_apply_apply]

theorem standard_join_twelve_nullhomotopic (f : C(Sphere 4, OrthogonalOperators 4)) :
    (RadialSphereJoin.sphereMap (G := Vector 12) (standardMap e d f)).Nullhomotopic := by
  let a := LinearIsometryEquiv.refl ℝ (Vector 12)
  apply (nullhomotopic_iff_of_homeomorph_square
    (unitSphereCoordinates (LinearIsometryEquiv.withLpProdCongr 2 e a))
    (unitSphereCoordinates (LinearIsometryEquiv.withLpProdCongr 2 d a))
    (RadialSphereJoin.sphereMap (OrthogonalHopfMap.sphereMap f))
    (RadialSphereJoin.sphereMap (standardMap e d f))
    (fun x ↦ (sphereMap_naturality e d a (OrthogonalHopfMap.sphereMap f)
      (standardMap e d f) (standardMap_square e d f) x).symm)).mp
  exact hopf_join_twelve_nullhomotopic f

theorem standard_hopf_twelve_suspensions_nullhomotopic
    (f : C(Sphere 4, OrthogonalOperators 4)) :
    (SphereMapSuspension.iterate (standardMap e d f) 12).Nullhomotopic :=
  (RadialJoinIteration.nullhomotopic_iff_iterate (standardMap e d f) 12).mp
    (standard_join_twelve_nullhomotopic e d f)

end Wikipedia.HopfProblem.DegreeCollapse.RadialHopfStableVanishing
