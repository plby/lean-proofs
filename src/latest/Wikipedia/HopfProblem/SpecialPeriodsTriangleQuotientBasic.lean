import Wikipedia.HopfProblem.SpecialPeriodsTriangleRegular
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientTopology

/-!
# The full actual triangle orbit space

This is the quotient of the original upper half-plane by the constructed
faithful triangle action, including the two elliptic orbits.  Its topology
is the quotient topology.  Proper discontinuity proves it Hausdorff, and
the original action makes the projection an open quotient map.

The complex atlas and the cusp compactification are separate constructions;
neither is presumed in these definitions.
-/

noncomputable section

open Set Topology UpperHalfPlane

namespace Wikipedia.HopfProblem.SpecialPeriods

attribute [local instance] triangleGeometricAction
  triangleGeometricAction_properlyDiscontinuous triangleGeometricAction_continuous

/-- The full orbit space, with its actual quotient topology. -/
abbrev TriangleOrbitSpace := Quotient (MulAction.orbitRel TriangleGroup ℍ)

/-- Projection from the actual upper half-plane to its triangle orbits. -/
def triangleOrbitProjection : ℍ → TriangleOrbitSpace := Quotient.mk _

theorem triangleOrbitProjection_surjective : Function.Surjective triangleOrbitProjection :=
  Quotient.mk_surjective

theorem triangleOrbitProjection_continuous : Continuous triangleOrbitProjection :=
  continuous_quot_mk

theorem triangleOrbitProjection_eq_iff_mem_orbit (x y : ℍ) :
    triangleOrbitProjection x = triangleOrbitProjection y ↔ x ∈ MulAction.orbit TriangleGroup y :=
  Quotient.eq''

theorem triangleOrbitProjection_eq_iff (x y : ℍ) :
    triangleOrbitProjection x = triangleOrbitProjection y ↔
      ∃ g : TriangleGroup, triangleGeometricRepresentation g y = x :=
  Quotient.eq''

@[simp] theorem triangleOrbitProjection_smul (g : TriangleGroup) (z : ℍ) :
    triangleOrbitProjection (triangleGeometricRepresentation g z) = triangleOrbitProjection z :=
  (triangleOrbitProjection_eq_iff _ _).mpr ⟨g, rfl⟩

theorem triangleOrbitProjection_isOpenQuotientMap : IsOpenQuotientMap triangleOrbitProjection :=
  MulAction.isOpenQuotientMap_quotientMk

theorem triangleOrbitProjection_isOpenMap : IsOpenMap triangleOrbitProjection :=
  triangleOrbitProjection_isOpenQuotientMap.isOpenMap

instance triangleOrbitSpace_t2 : T2Space TriangleOrbitSpace := inferInstance

instance triangleOrbitSpace_secondCountable : SecondCountableTopology TriangleOrbitSpace :=
  ContinuousConstSMul.secondCountableTopology

instance triangleOrbitSpace_locallyCompact : LocallyCompactSpace TriangleOrbitSpace :=
  triangleOrbitProjection_isOpenQuotientMap.locallyCompactSpace

instance triangleOrbitSpace_pathConnected : PathConnectedSpace TriangleOrbitSpace :=
  triangleOrbitProjection_surjective.pathConnectedSpace triangleOrbitProjection_continuous

/-- The distinguished order-three orbit. -/
def triangleOrbitCenterOne : TriangleOrbitSpace := triangleOrbitProjection Triangle.centerOne

/-- The distinguished order-four orbit. -/
def triangleOrbitCenterTwo : TriangleOrbitSpace := triangleOrbitProjection Triangle.centerTwo

end Wikipedia.HopfProblem.SpecialPeriods
