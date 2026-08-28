import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfFiberQuadratic
import Wikipedia.NoExoticSixSphere.ArfPlaneRecognition

/-!
# Arf invariant one for the original Hopf-square regular fiber

Actual native homology coordinates, actual factor values and the proved
geometric nondegeneracy identify the original quadratic form with the
anisotropic plane. This computes the invariant of the original regular
fiber and its original defining-equation normal frame. It does not yet
assert stable framed detection or supply the original threefold filling.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFiberArf

open NoExoticSixSphere QuaternionicHopf QuaternionicHopfProductDiffeomorph
open QuaternionicHopfFramedFiber QuaternionicHopfFiberHomology QuaternionicHopfFiberQuadratic
open SphereHomologyCoefficients

attribute [local instance] modHomologyModule

local instance : ChartedSpace (V 6) Fiber := fiberAtlas
local instance : IsManifold (𝓡 6) ∞ Fiber := fiber_isManifold
attribute [local instance] fiber_compact fiber_simplyConnected fiber_piTwo

variable (a : Sphere 16) (r : EuclideanEmbedding.TubularRetraction embedding) (x : Fiber)

def quadraticIsometry :
    (embedding.modTwoHomologyQuadraticForm (framing a) r x).IsometryEquiv
      Arf.anisotropicPlane :=
  Arf.anisotropicCoordinatesIsometry _
    (SurgeryDetector.geometric_quadratic_nondegenerate embedding (framing a) r x)
    coordinates (coordinates_left_value a r x) (coordinates_right_value a r x)

theorem actualGeometricArf_one :
    SurgeryDetector.actualGeometricArf embedding (framing a) r x = 1 := by
  let : Finite (ModHomology 2 Fiber 3) :=
    compactManifold_modTwoMiddleHomology_finiteType (V 6) Fiber x
  let : Fintype (ModHomology 2 Fiber 3) := Fintype.ofFinite _
  exact (Arf.invariant_isometry _ _
    (SurgeryDetector.geometric_quadratic_nondegenerate embedding (framing a) r x)
    (Arf.plane_nondegenerate 1 1) (quadraticIsometry a r x)).trans
      Arf.invariant_anisotropicPlane

theorem actualGeometricArf_ne_zero :
    SurgeryDetector.actualGeometricArf embedding (framing a) r x ≠ 0 := by
  rw [actualGeometricArf_one]
  exact one_ne_zero

def tubularRetraction (a : Sphere 16) : EuclideanEmbedding.TubularRetraction embedding :=
  Classical.choice (embedding.nonempty_tubularRetraction (framing a))

def basepoint : Fiber := fiberDiffeomorph (spherePole 3, spherePole 3)

theorem originalFiberArf_one (a : Sphere 16) :
    SurgeryDetector.actualGeometricArf embedding (framing a) (tubularRetraction a) basepoint = 1 :=
  actualGeometricArf_one a (tubularRetraction a) basepoint

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFiberArf
