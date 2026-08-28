import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfFiberHomology
import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfOriginalFactorParity
import Wikipedia.HopfProblem.DegreeCollapseGeometricArfDefined

/-!
# The actual Hopf-square quadratic form on its original factor classes

The product diffeomorphism supplies connectivity of the original regular
fiber. The already computed frame parities are then the values of the
original geometric quadratic form on the two actual factor sphere classes.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFiberQuadratic

open NoExoticSixSphere QuaternionicHopf QuaternionicHopfProductDiffeomorph
open QuaternionicHopfFramedFiber QuaternionicHopfFiberFactors QuaternionicHopfFiberHomology
open SphereHomologyCoefficients SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] modHomologyModule

local instance : ChartedSpace (V 6) Fiber := fiberAtlas
local instance : IsManifold (𝓡 6) ∞ Fiber := fiber_isManifold

theorem fiber_compact : CompactSpace Fiber :=
  isCompact_iff_compactSpace.mp (isClosed_eq smoothMap.continuous continuous_const).isCompact

local instance spherePiTwo (s : Sphere 3) : Subsingleton (π_ 2 (Sphere 3) s) :=
  subsingleton_sphereHomotopyGroup (by decide) s

local instance productSimplyConnected : SimplyConnectedSpace (Sphere 3 × Sphere 3) :=
  HigherHomotopy.simplyConnected_product

local instance productPiTwo (p : Sphere 3 × Sphere 3) :
    Subsingleton (π_ 2 (Sphere 3 × Sphere 3) p) :=
  HigherHomotopy.subsingleton_product p.1 p.2

theorem fiber_simplyConnected : SimplyConnectedSpace Fiber :=
  fiberDiffeomorph.symm.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace

attribute [local instance] fiber_compact fiber_simplyConnected

theorem fiber_piTwo (x : Fiber) : Subsingleton (π_ 2 Fiber x) := by
  let := TwoConnectedCoefficients.secondHomology_subsingleton
    (fiberDiffeomorph.symm x)
  let : Subsingleton (SingularHomology Fiber 2) :=
    (homeomorphHomologyEquiv fiberDiffeomorph.symm.toHomeomorph 2).injective.subsingleton
  exact (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv x).injective.subsingleton

attribute [local instance] fiber_piTwo

variable (a : Sphere 16) (r : EuclideanEmbedding.TubularRetraction embedding) (x : Fiber)

theorem left_geometricParity_one (q : Sphere 3) :
    embedding.geometricSphereParity (framing a) r (leftSphere q) = 1 := by
  rw [embedding.geometricSphereParity_eq_of_embedding (framing a) r (leftSphere q)
    (contMDiff_left q) (left_injective q) (left_mfderiv_injective q)]
  exact (leftParity_eq_sphereParity a q).symm.trans
    (QuaternionicHopfOriginalFactorParity.leftParity_one a q)

theorem right_geometricParity_one (q : Sphere 3) :
    embedding.geometricSphereParity (framing a) r (rightSphere q) = 1 := by
  rw [embedding.geometricSphereParity_eq_of_embedding (framing a) r (rightSphere q)
    (contMDiff_right q) (right_injective q) (right_mfderiv_injective q)]
  exact (rightParity_eq_sphereParity a q).symm.trans
    (QuaternionicHopfOriginalFactorParity.rightParity_one a q)

theorem left_quadraticValue_one (q : Sphere 3) :
    embedding.modTwoHomologyQuadraticForm (framing a) r x
      (SixSphereMiddleParity.sphereClass (leftSphere q)) = 1 := by
  rw [embedding.modTwoHomologyQuadraticForm_sphereClass]
  exact left_geometricParity_one a r q

theorem right_quadraticValue_one (q : Sphere 3) :
    embedding.modTwoHomologyQuadraticForm (framing a) r x
      (SixSphereMiddleParity.sphereClass (rightSphere q)) = 1 := by
  rw [embedding.modTwoHomologyQuadraticForm_sphereClass]
  exact right_geometricParity_one a r q

theorem coordinates_left_value :
    embedding.modTwoHomologyQuadraticForm (framing a) r x (coordinates.symm (1, 0)) = 1 := by
  rw [coordinates_symm_left]
  exact left_quadraticValue_one a r x (spherePole 3)

theorem coordinates_right_value :
    embedding.modTwoHomologyQuadraticForm (framing a) r x (coordinates.symm (0, 1)) = 1 := by
  rw [coordinates_symm_right]
  exact right_quadraticValue_one a r x (spherePole 3)

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFiberQuadratic
