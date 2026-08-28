import Wikipedia.NoExoticSixSphere.QuaternionicHopfFactorParity
import Wikipedia.NoExoticSixSphere.ProductModTwoThirdHomology
import Wikipedia.NoExoticSixSphere.ArfPlaneRecognition
import Wikipedia.NoExoticSixSphere.GeometricArfInvariant
import Wikipedia.NoExoticSixSphere.CollapseInducedQuadraticForm
import Wikipedia.NoExoticSixSphere.QuaternionicHopfSmoothCollapseData

/-!
# The actual framed Hopf product has geometric Arf invariant one

The original mod-two middle homology is identified with two coefficient
coordinates by its actual projections. The actual factor sphere classes
map to the two coordinate vectors. Their proved geometric quadratic values
and proved polar nondegeneracy identify the original quadratic form with
the anisotropic plane. This computes the geometric invariant of the same
framed embedding whose collapse has the original sixth-stem class.

No bordism detection or nontriviality of that native class is inferred here.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

open EuclideanEmbedding
open Wikipedia.HopfProblem.SphereHomologyCoefficients

attribute [local instance] modHomologyModule

local instance : ChartedSpace (V 6) (Sphere 3 × Sphere 3) := southPairEuclideanAtlas
local instance : IsManifold (𝓡 6) ∞ (Sphere 3 × Sphere 3) := southPairEuclideanIsManifold

local instance arfSpherePiTwo (s : Sphere 3) :
    Subsingleton (HomotopyGroup (Fin 2) (Sphere 3) s) :=
  subsingleton_sphereHomotopyGroup (by decide) s

local instance arfProductSimplyConnected : SimplyConnectedSpace (Sphere 3 × Sphere 3) :=
  HigherHomotopy.simplyConnected_product

local instance arfProductPiTwo (p : Sphere 3 × Sphere 3) :
    Subsingleton (HomotopyGroup (Fin 2) (Sphere 3 × Sphere 3) p) :=
  HigherHomotopy.subsingleton_product p.1 p.2

def southPairMiddleCoordinates :
    ModHomology 2 (Sphere 3 × Sphere 3) 3 ≃ₗ[ZMod 2] ZMod 2 × ZMod 2 :=
  ProductThirdHomology.modSphereLinearEquivalence

theorem southPairMiddleCoordinates_left :
    southPairMiddleCoordinates (SixSphereMiddleParity.sphereClass southPairLeftSphere) =
      (1, 0) := by
  change ProductThirdHomology.modSphereLinearEquivalence
    (modHomologyMap 2 (ProductThirdHomology.leftSection (spherePole 3)) 3
      (unitSphereModTopClass 2 2)) = _
  rw [ProductThirdHomology.modSphereLinearEquivalence_left,
    unitSphereModHomologyTopEquiv_topClass]

theorem southPairMiddleCoordinates_right :
    southPairMiddleCoordinates (SixSphereMiddleParity.sphereClass southPairRightSphere) =
      (0, 1) := by
  change ProductThirdHomology.modSphereLinearEquivalence
    (modHomologyMap 2 (ProductThirdHomology.rightSection (spherePole 3)) 3
      (unitSphereModTopClass 2 2)) = _
  rw [ProductThirdHomology.modSphereLinearEquivalence_right,
    unitSphereModHomologyTopEquiv_topClass]

theorem southPairMiddleCoordinates_symm_left :
    southPairMiddleCoordinates.symm (1, 0) =
      SixSphereMiddleParity.sphereClass southPairLeftSphere := by
  apply southPairMiddleCoordinates.injective
  rw [LinearEquiv.apply_symm_apply, southPairMiddleCoordinates_left]

theorem southPairMiddleCoordinates_symm_right :
    southPairMiddleCoordinates.symm (0, 1) =
      SixSphereMiddleParity.sphereClass southPairRightSphere := by
  apply southPairMiddleCoordinates.injective
  rw [LinearEquiv.apply_symm_apply, southPairMiddleCoordinates_right]

variable (r : TubularRetraction southPairEuclideanEmbedding) (p : Sphere 3 × Sphere 3)

def southPairQuadraticIsometry :
    (southPairEuclideanEmbedding.modTwoHomologyQuadraticForm
      southPairEuclideanNormalFrame r p).IsometryEquiv Arf.anisotropicPlane :=
  Arf.anisotropicCoordinatesIsometry _
    (southPairEuclideanEmbedding.modTwoHomologyQuadraticForm_nondegenerate
      southPairEuclideanNormalFrame r p) southPairMiddleCoordinates
    (by
      rw [southPairMiddleCoordinates_symm_left]
      exact southPairLeftSphere_quadraticValue_one r p)
    (by
      rw [southPairMiddleCoordinates_symm_right]
      exact southPairRightSphere_quadraticValue_one r p)

theorem southPair_geometricArf_one :
    GeometricArf.invariant southPairEuclideanEmbedding southPairEuclideanNormalFrame r p = 1 := by
  let : Finite (ModHomology 2 (Sphere 3 × Sphere 3) 3) :=
    compactManifold_modTwoMiddleHomology_finiteType (V 6) (Sphere 3 × Sphere 3) p
  let : Fintype (ModHomology 2 (Sphere 3 × Sphere 3) 3) := Fintype.ofFinite _
  exact (Arf.invariant_isometry _ _
    (southPairEuclideanEmbedding.modTwoHomologyQuadraticForm_nondegenerate
      southPairEuclideanNormalFrame r p) (Arf.plane_nondegenerate 1 1)
    (southPairQuadraticIsometry r p)).trans Arf.invariant_anisotropicPlane

def southPairTubularRetraction : TubularRetraction southPairEuclideanEmbedding :=
  Classical.choice (southPairEuclideanEmbedding.nonempty_tubularRetraction
    southPairEuclideanNormalFrame)

theorem geometricArf_southPair :
    GeometricArf.invariant southPairEuclideanEmbedding southPairEuclideanNormalFrame
      southPairTubularRetraction (spherePole 3, spherePole 3) = 1 :=
  southPair_geometricArf_one southPairTubularRetraction (spherePole 3, spherePole 3)

theorem southPair_coordinateInducedNormalFrame :
    southPairSmoothCollapseData.coordinateInducedNormalFrame = southPairEuclideanNormalFrame :=
  southPairSmoothCollapseData.coordinateInducedNormalFrame_eq_of_radius_one rfl

theorem southPair_coordinateInduced_geometricArf_one :
    GeometricArf.invariant southPairEuclideanEmbedding
      southPairSmoothCollapseData.coordinateInducedNormalFrame r p = 1 := by
  rw [southPair_coordinateInducedNormalFrame]
  exact southPair_geometricArf_one r p

end NoExoticSixSphere.QuaternionicHopf
