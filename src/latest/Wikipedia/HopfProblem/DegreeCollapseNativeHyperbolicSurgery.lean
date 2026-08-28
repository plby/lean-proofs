import Wikipedia.HopfProblem.DegreeCollapseHyperbolicQuotientSplit
import Wikipedia.HopfProblem.DegreeCollapseModTwoSurgeryIsometry

/-!
# The original geometric quadratic space is native new homology plus a hyperbolic plane

Reduce the supplied integer unit class through the actual coefficient map.
Its polar pairing with the actual attaching class is one. The attaching
quadratic value is zero, and correcting the unit class makes a hyperbolic
pair. Apply the explicit splitting to the already constructed native
mod-two surgery map. This gives an isometry from the original geometric
form to the actual new form times the standard hyperbolic plane.
No global nondegeneracy or existence of integer unit pairs is asserted.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryDetector

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct SmoothCube
open SingularMayerVietoris PeriodTorusHigherHomology SphereHomologyCoefficients

attribute [local instance] modHomologyModule

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [SimplyConnectedSpace M]
  [Subsingleton (SingularHomology M 2)]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (r : TubularRetraction e) (m : M) [Subsingleton (π_ 2 M m)]
  (f : C(Sphere 3, M)) (A : FramedAttachingProduct e a f) (hR : A.radius = 2)
  (d : SingularHomology M 3) (hd : detector f A hR d = 1)

include A hR d hd in
theorem attaching_modTwo_quadratic_zero :
    e.modTwoHomologyQuadraticForm a r m (modTwoAttachingClass f) = 0 := by
  change e.modTwoHomologyParity a r m
    (reductionHomologyMap 2 M 3 (integralSphereClass f)) = 0
  rw [modTwoHomologyParity_reduction, integralHomologyParity_sphereClass]
  exact attachingSphere_geometricParity_zero f A hR d hd r m

include A hR hd in
theorem unit_modTwo_cross : e.modTwoHomologyIntersection r m (modTwoAttachingClass f)
    (reductionHomologyMap 2 M 3 d) = 1 := by
  change orthogonalFunctional e r m f (reductionHomologyMap 2 M 3 d) = 1
  rw [orthogonalFunctional_reduction e a r m f A hR, hd, Int.cast_one]

def correctedUnitClass : ModHomology 2 M 3 :=
  HyperbolicReduction.correctedRight (e.modTwoHomologyQuadraticForm a r m)
    (modTwoAttachingClass f) (reductionHomologyMap 2 M 3 d)

include A hR hd in
theorem correctedUnitClass_cross :
    e.modTwoHomologyIntersection r m (modTwoAttachingClass f) (correctedUnitClass e a r m f d) = 1 :=
  HyperbolicReduction.correctedRight_cross _ _
    (e.modTwoHomologyQuadraticForm_polar a r m) _ _
    (attaching_modTwo_quadratic_zero e a r m f A hR d hd) (unit_modTwo_cross e a r m f A hR d hd)

include A hR hd in
theorem correctedUnitClass_quadratic_zero :
    e.modTwoHomologyQuadraticForm a r m (correctedUnitClass e a r m f d) = 0 :=
  HyperbolicReduction.correctedRight_zero _ _
    (e.modTwoHomologyQuadraticForm_polar a r m) _ _
    (attaching_modTwo_quadratic_zero e a r m f A hR d hd) (unit_modTwo_cross e a r m f A hR d hd)

def nativeHyperbolicSurgeryIsometry :
    letI := UnitSurgery.targetChartedSpace A hR;
    letI := UnitSurgery.target_isManifold A hR;
    letI := UnitSurgery.compactSpace_target A hR;
    letI : SimplyConnectedSpace (UnitSurgery.Target A hR) :=
      (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).1;
    ∀ (r' : TubularRetraction (UnitSurgery.inducedEmbedding A hR)) (m' : UnitSurgery.Target A hR),
      letI : Subsingleton (π_ 2 (UnitSurgery.Target A hR) m') :=
        (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).2.1 m';
      (e.modTwoHomologyQuadraticForm a r m).IsometryEquiv
        (((UnitSurgery.inducedEmbedding A hR).modTwoHomologyQuadraticForm
          (UnitSurgery.normalFraming A hR) r' m').prod Arf.hyperbolicPlane) := by
  let := UnitSurgery.targetChartedSpace A hR
  let := UnitSurgery.target_isManifold A hR
  let := UnitSurgery.compactSpace_target A hR
  let : SimplyConnectedSpace (UnitSurgery.Target A hR) :=
    (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).1
  intro r' m'
  let : Subsingleton (π_ 2 (UnitSurgery.Target A hR) m') :=
    (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).2.1 m'
  exact HyperbolicReduction.splitIsometry (e.modTwoHomologyQuadraticForm a r m)
    (e.modTwoHomologyIntersection r m) (e.modTwoHomologyQuadraticForm_polar a r m)
    (modTwoAttachingClass f) (correctedUnitClass e a r m f d)
    (attaching_modTwo_quadratic_zero e a r m f A hR d hd)
    (correctedUnitClass_quadratic_zero e a r m f A hR d hd)
    (correctedUnitClass_cross e a r m f A hR d hd)
    (modTwoSurgeryMap e a r m f A hR d hd) (modTwoSurgeryMap_kernel e a r m f A hR d hd)
    ((UnitSurgery.inducedEmbedding A hR).modTwoHomologyQuadraticForm
      (UnitSurgery.normalFraming A hR) r' m')
    (modTwoSurgeryMap_parity e a r m f A hR d hd r' m')
    (modTwoSurgeryMap_surjective e a r m f A hR d hd)

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryDetector
