import Wikipedia.HopfProblem.DegreeCollapseMiddleModTwoNondegenerate
import Wikipedia.HopfProblem.DegreeCollapseNativeArfSurgery

/-!
# The actual geometric Arf invariant needs no nondegeneracy hypothesis

Native Morse geometry now proves nondegeneracy of the genuine geometric
intersection pairing. The original quadratic form has exactly that polar
form, so its Arf invariant is defined without an additional assumption.
The existing actual unit-surgery theorem then preserves this invariant.
The integer unit detector class remains an explicit surgery hypothesis.
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
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (r : TubularRetraction e) (m : M) [Subsingleton (π_ 2 M m)]

theorem geometric_quadratic_nondegenerate :
    (e.modTwoHomologyQuadraticForm a r m).polarBilin.Nondegenerate := by
  rw [e.modTwoHomologyQuadraticForm_polar a r m]
  exact MorseCancellation.MiddleDuality.modTwoIntersection_nondegenerate e r m

def actualGeometricArf : ZMod 2 :=
  geometricArf e a r m (geometric_quadratic_nondegenerate e a r m)

theorem actualGeometricArf_eq_gaussSign :
    actualGeometricArf e a r m = Arf.signParity (geometricGaussSum e a r m) := rfl

variable [Subsingleton (SingularHomology M 2)]
  (f : C(Sphere 3, M)) (A : FramedAttachingProduct e a f) (hR : A.radius = 2)
  (d : SingularHomology M 3) (hd : detector f A hR d = 1)

theorem actualGeometricArf_preserved_by_unit_surgery :
    letI := UnitSurgery.targetChartedSpace A hR;
    letI := UnitSurgery.target_isManifold A hR;
    letI := UnitSurgery.compactSpace_target A hR;
    letI : SimplyConnectedSpace (UnitSurgery.Target A hR) :=
      (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).1;
    ∀ (r' : TubularRetraction (UnitSurgery.inducedEmbedding A hR)) (m' : UnitSurgery.Target A hR),
      letI : Subsingleton (π_ 2 (UnitSurgery.Target A hR) m') :=
        (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).2.1 m';
      actualGeometricArf e a r m = actualGeometricArf (UnitSurgery.inducedEmbedding A hR)
        (UnitSurgery.normalFraming A hR) r' m' := by
  let := UnitSurgery.targetChartedSpace A hR
  let := UnitSurgery.target_isManifold A hR
  let := UnitSurgery.compactSpace_target A hR
  let : SimplyConnectedSpace (UnitSurgery.Target A hR) :=
    (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).1
  intro r' m'
  let : Subsingleton (π_ 2 (UnitSurgery.Target A hR) m') :=
    (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).2.1 m'
  obtain ⟨-, -, hArf⟩ := native_quadratic_surgery_invariants e a r m f A hR d hd r' m'
  obtain ⟨hq', he⟩ := hArf (geometric_quadratic_nondegenerate e a r m)
  exact he

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryDetector
