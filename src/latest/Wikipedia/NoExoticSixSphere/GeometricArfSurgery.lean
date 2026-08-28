import Wikipedia.NoExoticSixSphere.GeometricArfInvariant
import Wikipedia.HopfProblem.DegreeCollapseNativeArfSurgery

/-!
# Preservation of the constructed geometric Arf invariant by actual unit surgery

The cap comparison supplies polar nondegeneracy for the original quadratic
form. Its Arf invariant is the same one used by the native hyperbolic surgery
isometry. That isometry therefore preserves the constructed invariant on
the actual surgery target with its independently constructed smooth atlas.
Second integral homology vanishing follows from two-connectedness.

The attaching product and an integral unit detector are still explicit
surgery data. This is not framed-bordism detection or a filling theorem.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.GeometricArf

open GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct
open DegreeCollapse DegreeCollapse.SurgeryDetector

attribute [local instance] modHomologyModule

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [SimplyConnectedSpace M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (r : TubularRetraction e) (m : M) [Subsingleton (π_ 2 M m)]

/-- Both constructions use the same original quadratic form and actual finite middle group. -/
theorem invariant_eq_geometricArf
    (hq : (e.modTwoHomologyQuadraticForm a r m).polarBilin.Nondegenerate) :
    invariant e a r m = SurgeryDetector.geometricArf e a r m hq := rfl

/-- The actual surgery isometry preserves the invariant without assuming polar nondegeneracy. -/
theorem invariant_preserved_by_unit_surgery
    (f : C(Sphere 3, M)) (A : FramedAttachingProduct e a f) (hR : A.radius = 2)
    (d : SingularHomology M 3) (hd : detector f A hR d = 1) :
    letI : Subsingleton (SingularHomology M 2) :=
      TwoConnectedCoefficients.secondHomology_subsingleton m;
    letI := UnitSurgery.targetChartedSpace A hR;
    letI := UnitSurgery.target_isManifold A hR;
    letI := UnitSurgery.compactSpace_target A hR;
    letI : SimplyConnectedSpace (UnitSurgery.Target A hR) :=
      (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).1;
    ∀ (r' : TubularRetraction (UnitSurgery.inducedEmbedding A hR))
      (m' : UnitSurgery.Target A hR),
      letI : Subsingleton (π_ 2 (UnitSurgery.Target A hR) m') :=
        (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).2.1 m';
      invariant e a r m = invariant (UnitSurgery.inducedEmbedding A hR)
        (UnitSurgery.normalFraming A hR) r' m' := by
  let : Subsingleton (SingularHomology M 2) :=
    TwoConnectedCoefficients.secondHomology_subsingleton m
  let := UnitSurgery.targetChartedSpace A hR
  let := UnitSurgery.target_isManifold A hR
  let := UnitSurgery.compactSpace_target A hR
  let : SimplyConnectedSpace (UnitSurgery.Target A hR) :=
    (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).1
  intro r' m'
  let : Subsingleton (π_ 2 (UnitSurgery.Target A hR) m') :=
    (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).2.1 m'
  obtain ⟨-, -, hArf⟩ := native_quadratic_surgery_invariants e a r m f A hR d hd r' m'
  obtain ⟨hq', he⟩ := hArf (e.modTwoHomologyQuadraticForm_nondegenerate a r m)
  exact he

end NoExoticSixSphere.GeometricArf
