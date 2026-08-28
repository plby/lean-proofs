import Wikipedia.HopfProblem.DegreeCollapseRetainedDerivativeParity
import Wikipedia.HopfProblem.DegreeCollapseFramedSphereParityComparison

/-!
# Geometric framing parity is preserved on retained sphere representatives

A unit value of the original detector constructs a geometric dual, so the
actual native surgery target remains two-connected. Construct an exterior
representative of the zero H3 class. Its retained class maps to zero in
the actual trace, and injectivity of the native-end H3 map makes that
retained class zero as well. Third Hurewicz makes both reference spheres
nullhomotopic, so both geometric parities are zero. Comparing differences
of geometric and untwisted derivative parities with this reference removes
the possible source-twist offset. No numerical value is assigned to the
twist, and no geometric dual or parity comparison is an extra hypothesis.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.FramedRepresentative.NativeRetention

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
open SmoothCube Wikipedia.SmoothSixDPoincare SingularMayerVietoris

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [SimplyConnectedSpace M]
  [Subsingleton (SingularHomology M 2)] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : C(Sphere 3, M)}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)
  (B : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M)
  (hB : B.chart.target ⊆ retainedExterior A) (r : TubularRetraction e)

theorem retained_geometricParity (d : SingularHomology M 3)
    (hd : DualCover.markedDetector (E := Vector 4) (UnitSurgery.face A hR)
      (ContinuousLinearEquiv.refl ℝ (Vector 3)) d = 1) :
    letI := UnitSurgery.targetChartedSpace A hR;
    letI := UnitSurgery.target_isManifold A hR;
    letI := UnitSurgery.compactSpace_target A hR;
    ∀ r' : TubularRetraction (UnitSurgery.inducedEmbedding A hR),
      (UnitSurgery.inducedEmbedding A hR).geometricSphereParity (UnitSurgery.normalFraming A hR) r'
        (FramedSurgery.coreMap (E := Vector 4) (roundedFace A hR B hB)) =
      e.geometricSphereParity a r (FramedSurgery.coreMap (E := Vector 4) B) := by
  let := UnitSurgery.targetChartedSpace A hR
  let := UnitSurgery.target_isManifold A hR
  let := UnitSurgery.compactSpace_target A hR
  intro r'
  have htwo := FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd
  let : SimplyConnectedSpace (UnitSurgery.Target A hR) := htwo.1
  let m : M := FramedSurgery.coreMap (E := Vector 4) B (Stiefel.pole 3)
  let m' : UnitSurgery.Target A hR :=
    FramedSurgery.coreMap (E := Vector 4) (roundedFace A hR B hB) (Stiefel.pole 3)
  let : Subsingleton (π_ 2 M m) :=
    (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv m).injective.subsingleton
  let : Subsingleton (π_ 2 (UnitSurgery.Target A hR) m') := htwo.2.1 m'
  obtain ⟨C, hC, hCext⟩ := exists_rounded_exterior_of_zero_homology A hR 0 (map_zero _)
  have hC' : integralSphereClass
      (FramedSurgery.coreMap (E := Vector 4) (roundedFace A hR C hCext)) = 0 := by
    apply TraceBody.nativeTarget_homology_injective_three A hR
    rw [roundedFace_trace_class A hR C hCext, hC, map_zero, map_zero]
  have hz := geometricParity_zero_of_integral_class e a r m
    (FramedSurgery.coreMap (E := Vector 4) C) hC
  have hz' := geometricParity_zero_of_integral_class (UnitSurgery.inducedEmbedding A hR)
    (UnitSurgery.normalFraming A hR) r' m'
    (FramedSurgery.coreMap (E := Vector 4) (roundedFace A hR C hCext)) hC'
  have hold := geometricParity_sum_eq_derivative_faces e a r B C
  have hnew := geometricParity_sum_eq_derivative_faces (UnitSurgery.inducedEmbedding A hR)
    (UnitSurgery.normalFraming A hR) r' (roundedFace A hR B hB) (roundedFace A hR C hCext)
  rw [retained_derivativeParity A hR B hB, retained_derivativeParity A hR C hCext] at hnew
  have h := hnew.trans hold.symm
  rw [hz', hz, add_zero, add_zero] at h
  exact h

end Wikipedia.HopfProblem.DegreeCollapse.FramedRepresentative.NativeRetention
