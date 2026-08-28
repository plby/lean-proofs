import Wikipedia.HopfProblem.DegreeCollapseSurgeryDetectorQuotient
import Wikipedia.HopfProblem.DegreeCollapseRetainedGeometricParity
import Wikipedia.NoExoticSixSphere.IntegralHomologyQuadraticParity

/-!
# The actual surgery homology map preserves geometric quadratic parity

Every detector-kernel class has a full framed representative outside the
larger rounding tube. The trace identity identifies its retained class
with the constructed native lift. Hurewicz and the retained geometric
parity comparison therefore identify the actual homology parities. Their
quadratic identities also identify the actual mod-two intersection values
on these integral classes. No integer-valued intersection form is asserted.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryDetector

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
open SmoothCube Wikipedia.SmoothSixDPoincare
open SingularMayerVietoris PeriodTorusHigherHomology

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [SimplyConnectedSpace M]
  [Subsingleton (SingularHomology M 2)]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}
  (f : C(Sphere 3, M)) (A : FramedAttachingProduct e a f) (hR : A.radius = 2)
  (d : SingularHomology M 3) (hd : detector f A hR d = 1)
  (r : TubularRetraction e) (m : M) [Subsingleton (π_ 2 M m)]

theorem nativeLift_parity :
    letI := UnitSurgery.targetChartedSpace A hR;
    letI := UnitSurgery.target_isManifold A hR;
    letI := UnitSurgery.compactSpace_target A hR;
    letI : SimplyConnectedSpace (UnitSurgery.Target A hR) :=
      (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).1;
    ∀ (r' : TubularRetraction (UnitSurgery.inducedEmbedding A hR)) (m' : UnitSurgery.Target A hR),
      letI : Subsingleton (π_ 2 (UnitSurgery.Target A hR) m') :=
        (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).2.1 m';
      ∀ x : LinearMap.ker (detector f A hR),
        (UnitSurgery.inducedEmbedding A hR).integralHomologyParity
          (UnitSurgery.normalFraming A hR) r' m' (nativeLift f A hR d hd x) =
        e.integralHomologyParity a r m x := by
  let := UnitSurgery.targetChartedSpace A hR
  let := UnitSurgery.target_isManifold A hR
  let := UnitSurgery.compactSpace_target A hR
  let : SimplyConnectedSpace (UnitSurgery.Target A hR) :=
    (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).1
  intro r' m'
  let : Subsingleton (π_ 2 (UnitSurgery.Target A hR) m') :=
    (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).2.1 m'
  intro x
  obtain ⟨B, hclass, hB⟩ := FramedRepresentative.exists_rounded_exterior_of_zero_homology
    A hR x.val x.property
  have hy : nativeLift f A hR d hd x = integralSphereClass
      (FramedSurgery.coreMap (E := Vector 4)
        (FramedRepresentative.NativeRetention.roundedFace A hR B hB)) := by
    apply nativeLift_eq_of_trace
    rw [FramedRepresentative.NativeRetention.roundedFace_trace_class, hclass]
  rw [hy, integralHomologyParity_sphereClass, ← hclass, integralHomologyParity_sphereClass]
  exact FramedRepresentative.NativeRetention.retained_geometricParity A hR B hB r d hd r'

theorem nativeLift_intersection :
    letI := UnitSurgery.targetChartedSpace A hR;
    letI := UnitSurgery.target_isManifold A hR;
    letI := UnitSurgery.compactSpace_target A hR;
    letI : SimplyConnectedSpace (UnitSurgery.Target A hR) :=
      (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).1;
    ∀ (r' : TubularRetraction (UnitSurgery.inducedEmbedding A hR)) (m' : UnitSurgery.Target A hR),
      letI : Subsingleton (π_ 2 (UnitSurgery.Target A hR) m') :=
        (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).2.1 m';
      ∀ x y : LinearMap.ker (detector f A hR),
        (UnitSurgery.inducedEmbedding A hR).integralHomologyIntersection r' m'
          (nativeLift f A hR d hd x) (nativeLift f A hR d hd y) =
        e.integralHomologyIntersection r m x y := by
  let := UnitSurgery.targetChartedSpace A hR
  let := UnitSurgery.target_isManifold A hR
  let := UnitSurgery.compactSpace_target A hR
  let : SimplyConnectedSpace (UnitSurgery.Target A hR) :=
    (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).1
  intro r' m'
  let : Subsingleton (π_ 2 (UnitSurgery.Target A hR) m') :=
    (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).2.1 m'
  intro x y
  have h := nativeLift_parity f A hR d hd r m r' m' (x + y)
  rw [map_add, integralHomologyParity_add] at h
  change _ = e.integralHomologyParity a r m (x.val + y.val) at h
  rw [integralHomologyParity_add, nativeLift_parity f A hR d hd r m r' m' x,
    nativeLift_parity f A hR d hd r m r' m' y] at h
  exact add_left_cancel h

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryDetector
