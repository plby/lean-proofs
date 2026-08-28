import Wikipedia.HopfProblem.DegreeCollapseRetainedTraceHomology
import Wikipedia.HopfProblem.DegreeCollapseHomologicalDualSurgery
import Wikipedia.HopfProblem.DegreeCollapseIntegerKernelComparison

/-!
# The detector kernel is precisely the old classes that lift to the new end

Constructed exterior representatives give one kernel containment for the
actual marked detector and reverse trace coordinate. A unit detector value
constructs a geometric dual and kills the actual belt. Both coordinates
are then onto the integers, so the containment is equality. This retains
the original end maps and the original attaching class. Existence of the
unit value is still a hypothesis, not a global duality assertion.
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

def detector : SingularHomology M 3 →ₗ[ℤ] ℤ :=
  DualCover.markedDetector (E := Vector 4) (UnitSurgery.face A hR)
    (ContinuousLinearEquiv.refl ℝ (Vector 3))

def traceCoordinate : SingularHomology M 3 →ₗ[ℤ] ℤ :=
  (TraceBody.nativeMiddleCoordinate f A hR).comp (singularHomologyMap (topMap A) 3)

theorem kernel_le : LinearMap.ker (detector f A hR) ≤
    LinearMap.ker (traceCoordinate f A hR) := by
  intro x hx
  let := UnitSurgery.targetChartedSpace A hR
  obtain ⟨B, _, hB⟩ :=
    FramedRepresentative.NativeRetention.exists_native_representative_of_zero_homology A hR x hx
  have hr : singularHomologyMap (topMap A) 3 x ∈
      LinearMap.range (singularHomologyMap (TraceBody.nativeTargetInclusion A hR) 3) :=
    ⟨integralSphereClass (FramedSurgery.coreMap (E := Vector 4) B), hB⟩
  rw [TraceBody.nativeMiddleCoordinate_exact f A hR] at hr
  exact hr

theorem belt_zero_of_unit (d : SingularHomology M 3) (hd : detector f A hR d = 1) :
    TraceBody.nativeBeltClass f A hR = 0 := by
  obtain ⟨B, q, u, _, hcross, ht⟩ :=
    FramedDual.exists_framed_dual_of_unit_homology f A hR d hd
  obtain ⟨_, _, hz⟩ := TraceBody.geometric_dual_primitive_and_belt_zero
    f A hR B q u hcross ht
  exact hz

theorem traceCoordinate_surjective (d : SingularHomology M 3)
    (hd : detector f A hR d = 1) : Surjective (traceCoordinate f A hR) :=
  (TraceBody.nativeMiddleCoordinate_surjective f A hR (belt_zero_of_unit f A hR d hd)).comp
    (TraceCoreAttachment.topMap_homology_surjective_three f A hR)

theorem kernel_eq (d : SingularHomology M 3) (hd : detector f A hR d = 1) :
    LinearMap.ker (detector f A hR) = LinearMap.ker (traceCoordinate f A hR) :=
  IntegerKernelComparison.kernel_eq _ _ d hd (kernel_le f A hR)
    (traceCoordinate_surjective f A hR d hd)

theorem coordinate_equal_or_negative (d : SingularHomology M 3)
    (hd : detector f A hR d = 1) :
    traceCoordinate f A hR = detector f A hR ∨
      traceCoordinate f A hR = -detector f A hR :=
  IntegerKernelComparison.equal_or_negative _ _ d hd (kernel_le f A hR)
    (traceCoordinate_surjective f A hR d hd)

theorem old_class_lifts_iff (d : SingularHomology M 3) (hd : detector f A hR d = 1)
    (x : SingularHomology M 3) :
    (∃ y : SingularHomology (UnitSurgery.Target A hR) 3,
      singularHomologyMap (TraceBody.nativeTargetInclusion A hR) 3 y =
        singularHomologyMap (topMap A) 3 x) ↔ detector f A hR x = 0 := by
  change singularHomologyMap (topMap A) 3 x ∈
    LinearMap.range (singularHomologyMap (TraceBody.nativeTargetInclusion A hR) 3) ↔ _
  rw [TraceBody.nativeMiddleCoordinate_exact f A hR]
  change x ∈ LinearMap.ker (traceCoordinate f A hR) ↔ x ∈ LinearMap.ker (detector f A hR)
  rw [kernel_eq f A hR d hd]

theorem attachingClass_detector_zero (d : SingularHomology M 3)
    (hd : detector f A hR d = 1) :
    detector f A hR (TraceCoreAttachment.originalSphereClass f) = 0 := by
  have hT : singularHomologyMap (topMap A) 3 (TraceCoreAttachment.originalSphereClass f) = 0 := by
    change TraceCoreAttachment.originalSphereClass f ∈ LinearMap.ker _
    rw [TraceCoreAttachment.topMap_three_kernel f A hR]
    exact Submodule.subset_span (mem_singleton _)
  have hx : TraceCoreAttachment.originalSphereClass f ∈ LinearMap.ker (traceCoordinate f A hR) := by
    change TraceBody.nativeMiddleCoordinate f A hR
      (singularHomologyMap (topMap A) 3 (TraceCoreAttachment.originalSphereClass f)) = 0
    rw [hT, map_zero]
  rw [← kernel_eq f A hR d hd] at hx
  exact hx

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryDetector
