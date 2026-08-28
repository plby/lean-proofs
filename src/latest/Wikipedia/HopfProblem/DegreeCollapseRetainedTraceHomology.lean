import Wikipedia.HopfProblem.DegreeCollapseRetainedHomologyRepresentative
import Wikipedia.HopfProblem.DegreeCollapseSurgeryNativeEndComparison

/-!
# A retained framed representative carries the same actual trace class

The original cylinder gives a homotopy from its top inclusion to the
literal bottom map. On a face outside the full attaching face, the flat
native-end map is exactly this bottom map. The checked rounding homotopy
therefore compares the original and retained core maps in the actual
rounded trace. The resulting integral homology identity uses the original
two end inclusions, not an abstract quotient representative.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.FramedRepresentative.NativeRetention

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
open SmoothCube Wikipedia.SmoothSixDPoincare
open SingularMayerVietoris PeriodTorusHigherHomology

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def cylinderIntoTrace : C(UnroundedTrace.Cylinder A, ambientSet A) :=
  (TraceCoreAttachment.cylinderInclusion A).comp
    (TraceCoreAttachment.cylinderHomeomorph A).toHomotopyEquiv.toFun

def bottomSection : C(M, UnroundedTrace.Cylinder A) :=
  ⟨fun m ↦ (m, ⟨0, le_rfl, (UnroundedTrace.height_pos A).le⟩),
    continuous_id.prodMk continuous_const⟩

def bottomTraceMap : C(M, ambientSet A) := (cylinderIntoTrace A).comp (bottomSection A)

theorem top_homotopic_bottom : (topMap A).Homotopic (bottomTraceMap A) := by
  have H : ((TraceCoreAttachment.cylinderTopSection A).comp
      (TraceCoreAttachment.cylinderProjection A)).Homotopic
      (ContinuousMap.id (UnroundedTrace.Cylinder A)) :=
    ⟨TraceCoreAttachment.cylinderContraction A⟩
  have H' := ((ContinuousMap.Homotopic.refl (cylinderIntoTrace A)).comp H).comp
    (ContinuousMap.Homotopic.refl (bottomSection A))
  exact H'

variable (hR : A.radius = 2)
  (B : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M)
  (hB : B.chart.target ⊆ (range (UnitSurgery.face A hR).map)ᶜ)

theorem flat_retained_core : letI := UnitSurgery.targetChartedSpace A hR;
    (TraceBody.flatTargetInclusion A hR).comp
      (FramedSurgery.coreMap (E := Vector 4) (face A hR B hB)) =
      (bottomTraceMap A).comp (FramedSurgery.coreMap (E := Vector 4) B) := by
  let := UnitSurgery.targetChartedSpace A hR
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  have hs : FramedSurgery.coreMap (E := Vector 4) B s ∉
      FramedSurgery.faceInterior (E := Vector 4) (UnitSurgery.face A hR) := by
    intro h
    exact hB (FramedSurgery.core_mem_chart_target (E := Vector 4) B s)
      (FramedSurgery.faceInterior_subset_range (E := Vector 4) h)
  let x : FramedSurgery.Exterior (E := Vector 4) (UnitSurgery.face A hR) :=
    ⟨FramedSurgery.coreMap (E := Vector 4) B s, hs⟩
  change (TraceBody.flatTargetInclusion A hR
    (FramedSurgery.coreMap (E := Vector 4) (face A hR B hB) s)).val =
      e.heightCylinder (FramedSurgery.coreMap (E := Vector 4) B s, 0)
  rw [face_core]
  exact TraceBody.flatTarget_old_exterior A hR x

theorem native_retained_homotopic_original : letI := UnitSurgery.targetChartedSpace A hR;
    ((TraceBody.nativeTargetInclusion A hR).comp
      (FramedSurgery.coreMap (E := Vector 4) (face A hR B hB))).Homotopic
      ((topMap A).comp (FramedSurgery.coreMap (E := Vector 4) B)) := by
  let := UnitSurgery.targetChartedSpace A hR
  have H := (TraceBody.nativeTarget_homotopic_flat A hR).comp
    (ContinuousMap.Homotopic.refl (FramedSurgery.coreMap (E := Vector 4) (face A hR B hB)))
  rw [flat_retained_core A hR B hB] at H
  exact H.trans ((top_homotopic_bottom A).comp
    (ContinuousMap.Homotopic.refl (FramedSurgery.coreMap (E := Vector 4) B))).symm

theorem retained_trace_class : letI := UnitSurgery.targetChartedSpace A hR;
    singularHomologyMap (TraceBody.nativeTargetInclusion A hR) 3
      (integralSphereClass (FramedSurgery.coreMap (E := Vector 4) (face A hR B hB))) =
      singularHomologyMap (topMap A) 3
        (integralSphereClass (FramedSurgery.coreMap (E := Vector 4) B)) := by
  let := UnitSurgery.targetChartedSpace A hR
  have H := homotopic_homologyMap (native_retained_homotopic_original A hR B hB) 3
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at H
  exact congrArg (fun L ↦ L integralCubeSphereClass) H

theorem exists_native_representative_of_zero_homology [SimplyConnectedSpace M]
    [Subsingleton (SingularHomology M 2)] (c : SingularHomology M 3)
    (hc : DualCover.markedDetector (E := Vector 4) (UnitSurgery.face A hR)
      (ContinuousLinearEquiv.refl ℝ (Vector 3)) c = 0) :
    letI := UnitSurgery.targetChartedSpace A hR;
    ∃ C : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) (UnitSurgery.Target A hR),
      Disjoint C.chart.target
        (range (FramedSurgery.newMap (E := Vector 4) (UnitSurgery.face A hR) 2)) ∧
      singularHomologyMap (TraceBody.nativeTargetInclusion A hR) 3
        (integralSphereClass (FramedSurgery.coreMap (E := Vector 4) C)) =
        singularHomologyMap (topMap A) 3 c := by
  let := UnitSurgery.targetChartedSpace A hR
  obtain ⟨B, hclass, hB⟩ := exists_framed_exterior_of_zero_homology e a
    (UnitSurgery.face A hR) c hc
  refine ⟨face A hR B hB, face_avoids_new A hR B hB, ?_⟩
  rw [retained_trace_class A hR B hB, hclass]

end Wikipedia.HopfProblem.DegreeCollapse.FramedRepresentative.NativeRetention
