import Wikipedia.HopfProblem.DegreeCollapseOuterAttachingFace
import Wikipedia.HopfProblem.DegreeCollapseRetainedTraceHomology

/-!
# Detector-kernel representatives outside the whole rounded surgery region

The outer face has exactly the full rounding tube as its range and the
same original attaching core. Apply whole-neighborhood separation to it,
starting with the constructed disjoint core representative. The result
lies in the genuine retained exterior, where the original ambient and
normal-framing formulas hold. The canonical surgery face still uses its
original radius-one construction and original atlas.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.FramedRepresentative

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
open SmoothCube Wikipedia.SmoothSixDPoincare
open SingularMayerVietoris

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

theorem exists_rounded_exterior_of_zero_homology [SimplyConnectedSpace M]
    [Subsingleton (SingularHomology M 2)] (c : SingularHomology M 3)
    (hc : DualCover.markedDetector (E := Vector 4) (UnitSurgery.face A hR)
      (ContinuousLinearEquiv.refl ℝ (Vector 3)) c = 0) :
    ∃ B : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M,
      integralSphereClass (FramedSurgery.coreMap (E := Vector 4) B) = c ∧
      B.chart.target ⊆ retainedExterior A := by
  obtain ⟨B, hclass, hdisjoint⟩ := exists_framed_avoiding_of_zero_homology e a
    (UnitSurgery.face A hR) c hc
  have hdisjoint' : Disjoint (range (FramedSurgery.coreMap (E := Vector 4) B))
      (range (FramedSurgery.coreMap (E := Vector 4) (OuterFace.outerFace A))) := by
    rw [OuterFace.outerFace_core_eq_unit A hR]
    exact hdisjoint
  obtain ⟨B', H, hB'⟩ := exists_framed_neighborhood_avoiding_full_face
    (OuterFace.outerFace A) B hdisjoint'
  refine ⟨B', (integralSphereClass_homotopic H).symm.trans hclass, ?_⟩
  rw [OuterFace.outerFace_range] at hB'
  exact hB'

namespace NativeRetention

variable (B : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M)
  (hB : B.chart.target ⊆ retainedExterior A)

include hB in
theorem rounded_unit_avoidance : B.chart.target ⊆ (range (UnitSurgery.face A hR).map)ᶜ :=
  hB.trans (OuterFace.retainedExterior_subset_unitExterior A hR)

def roundedCore : C(Sphere 3, retainedExterior A) :=
  ⟨fun s ↦ ⟨FramedSurgery.coreMap (E := Vector 4) B s,
      hB (FramedSurgery.core_mem_chart_target (E := Vector 4) B s)⟩,
    (FramedSurgery.coreMap (E := Vector 4) B).continuous.subtype_mk _⟩

def roundedFace : letI := UnitSurgery.targetChartedSpace A hR;
    SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) (UnitSurgery.Target A hR) :=
  face A hR B (rounded_unit_avoidance A hR B hB)

theorem roundedFace_core (s : Sphere 3) : letI := UnitSurgery.targetChartedSpace A hR;
    FramedSurgery.coreMap (E := Vector 4) (roundedFace A hR B hB) s =
      UnitSurgery.exteriorMap A hR (roundedCore A B hB s) := by
  let := UnitSurgery.targetChartedSpace A hR
  exact face_map A hR B (rounded_unit_avoidance A hR B hB) (s, ⟨0, by simp⟩)
    (UnitSurgery.exteriorPoint A hR (roundedCore A B hB s)) rfl

theorem roundedFace_trace_class : letI := UnitSurgery.targetChartedSpace A hR;
    singularHomologyMap (TraceBody.nativeTargetInclusion A hR) 3
      (integralSphereClass (FramedSurgery.coreMap (E := Vector 4) (roundedFace A hR B hB))) =
      singularHomologyMap (topMap A) 3
        (integralSphereClass (FramedSurgery.coreMap (E := Vector 4) B)) :=
  retained_trace_class A hR B (rounded_unit_avoidance A hR B hB)

end NativeRetention
end Wikipedia.HopfProblem.DegreeCollapse.FramedRepresentative
