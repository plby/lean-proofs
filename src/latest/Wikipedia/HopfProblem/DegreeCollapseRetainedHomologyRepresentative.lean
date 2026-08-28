import Wikipedia.HopfProblem.DegreeCollapseFramedZeroDetector
import Wikipedia.HopfProblem.DegreeCollapseDisjointFramedNeighborhoods
import Wikipedia.SmoothSixDPoincare.FramedSurgeryRetainedFace

/-!
# Full exterior representatives and their actual native surgery faces

Every class in the actual detector kernel is represented by a full framed
face whose whole chart avoids the original attaching face. The canonical
old patch retains that entire face in the native surgery atlas, with its
literal point map and full chart target recorded. Its new chart avoids
the whole new handle patch. No replacement atlas or abstract class map is
used to define this retained representative.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.FramedRepresentative

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open EuclideanEmbedding SmoothCube Wikipedia.SmoothSixDPoincare
open SingularMayerVietoris

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M]

theorem exists_framed_exterior_of_zero_homology [SimplyConnectedSpace M]
    [Subsingleton (SingularHomology M 2)]
    (e : EuclideanEmbedding 6 M)
    (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
    (A : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M)
    (c : SingularHomology M 3)
    (hc : DualCover.markedDetector (E := Vector 4) A
      (ContinuousLinearEquiv.refl ℝ (Vector 3)) c = 0) :
    ∃ B : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M,
      integralSphereClass (FramedSurgery.coreMap (E := Vector 4) B) = c ∧
      B.chart.target ⊆ (range A.map)ᶜ := by
  obtain ⟨B, hB, hdisjoint⟩ := exists_framed_avoiding_of_zero_homology e a A c hc
  obtain ⟨B', H, hB'⟩ := exists_framed_neighborhood_avoiding_full_face A B hdisjoint
  exact ⟨B', (integralSphereClass_homotopic H).symm.trans hB, hB'⟩

namespace NativeRetention

open EuclideanEmbedding.FramedAttachingProduct

variable {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)
  (B : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M)
  (hB : B.chart.target ⊆ (range (UnitSurgery.face A hR).map)ᶜ)

include hB in
theorem chart_target_old : B.chart.target ⊆ FramedSurgery.oldPatch (E := Vector 4)
    (UnitSurgery.face A hR) := by
  intro y hy hcore
  obtain ⟨s, hs⟩ := hcore
  exact hB hy ⟨(s, ⟨0, by simp⟩), hs⟩

def face : letI := UnitSurgery.targetChartedSpace A hR;
    SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) (UnitSurgery.Target A hR) :=
  (UnitSurgery.boundaryData A hR).retainFace B (chart_target_old A hR B hB)

theorem face_map (p : Sphere 3 × MorseHandle.UnitDisk (Vector 3))
    (x : FramedSurgery.oldPatch (E := Vector 4) (UnitSurgery.face A hR))
    (hx : x.val = B.map p) : letI := UnitSurgery.targetChartedSpace A hR;
    (face A hR B hB).map p = FramedSurgery.oldMap (E := Vector 4) (UnitSurgery.face A hR) 2 x :=
  (UnitSurgery.boundaryData A hR).retainFace_map B (chart_target_old A hR B hB) p x hx

theorem face_target : letI := UnitSurgery.targetChartedSpace A hR;
    (face A hR B hB).chart.target =
      FramedSurgery.oldMap (E := Vector 4) (UnitSurgery.face A hR) 2 ''
        {x : FramedSurgery.oldPatch (E := Vector 4) (UnitSurgery.face A hR) |
          x.val ∈ B.chart.target} :=
  (UnitSurgery.boundaryData A hR).retainFace_chart_target B (chart_target_old A hR B hB)

theorem face_avoids_new : letI := UnitSurgery.targetChartedSpace A hR;
    Disjoint (face A hR B hB).chart.target
      (range (FramedSurgery.newMap (E := Vector 4) (UnitSurgery.face A hR) 2)) :=
  (UnitSurgery.boundaryData A hR).retainFace_chart_avoids_new B (chart_target_old A hR B hB)
    (disjoint_left.mpr (fun _ hy hz ↦ hB hy hz))

def oldCore : C(Sphere 3, FramedSurgery.oldPatch (E := Vector 4) (UnitSurgery.face A hR)) :=
  ⟨fun s ↦ ⟨FramedSurgery.coreMap (E := Vector 4) B s,
      chart_target_old A hR B hB (FramedSurgery.core_mem_chart_target (E := Vector 4) B s)⟩,
    (FramedSurgery.coreMap (E := Vector 4) B).continuous.subtype_mk _⟩

theorem face_core : letI := UnitSurgery.targetChartedSpace A hR;
    FramedSurgery.coreMap (E := Vector 4) (face A hR B hB) =
      (FramedSurgery.oldMap (E := Vector 4) (UnitSurgery.face A hR) 2).comp
        (oldCore A hR B hB) := by
  let := UnitSurgery.targetChartedSpace A hR
  apply ContinuousMap.ext
  intro s
  exact face_map A hR B hB (s, ⟨0, by simp⟩) (oldCore A hR B hB s) rfl

end NativeRetention
end Wikipedia.HopfProblem.DegreeCollapse.FramedRepresentative
