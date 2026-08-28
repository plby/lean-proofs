import Wikipedia.HopfProblem.DegreeCollapseFramedFaceShrinking
import Wikipedia.SmoothSixDPoincare.ChartedFaceAvoidance
import Wikipedia.SmoothSixDPoincare.SmoothClosedFaceTargetRestriction
import Wikipedia.SmoothSixDPoincare.AmbientIsotopyInverse
import Wikipedia.SmoothSixDPoincare.AmbientIsotopyHomology

/-!
# Disjoint full framed neighborhoods from disjoint sphere cores

First shrink the moving face inside the complement of the fixed core.
Shrink the fixed face away from that entire moving face by a supported
ambient isotopy. Its inverse moves the moving face off the original full
fixed face. Restricting its actual chart gives whole-target avoidance.
The original fixed face is unchanged in the final result, and the moving
core retains its actual homotopy class.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.FramedRepresentative

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [T2Space M]
  (A B : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M)

theorem exists_framed_neighborhood_avoiding_full_face
    (hdisjoint : Disjoint (range (FramedSurgery.coreMap (E := Vector 4) B))
      (range (FramedSurgery.coreMap (E := Vector 4) A))) :
    ∃ B' : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M,
      (FramedSurgery.coreMap (E := Vector 4) B).Homotopic
        (FramedSurgery.coreMap (E := Vector 4) B') ∧
      B'.chart.target ⊆ (range A.map)ᶜ := by
  obtain ⟨C, hCcore, hCtarget⟩ := exists_shrunk_face_in_open B
    (FramedSurgery.oldPatch (E := Vector 4) A) (FramedSurgery.oldPatch (E := Vector 4) A).isOpen
    (fun s ↦ disjoint_left.mp hdisjoint (mem_range_self s))
  have hAcore (s : Sphere 3) : A.map (s, ⟨0, by simp⟩) ∉ range C.map := by
    rintro ⟨p, hp⟩
    have hpt : C.map p ∈ C.chart.target := by
      rw [← C.point p.1 p.2]
      exact C.chart.map_source (C.source ⟨mem_univ _, p.2.property⟩)
    have havoid := hCtarget hpt
    apply havoid
    exact ⟨s, hp.symm⟩
  obtain ⟨D, hD, havoid⟩ := SupportedDiffeomorph.exists_avoiding_of_charted_face
    A.chart A.map A.source A.point (isCompact_range C.map.continuous).isClosed hAcore
  let C' := C.postcompose D.symm
  have hdisjoint' : Disjoint (range C'.map) (range A.map) := by
    apply disjoint_left.mpr
    rintro z ⟨p, rfl⟩ ⟨q, hq⟩
    have he : D (A.map q) = C.map p :=
      (congrArg D hq).trans (D.apply_symm_apply (C.map p))
    exact disjoint_left.mp havoid ⟨q, rfl⟩ ⟨p, he.symm⟩
  let B' := C'.avoidClosed (range A.map) (isCompact_range A.map.continuous).isClosed hdisjoint'
  have H : (FramedSurgery.coreMap (E := Vector 4) C).Homotopic
      (FramedSurgery.coreMap (E := Vector 4) C') :=
    hD.symm.comp_homotopic (FramedSurgery.coreMap (E := Vector 4) C)
  refine ⟨B', ?_, fun _ hy ↦ hy.1⟩
  change (FramedSurgery.coreMap (E := Vector 4) B).Homotopic
    (FramedSurgery.coreMap (E := Vector 4) C')
  rwa [hCcore] at H

end Wikipedia.HopfProblem.DegreeCollapse.FramedRepresentative
