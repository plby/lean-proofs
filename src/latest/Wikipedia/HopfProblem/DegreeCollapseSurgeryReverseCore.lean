import Wikipedia.HopfProblem.DegreeCollapseSurgeryFlatBoundary

/-!
# The same actual trace body is a three-cell attachment from the surgery end

The flat surgery boundary together with the whole original handle covers
the flattened body. Their intersection is exactly D4 × S2. Exchange the
two handle factors and apply the existing relative handle deformation.
The resulting core disk is the literal map v ↦ A.map (0,v).
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TraceBody

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct
open Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

theorem body_eq_flat_union : bodySet A = flatBoundarySet A hR ∪
    range (TraceCoreAttachment.unitHandleMap A hR) := by
  ext x
  constructor
  · rintro (⟨m, rfl⟩ | hx)
    · have hm : m ∈
          range (FramedSurgery.exteriorOldMap (E := Vector 4) (UnitSurgery.face A hR)) ∪
            range (UnitSurgery.face A hR).map := by
        rw [FramedSurgery.exterior_old_face_cover]
        trivial
      rcases hm with ⟨r, rfl⟩ | ⟨p, rfl⟩
      · exact Or.inl (Or.inl ⟨r, rfl⟩)
      · right
        refine ⟨(⟨p.1.val, sphere_subset_closedBall p.1.property⟩, p.2), ?_⟩
        have hv : p.2.val ∈ closedBall (0 : Vector 3) A.radius :=
          (closedBall_subset_closedBall (by rw [hR]; norm_num : (1 : ℝ) ≤ A.radius)) p.2.property
        exact (A.map_boundary p.1 p.2.val hv).trans (e.heightCylinder_zero _).symm
    · right
      rwa [TraceCoreAttachment.range_unitHandleMap]
  · rintro (hx | hx)
    · exact flatBoundary_subset_body A hR hx
    · right
      rwa [TraceCoreAttachment.range_unitHandleMap] at hx

theorem unitHandleMap_mem_flat_iff (z : Handle.Space (N := Vector 4) (P := Vector 3)) :
    TraceCoreAttachment.unitHandleMap A hR z ∈ flatBoundarySet A hR ↔ ‖z.2.val‖ = 1 := by
  constructor
  · rintro (⟨r, hr⟩ | ⟨p, hp⟩)
    · have hv : z.2.val ∈ closedBall (0 : Vector 3) A.radius :=
        (closedBall_subset_closedBall (by rw [hR]; norm_num : (1 : ℝ) ≤ A.radius)) z.2.property
      have he : A.map (z.1.val, z.2.val) = e.heightCylinder (r.val, 0) := hr.symm
      obtain ⟨s, hs, hm, ht⟩ := (UnroundedTrace.intersection_iff A z.1.property hv r.val
        ⟨le_rfl, (UnroundedTrace.height_pos A).le⟩).mp he
      apply le_antisymm (mem_closedBall_zero_iff.mp z.2.property)
      apply le_of_not_gt
      intro hlt
      apply r.property
      have hmem := (FramedSurgery.face_mem_interior_iff (E := Vector 4)
        (UnitSurgery.face A hR) s z.2).mpr hlt
      change A.tube (s, z.2.val) ∈ _ at hmem
      rwa [hm] at hmem
    · have hz : FramedSurgery.wholeNewFace (Vector 4) (Vector 3) p = z :=
        TraceCoreAttachment.injective_unitHandleMap A hR hp
      have hv := congrArg (fun w : Handle.Space (N := Vector 4) (P := Vector 3) ↦ w.2.val) hz
      exact (congrArg norm hv).symm.trans (mem_sphere_zero_iff_norm.mp p.2.property)
  · intro hz
    exact Or.inr ⟨(z.1, ⟨z.2.val, mem_sphere_zero_iff_norm.mpr hz⟩), rfl⟩

def reverseHandleMap : C(Handle.Space (N := Vector 3) (P := Vector 4),
    Vector (e.ambientDimension + 6)) :=
  (TraceCoreAttachment.unitHandleMap A hR).comp ⟨Prod.swap, continuous_swap⟩

theorem reverseHandleMap_apply (z : Handle.Space (N := Vector 3) (P := Vector 4)) :
    reverseHandleMap A hR z = A.map (z.2.val, z.1.val) := rfl

theorem injective_reverseHandleMap : Injective (reverseHandleMap A hR) :=
  (TraceCoreAttachment.injective_unitHandleMap A hR).comp Prod.swap_injective

theorem range_reverseHandleMap : range (reverseHandleMap A hR) =
    range (TraceCoreAttachment.unitHandleMap A hR) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z.swap, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z.swap, rfl⟩

theorem reverseHandleMap_mem_flat_iff (z : Handle.Space (N := Vector 3) (P := Vector 4)) :
    reverseHandleMap A hR z ∈ flatBoundarySet A hR ↔ ‖z.1.val‖ = 1 :=
  unitHandleMap_mem_flat_iff A hR z.swap

def reverseCoreMap : C(closedBall (0 : Vector 3) 1, Vector (e.ambientDimension + 6)) :=
  (reverseHandleMap A hR).comp
    ⟨fun v ↦ (v, ⟨0, mem_closedBall_self (by norm_num)⟩), continuous_id.prodMk continuous_const⟩

theorem reverseCoreMap_apply (v : closedBall (0 : Vector 3) 1) :
    reverseCoreMap A hR v = A.map (0, v.val) := rfl

theorem injective_reverseCoreMap : Injective (reverseCoreMap A hR) := by
  intro v w h
  exact congrArg Prod.fst (injective_reverseHandleMap A hR h)

theorem reverseCoreMap_mem_flat_iff (v : closedBall (0 : Vector 3) 1) :
    reverseCoreMap A hR v ∈ flatBoundarySet A hR ↔ ‖v.val‖ = 1 :=
  reverseHandleMap_mem_flat_iff A hR (v, ⟨0, mem_closedBall_self (by norm_num)⟩)

theorem image_reverse_handle_core :
    reverseHandleMap A hR '' CoreAttachment.Core = range (reverseCoreMap A hR) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.1, ?_⟩
    change A.map (0, z.1.val) = A.map (z.2.val, z.1.val)
    rw [show z.2.val = 0 from hz]
  · rintro ⟨v, rfl⟩
    exact ⟨(v, ⟨0, mem_closedBall_self (by norm_num)⟩), rfl, rfl⟩

def reverseCoreUnionBodyHomotopyEquiv :
    ↥(flatBoundarySet A hR ∪ range (reverseCoreMap A hR)) ≃ₕ bodySet A := by
  let B := flatBoundarySet A hR
  let : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_flatBoundarySet A hR)
  let core := CoreAttachment.coreUnionHomotopyEquiv B (reverseHandleMap A hR)
    (injective_reverseHandleMap A hR) (reverseHandleMap_mem_flat_iff A hR)
  let mark := Homeomorph.setCongr
    (congrArg (fun S : Set (Vector (e.ambientDimension + 6)) ↦ B ∪ S)
      (image_reverse_handle_core A hR))
  let full : Attachment.Union B (reverseHandleMap A hR) ≃ₜ bodySet A :=
    Homeomorph.setCongr (by rw [range_reverseHandleMap]; exact (body_eq_flat_union A hR).symm)
  exact mark.symm.toHomotopyEquiv.trans (core.trans full.toHomotopyEquiv)

theorem reverseCoreUnionBodyHomotopyEquiv_ambient
    (x : ↥(flatBoundarySet A hR ∪ range (reverseCoreMap A hR))) :
    (reverseCoreUnionBodyHomotopyEquiv A hR x).val = x.val := rfl

def reverseCoreUnionTraceHomotopyEquiv :
    ↥(flatBoundarySet A hR ∪ range (reverseCoreMap A hR)) ≃ₕ RoundedTrace.ambientSet A :=
  (reverseCoreUnionBodyHomotopyEquiv A hR).trans (bodyTraceHomotopyEquiv A)

theorem reverseCoreUnionTraceHomotopyEquiv_ambient
    (x : ↥(flatBoundarySet A hR ∪ range (reverseCoreMap A hR))) :
    (reverseCoreUnionTraceHomotopyEquiv A hR x).val = x.val := rfl

def reverseCorePresentation : EmbeddedCellAttachment (Vector 3)
    ↥(flatBoundarySet A hR ∪ range (reverseCoreMap A hR)) :=
  EmbeddedCellAttachment.ofUnion (flatBoundarySet A hR) (reverseCoreMap A hR)
    (isClosed_flatBoundarySet A hR)
    ((reverseCoreMap A hR).continuous.isClosedEmbedding (injective_reverseCoreMap A hR))
    (reverseCoreMap_mem_flat_iff A hR)

end Wikipedia.HopfProblem.DegreeCollapse.TraceBody
