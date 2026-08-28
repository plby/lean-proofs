import Wikipedia.HopfProblem.DegreeCollapseSurgeryFlatEndHomology
import Wikipedia.SmoothSixDPoincare.FramedSurgeryRetainedBodyFace

/-!
# Exact flat-target formulas on the canonical surgery patches

Compute the actual flat representative on the old exterior and new open
face. The original tube embedding recognizes the whole exterior region,
including radius one. The canonical radial exchange then computes the
negative collar side, while the nonnegative side stays in the old exterior.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TraceBody

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct
open EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
open Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

theorem flatTarget_old_exterior (r : FramedSurgery.Exterior (E := Vector 4)
    (UnitSurgery.face A hR)) :
    (flatTargetInclusion A hR
      (FramedSurgery.exteriorNewMap (E := Vector 4) (UnitSurgery.face A hR) 2 r)).val =
        e.heightCylinder (r.val, 0) := by
  change (flatBoundaryHomeomorph A hR _).val = _
  rw [flatBoundaryHomeomorph_exterior]
  rfl

theorem flatTarget_new (p : FramedSurgery.NewPatch (Vector 4) (Vector 3)) :
    (flatTargetInclusion A hR
      (FramedSurgery.newMap (E := Vector 4) (UnitSurgery.face A hR) 2 p)).val =
        A.map (p.1.val, p.2.val) := by
  rw [← FramedSurgery.closedNewMap_open (E := Vector 4) (UnitSurgery.face A hR) 2 p]
  change (flatBoundaryHomeomorph A hR _).val = _
  rw [flatBoundaryHomeomorph_newFace]
  rfl

theorem tube_not_faceInterior_of_one_le (s : Sphere 3) {v : Vector 3}
    (hv : v ∈ closedBall (0 : Vector 3) A.radius) (hn : 1 ≤ ‖v‖) :
    A.tube (s, v) ∉ FramedSurgery.faceInterior (E := Vector 4) (UnitSurgery.face A hR) := by
  intro h
  obtain ⟨p, hp⟩ := FramedSurgery.faceInterior_subset_range h
  have hmem : (UnitSurgery.face A hR).map p ∈
      FramedSurgery.faceInterior (E := Vector 4) (UnitSurgery.face A hR) := hp.symm ▸ h
  have hlt := (FramedSurgery.face_mem_interior_iff (E := Vector 4)
    (UnitSurgery.face A hR) p.1 p.2).mp hmem
  have hpv : p.2.val ∈ closedBall (0 : Vector 3) A.radius :=
    (closedBall_subset_closedBall (by rw [hR]; norm_num : (1 : ℝ) ≤ A.radius)) p.2.property
  have he : (p.1, (⟨p.2.val, hpv⟩ : closedBall (0 : Vector 3) A.radius)) =
      (s, ⟨v, hv⟩) := A.tube_embedded.injective hp
  have hev := congrArg (fun z : Sphere 3 × closedBall (0 : Vector 3) A.radius ↦ z.2.val) he
  rw [hev] at hlt
  exact (not_lt_of_ge hn) hlt

theorem retainedExterior_not_faceInterior (m : retainedExterior A) :
    m.val ∉ FramedSurgery.faceInterior (E := Vector 4) (UnitSurgery.face A hR) := by
  intro h
  obtain ⟨p, hp⟩ := FramedSurgery.faceInterior_subset_range h
  apply m.property
  have houter : (1 : ℝ) ≤ outerRadius A := by
    have hh := (outerRadius_gt_handle A).le
    rwa [TraceCoreAttachment.handleRadius_eq_one A hR] at hh
  exact ⟨(p.1, p.2.val), ⟨mem_univ _,
    (closedBall_subset_closedBall houter) p.2.property⟩, hp⟩

theorem flatTarget_exterior (m : retainedExterior A) :
    (flatTargetInclusion A hR (UnitSurgery.exteriorMap A hR m)).val =
      e.heightCylinder (m.val, 0) :=
  flatTarget_old_exterior A hR ⟨m.val, retainedExterior_not_faceInterior A hR m⟩

theorem flatTarget_handle (p : boundaryHandleParameters A) :
    (flatTargetInclusion A hR (UnitSurgery.handleMap A hR p)).val =
      A.map (p.val.1, p.val.2.val) :=
  flatTarget_new A hR (UnitSurgery.handlePoint A p)

theorem flatTarget_collar_nonneg (p : boundaryCollarParameters A) (hu : 0 ≤ p.val.2.2) :
    (flatTargetInclusion A hR (UnitSurgery.collarMap A hR p)).val =
      A.collarSheet ((p.val.1, UnitSurgery.collarOriginalVector A p), 0) := by
  have hn : 1 ≤ ‖UnitSurgery.collarOriginalVector A p‖ := by
    rw [UnitSurgery.norm_collarOriginalVector]
    have hs := Real.sq_sqrt (show 0 ≤ 1 + p.val.2.2 by linarith)
    nlinarith [Real.sqrt_nonneg (1 + p.val.2.2)]
  let r : FramedSurgery.Exterior (E := Vector 4) (UnitSurgery.face A hR) :=
    ⟨A.tube (p.val.1, UnitSurgery.collarOriginalVector A p),
      tube_not_faceInterior_of_one_le A hR p.val.1
        (UnitSurgery.collarOriginalVector_mem A hR p) hn⟩
  exact flatTarget_old_exterior A hR r

theorem flatTarget_collar_neg (p : boundaryCollarParameters A) (hu : p.val.2.2 < 0) :
    (flatTargetInclusion A hR (UnitSurgery.collarMap A hR p)).val =
      A.map (Real.sqrt (1 + p.val.2.2) • p.val.1.val, p.val.2.1.val) := by
  let v := UnitSurgery.collarOriginalVector A p
  let r := Real.sqrt (1 + p.val.2.2)
  have hr : 0 < r := Real.sqrt_pos.mpr (by linarith [UnitSurgery.collar_parameter_gt_neg_one A p])
  have hs : r ^ 2 = 1 + p.val.2.2 :=
    Real.sq_sqrt (by linarith [UnitSurgery.collar_parameter_gt_neg_one A p])
  have hnorm : ‖v‖ = r := UnitSurgery.norm_collarOriginalVector A p
  have hlt : ‖v‖ < 1 := by rw [hnorm]; nlinarith
  let z : FramedSurgery.Overlap (Vector 4) (Vector 3) :=
    (p.val.1, ⟨v, UnitSurgery.collarOriginalVector_ne_zero A p, hlt⟩)
  have hold : FramedSurgery.oldOverlap (E := Vector 4) (UnitSurgery.face A hR) z =
      UnitSurgery.collarPoint A hR p := rfl
  have he := FramedSurgery.overlap_identification (E := Vector 4) (UnitSurgery.face A hR) 2 z
  rw [hold] at he
  change (flatTargetInclusion A hR
    (FramedSurgery.oldMap (E := Vector 4) (UnitSurgery.face A hR) 2
      (UnitSurgery.collarPoint A hR p))).val = _
  rw [he, flatTarget_new]
  rw [FramedSurgery.newOverlap_fst, FramedSurgery.newOverlap_snd]
  change A.map (‖v‖ • p.val.1.val, ‖v‖⁻¹ • v) = _
  rw [hnorm]
  have hv : r⁻¹ • v = p.val.2.1.val := by
    change r⁻¹ • (r • p.val.2.1.val) = _
    rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  rw [hv]

end Wikipedia.HopfProblem.DegreeCollapse.TraceBody
