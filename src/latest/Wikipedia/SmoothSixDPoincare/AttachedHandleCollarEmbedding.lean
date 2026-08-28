import Wikipedia.SmoothSixDPoincare.AttachedHandleCollarMap
import Wikipedia.SmoothSixDPoincare.CollaredHandleEmbeddingRadial
import Wikipedia.SmoothSixDPoincare.FramedSurgeryCompact

/-!
# The assembled whole-boundary collar is a closed embedding

Depth first identifies the two time parameters. The embedded product's
negative radius then detects a common corner whenever an old and a new
collar point agree. Thus there are exactly the original boundary incidences.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

variable {E F G H X Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace H X] {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (PuncturedHandle.UnitSphere E) F X)
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  (i : C(X, Y)) (C : InwardBoundaryCollar i) (hi : IsClosedEmbedding i)
  (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]

omit [T2Space X] [CompactSpace X] [T2Space Y] [CompactSpace Y] in
theorem collar_old_new_radius_one (r : Exterior A) (p : ClosedNewFace E F) (t : unitInterval)
    (h : oldCollarMap A i C (r, t) =
      CollaredHandleEmbedding.newCollarMap A.map i C hi.injective A.closedEmbedding.injective
        (p, t)) : ‖p.1.val‖ = 1 := by
  have hr := CollaredHandleEmbedding.parametrization_old_collar_norm A.map i C hi.injective
    A.closedEmbedding.injective (HandleCollarCoordinates.coordinates (p, t)) r.val
      (HandleCollarCoordinates.oldTime t) h.symm
  rw [HandleCollarCoordinates.coordinates_fst_norm] at hr
  change 2 * (HandleCollarCoordinates.factor t * ‖p.1.val‖) =
    1 + HandleCollarCoordinates.time t at hr
  unfold HandleCollarCoordinates.factor at hr
  have hp := mem_closedBall_zero_iff.mp p.1.property
  have hw := mul_nonneg (HandleCollarCoordinates.time_nonneg t) (sub_nonneg.mpr hp)
  nlinarith

omit [CompactSpace X] [T2Space Y] [CompactSpace Y] in
theorem collar_old_new_boundary (r : Exterior A) (p : ClosedNewFace E F) (t : unitInterval)
    (h : oldCollarMap A i C (r, t) =
      CollaredHandleEmbedding.newCollarMap A.map i C hi.injective A.closedEmbedding.injective
        (p, t)) : exteriorNewMap A n r = closedNewMap A n p := by
  have hp := collar_old_new_radius_one A i C hi r p t h
  let u : PuncturedHandle.UnitSphere E := ⟨p.1.val, mem_sphere_zero_iff_norm.mpr hp⟩
  have hh := h.trans (CollaredHandleEmbedding.newCollarMap_corner A.map i C hi.injective
    A.closedEmbedding.injective u p.2 t)
  have hb := (FaceAttachment.oldMap_eq_oldMap (bodyFaceMap A i)
    (bodyFaceMap_injective A i hi.injective) _ _).mp hh
  have hc := C.closedEmbedding.injective hb
  have hx : r = exteriorCorner A (u, p.2) :=
    Subtype.ext (congrArg (fun q : X × unitInterval => q.1) hc)
  rw [hx]
  exact exteriorNewMap_corner A n (u, p.2)

theorem collarMap_injective : Injective (collarMap A i C hi n) := by
  rintro ⟨z, t⟩ ⟨z', t'⟩ h
  have ht : t = t' := collarMap_time_injective A i C hi n (z, t) (z', t') h
  subst t'
  apply Prod.ext
  swap
  · rfl
  have hz : z ∈ range (exteriorNewMap A n) ∪ range (closedNewMap A n) :=
    (exterior_new_face_cover A n).symm ▸ mem_univ z
  have hz' : z' ∈ range (exteriorNewMap A n) ∪ range (closedNewMap A n) :=
    (exterior_new_face_cover A n).symm ▸ mem_univ z'
  rcases hz with ⟨r, rfl⟩ | ⟨p, rfl⟩
  · rcases hz' with ⟨s, rfl⟩ | ⟨q, rfl⟩
    · rw [collarMap_exterior, collarMap_exterior] at h
      have hb := (FaceAttachment.oldMap_eq_oldMap (bodyFaceMap A i)
        (bodyFaceMap_injective A i hi.injective) _ _).mp h
      have hc := C.closedEmbedding.injective hb
      exact congrArg (exteriorNewMap A n)
        (Subtype.ext (congrArg (fun q : X × unitInterval => q.1) hc))
    · rw [collarMap_exterior, collarMap_new] at h
      exact collar_old_new_boundary A i C hi n r q t h
  · rcases hz' with ⟨r, rfl⟩ | ⟨q, rfl⟩
    · rw [collarMap_new, collarMap_exterior] at h
      exact (collar_old_new_boundary A i C hi n r p t h.symm).symm
    · rw [collarMap_new, collarMap_new] at h
      have hp := (CollaredHandleEmbedding.newCollarMap_isClosedEmbedding A.map i C hi.injective
        A.closedEmbedding.injective).injective h
      exact congrArg (closedNewMap A n)
        (congrArg (fun v : ClosedNewFace E F × unitInterval => v.1) hp)

theorem collarMap_isClosedEmbedding : IsClosedEmbedding (collarMap A i C hi n) := by
  let _ : T2Space (AttachedBody A i) := attachedBodyT2Space A i hi.injective
  exact (collarMap A i C hi n).continuous.isClosedEmbedding (collarMap_injective A i C hi n)

end Wikipedia.SmoothSixDPoincare.FramedSurgery
