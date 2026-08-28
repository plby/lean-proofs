import Wikipedia.HopfProblem.DegreeCollapseSurgeryCylinder

/-!
# Collapse the actual trace cylinder while fixing its whole handle

The cylinder contracts to height zero. Its intersection with the actual
handle is already at height zero, so the relative quotient construction
descends this motion while fixing the handle. The endpoint is the actual
ambient union of the bottom manifold and the whole handle. No new topology
or boundary identification is imposed on that union.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.TraceBody

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def bottomMap : C(M, Vector (e.ambientDimension + 6)) :=
  (UnroundedTrace.cylinderMap A).comp
    ⟨fun m ↦ (m, ⟨0, le_rfl, (UnroundedTrace.height_pos A).le⟩),
      continuous_id.prodMk continuous_const⟩

def bodySet : Set (Vector (e.ambientDimension + 6)) :=
  range (bottomMap A) ∪ range (UnroundedTrace.handleMap A)

theorem body_subset_unrounded : bodySet A ⊆ UnroundedTrace.ambientSet A := by
  rintro x (⟨m, rfl⟩ | hx)
  · exact Or.inl ⟨(m, ⟨0, le_rfl, (UnroundedTrace.height_pos A).le⟩), rfl⟩
  · exact Or.inr hx

theorem isCompact_bodySet : IsCompact (bodySet A) :=
  (isCompact_range (bottomMap A).continuous).union
    (isCompact_range (UnroundedTrace.handleMap A).continuous)

def cylinderBottom : C(UnroundedTrace.Cylinder A, UnroundedTrace.Cylinder A) :=
  ⟨fun p ↦ (p.1, ⟨0, le_rfl, (UnroundedTrace.height_pos A).le⟩),
    continuous_fst.prodMk continuous_const⟩

def cylinderMotion : (ContinuousMap.id (UnroundedTrace.Cylinder A)).Homotopy
    (cylinderBottom A) := by
  have htime (z : I × UnroundedTrace.Cylinder A) :
      (1 - (z.1 : ℝ)) * z.2.2.val ∈ Icc 0 (UnroundedTrace.height A) := by
    constructor
    · exact mul_nonneg (sub_nonneg.mpr z.1.property.2) z.2.2.property.1
    · nlinarith [mul_nonneg z.1.property.1 z.2.2.property.1, z.2.2.property.2]
  refine {
    toFun := fun z ↦ (z.2.1, ⟨(1 - (z.1 : ℝ)) * z.2.2.val, htime z⟩)
    continuous_toFun := by fun_prop
    map_zero_left := ?_
    map_one_left := ?_ }
  · intro p
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change (1 - (0 : ℝ)) * p.2.val = p.2.val
      simp
  · intro p
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change (1 - (1 : ℝ)) * p.2.val = 0
      simp

def cylinderHandleFace : Set (UnroundedTrace.Cylinder A) :=
  (UnroundedTrace.cylinderMap A) ⁻¹' range (UnroundedTrace.handleMap A)

theorem height_zero_on_handle (p : UnroundedTrace.Cylinder A)
    (hp : p ∈ cylinderHandleFace A) : p.2.val = 0 := by
  obtain ⟨q, hq⟩ := hp
  have h := (UnroundedTrace.intersection_iff A q.1.property
    (UnroundedTrace.handle_vector_mem A q) p.1 p.2.property).mp hq
  obtain ⟨s, hs, hm, ht⟩ := h
  exact ht

def cylinderRelativeMotion : (ContinuousMap.id (UnroundedTrace.Cylinder A)).HomotopyRel
    (cylinderBottom A) (cylinderHandleFace A) where
  __ := cylinderMotion A
  prop' t p hp := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change (1 - (t : ℝ)) * p.2.val = p.2.val
      rw [height_zero_on_handle A p hp, mul_zero]

local instance : CompactSpace (range (UnroundedTrace.handleMap A)) :=
  isCompact_iff_compactSpace.mp (isCompact_range (UnroundedTrace.handleMap A).continuous)

def swappedFamily : C(I × Attachment.Union (range (UnroundedTrace.handleMap A))
    (UnroundedTrace.cylinderMap A),
    Attachment.Union (range (UnroundedTrace.handleMap A)) (UnroundedTrace.cylinderMap A)) :=
  Attachment.unionFamily (range (UnroundedTrace.handleMap A)) (cylinderHandleFace A)
    (UnroundedTrace.cylinderMap A) (cylinderRelativeMotion A)
    (UnroundedTrace.closedEmbedding_cylinder A).injective (fun _ ↦ Iff.rfl)

def unionSwap : UnroundedTrace.ambientSet A ≃ₜ
    Attachment.Union (range (UnroundedTrace.handleMap A)) (UnroundedTrace.cylinderMap A) :=
  Homeomorph.setCongr (union_comm _ _)

def deformation : C(I × UnroundedTrace.ambientSet A, UnroundedTrace.ambientSet A) :=
  (unionSwap A).symm.toHomotopyEquiv.toFun.comp
    ((swappedFamily A).comp ((ContinuousMap.id I).prodMap
      (unionSwap A).toHomotopyEquiv.toFun))

theorem deformation_cylinder (t : I) (p : UnroundedTrace.Cylinder A) :
    (deformation A (t, ⟨UnroundedTrace.cylinderMap A p, Or.inl ⟨p, rfl⟩⟩)).val =
      e.heightCylinder (p.1, (1 - (t : ℝ)) * p.2.val) :=
  Attachment.unionFamily_on_handle (range (UnroundedTrace.handleMap A)) (cylinderHandleFace A)
    (UnroundedTrace.cylinderMap A) (cylinderRelativeMotion A)
    (UnroundedTrace.closedEmbedding_cylinder A).injective (fun _ ↦ Iff.rfl) t p

theorem deformation_handle (t : I) (p : UnroundedTrace.Handle A) :
    (deformation A (t, ⟨UnroundedTrace.handleMap A p, Or.inr ⟨p, rfl⟩⟩)).val =
      UnroundedTrace.handleMap A p :=
  congrArg Subtype.val (Attachment.unionFamily_fixed_lower
    (range (UnroundedTrace.handleMap A)) (cylinderHandleFace A)
    (UnroundedTrace.cylinderMap A) (cylinderRelativeMotion A)
    (UnroundedTrace.closedEmbedding_cylinder A).injective (fun _ ↦ Iff.rfl) t ⟨_, ⟨p, rfl⟩⟩)

theorem deformation_zero (x : UnroundedTrace.ambientSet A) : deformation A (0, x) = x := by
  rcases x with ⟨x, ⟨p, rfl⟩ | ⟨p, rfl⟩⟩
  · apply Subtype.ext
    rw [deformation_cylinder]
    change e.heightCylinder (p.1, (1 - (0 : ℝ)) * p.2.val) = e.heightCylinder (p.1, p.2.val)
    rw [sub_zero, one_mul]
  · exact Subtype.ext (deformation_handle A 0 p)

theorem deformation_one_mem (x : UnroundedTrace.ambientSet A) :
    (deformation A (1, x)).val ∈ bodySet A := by
  rcases x with ⟨x, ⟨p, rfl⟩ | ⟨p, rfl⟩⟩
  · rw [deformation_cylinder]
    change e.heightCylinder (p.1, (1 - (1 : ℝ)) * p.2.val) ∈ bodySet A
    rw [sub_self, zero_mul]
    exact Or.inl ⟨p.1, rfl⟩
  · rw [deformation_handle]
    exact Or.inr ⟨p, rfl⟩

def inclusion : C(bodySet A, UnroundedTrace.ambientSet A) :=
  ⟨fun x ↦ ⟨x.val, body_subset_unrounded A x.property⟩, continuous_subtype_val.subtype_mk _⟩

theorem deformation_fixed (t : I) (x : bodySet A) :
    deformation A (t, inclusion A x) = inclusion A x := by
  rcases x with ⟨x, ⟨m, rfl⟩ | ⟨p, rfl⟩⟩
  · apply Subtype.ext
    have h := deformation_cylinder A t (m, ⟨0, le_rfl, (UnroundedTrace.height_pos A).le⟩)
    exact h.trans (by
      change e.heightCylinder (m, (1 - (t : ℝ)) * 0) = e.heightCylinder (m, 0)
      rw [mul_zero])
  · exact Subtype.ext (deformation_handle A t p)

def retraction : C(UnroundedTrace.ambientSet A, bodySet A) :=
  ⟨fun x ↦ ⟨(deformation A (1, x)).val, deformation_one_mem A x⟩,
    (continuous_subtype_val.comp ((deformation A).continuous.comp
      (continuous_const.prodMk continuous_id))).subtype_mk _⟩

def bodyUnroundedHomotopyEquiv : bodySet A ≃ₕ UnroundedTrace.ambientSet A where
  toFun := inclusion A
  invFun := retraction A
  left_inv := by
    have h : (retraction A).comp (inclusion A) = ContinuousMap.id (bodySet A) := by
      apply ContinuousMap.ext
      intro x
      exact Subtype.ext (congrArg (fun z : UnroundedTrace.ambientSet A ↦ z.val)
        (deformation_fixed A 1 x))
    rw [h]
  right_inv := by
    let H : (ContinuousMap.id (UnroundedTrace.ambientSet A)).Homotopy
        ((inclusion A).comp (retraction A)) := {
      toContinuousMap := deformation A
      map_zero_left := deformation_zero A
      map_one_left := fun _ ↦ rfl }
    exact ⟨H.symm⟩

def bodyTraceHomotopyEquiv : bodySet A ≃ₕ RoundedTrace.ambientSet A :=
  (bodyUnroundedHomotopyEquiv A).trans (TraceRetraction.unroundedHomotopyEquiv A)

theorem bodyTraceHomotopyEquiv_ambient (x : bodySet A) :
    (bodyTraceHomotopyEquiv A x).val = x.val := rfl

end Wikipedia.HopfProblem.DegreeCollapse.TraceBody
