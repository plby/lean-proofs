import Wikipedia.NoExoticSixSphere.RoundedTraceOpenCover
import Wikipedia.NoExoticSixSphere.HandleSuperlevel

/-!
# Exact coordinates on the unchanged open handle region

Removing the cylinder removes the attaching face, so the four-disk
coordinate lies in its open unit ball. The transverse coordinate stays in
the smaller closed ball, strictly inside the available smooth product.
The actual handle embedding gives the homeomorphism onto this open window.
-/

noncomputable section

open Function Set Metric Topology TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

abbrev HandleSuperlevel :=
  {p : Vector 4 × Vector (n - 3) // 0 ≤ NoExoticSixSphere.HandleSuperlevel.level
    (UnroundedTrace.handleRadius A) p}

theorem handleSuperlevel_transverse (p : HandleSuperlevel A) :
    p.val.2 ∈ closedBall (0 : Vector (n - 3)) (UnroundedTrace.handleRadius A) :=
  (NoExoticSixSphere.HandleSuperlevel.nonneg_iff
    (UnroundedTrace.handleRadius_pos A) p.val).mp p.property

theorem handleSuperlevel_vector_mem (p : HandleSuperlevel A) :
    p.val.2 ∈ closedBall (0 : Vector (n - 3)) A.radius :=
  (closedBall_subset_closedBall (UnroundedTrace.handleRadius_lt A).le)
    (handleSuperlevel_transverse A p)

def unchangedHandleWindow : Opens (HandleSuperlevel A) where
  carrier := {p | p.val.1 ∈ ball (0 : Vector 4) 1 ∧
    A.map p.val ∉ range (UnroundedTrace.cylinderMap A) ∪ A.collarSheet '' addedParameters A}
  is_open' := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have hs : ContDiffAt ℝ ∞ A.map p.val := A.smooth p.val.1
      (ball_subset_closedBall hp.1) p.val.2 (handleSuperlevel_vector_mem A p)
    have hm : ContinuousAt (fun q : HandleSuperlevel A ↦ A.map q.val) p :=
      hs.continuousAt.comp continuous_subtype_val.continuousAt
    exact Filter.inter_mem ((isOpen_ball.preimage continuous_subtype_val.fst).mem_nhds hp.1)
      (hm (((UnroundedTrace.closedEmbedding_cylinder A).isClosed_range.union
        (isCompact_addedImage A).isClosed).isOpen_compl.mem_nhds hp.2))

def handleWindowRestriction : C(unchangedHandleWindow A, UnroundedTrace.Handle A) :=
  ⟨fun p ↦ (⟨p.val.val.1, ball_subset_closedBall p.property.1⟩,
      ⟨p.val.val.2, handleSuperlevel_transverse A p.val⟩),
    (((continuous_subtype_val.comp continuous_subtype_val).fst).subtype_mk _).prodMk
      (((continuous_subtype_val.comp continuous_subtype_val).snd).subtype_mk _)⟩

theorem isEmbedding_handleWindowRestriction : IsEmbedding (handleWindowRestriction A) := by
  apply IsEmbedding.of_comp (handleWindowRestriction A).continuous
    (continuous_subtype_val.prodMap continuous_subtype_val)
  exact IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal

theorem handleWindow_mem (p : unchangedHandleWindow A) : A.map p.val.val ∈ ambientSet A :=
  unrounded_subset A (Or.inr ⟨handleWindowRestriction A p, rfl⟩)

def unchangedHandleMap : C(unchangedHandleWindow A, ambientSet A) :=
  ⟨fun p ↦ ⟨A.map p.val.val, handleWindow_mem A p⟩,
    ((UnroundedTrace.handleMap A).continuous.comp
      (handleWindowRestriction A).continuous).subtype_mk _⟩

theorem isEmbedding_unchangedHandleMap : IsEmbedding (unchangedHandleMap A) := by
  have he : IsEmbedding (fun p : unchangedHandleWindow A ↦ A.map p.val.val) :=
    (UnroundedTrace.closedEmbedding_handle A).isEmbedding.comp
      (isEmbedding_handleWindowRestriction A)
  exact he.codRestrict (ambientSet A) (handleWindow_mem A)

theorem handleOnly_core_interior (p : UnroundedTrace.Handle A)
    (hp : UnroundedTrace.handleMap A p ∉ range (UnroundedTrace.cylinderMap A)) :
    p.1.val ∈ ball (0 : Vector 4) 1 := by
  have hnot : p ∉ UnroundedTrace.attachingFace A :=
    fun h ↦ hp ((UnroundedTrace.handle_mem_cylinder_iff A p).mpr h)
  have hle : ‖p.1.val‖ ≤ 1 := by
    simpa only [mem_closedBall, dist_zero_right] using p.1.property
  have hne : ‖p.1.val‖ ≠ 1 := by
    intro h
    apply hnot
    change p.1.val ∈ sphere (0 : Vector 4) 1
    simpa only [mem_sphere, dist_zero_right] using h
  simpa only [mem_ball, dist_zero_right] using lt_of_le_of_ne hle hne

theorem range_unchangedHandleMap : range (unchangedHandleMap A) =
    (handleOnlyPart A : Set (ambientSet A)) := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    exact p.property.2
  · intro hy
    obtain ⟨q, hq⟩ := handleOnlyPart_mem A ⟨y, hy⟩
    have hx := handleOnly_core_interior A q (fun hc ↦ hy (Or.inl (hq ▸ hc)))
    let p : HandleSuperlevel A := ⟨(q.1.val, q.2.val),
      (NoExoticSixSphere.HandleSuperlevel.nonneg_iff
        (UnroundedTrace.handleRadius_pos A) _).mpr q.2.property⟩
    have hp : p ∈ unchangedHandleWindow A := by
      refine ⟨hx, ?_⟩
      change UnroundedTrace.handleMap A q ∉ _
      rw [hq]
      exact hy
    exact ⟨⟨p, hp⟩, Subtype.ext hq⟩

def unchangedHandleHomeomorph : handleOnlyPart A ≃ₜ unchangedHandleWindow A :=
  ((isEmbedding_unchangedHandleMap A).toHomeomorph.trans
    (Homeomorph.setCongr (range_unchangedHandleMap A))).symm

theorem unchangedHandleHomeomorph_ambient (p : handleOnlyPart A) :
    A.map (unchangedHandleHomeomorph A p).val.val = p.val.val :=
  congrArg (fun y : handleOnlyPart A ↦ y.val.val)
    ((unchangedHandleHomeomorph A).symm_apply_apply p)

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
