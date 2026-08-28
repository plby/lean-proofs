import Wikipedia.NoExoticSixSphere.PuncturedConvexCell
import Mathlib.Analysis.Normed.Module.Convex

/-!
# The characteristic disk punctured at any interior point

Translation reduces an arbitrary interior puncture to the origin in a
translated convex disk. The resulting retraction takes values in the
original unit sphere, and its homotopy fixes that sphere pointwise.
No special position of the point chosen by cell excision is assumed.
-/

noncomputable section

open Set Metric Topology ContinuousMap
open scoped unitInterval

namespace NoExoticSixSphere.PuncturedDiskRetraction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev Space (p : E) := {x : E // x ∈ closedBall (0 : E) 1 ∧ x ≠ p}

abbrev translatedBall (p : E) : Set E := closedBall (-p) 1

theorem translatedBall_nhds (p : E) (hp : ‖p‖ < 1) : translatedBall p ∈ 𝓝 0 := by
  apply closedBall_mem_nhds_of_mem
  simpa only [mem_ball, dist_eq_norm, zero_sub, neg_neg] using hp

theorem translatedBall_bounded (p : E) : Bornology.IsVonNBounded ℝ (translatedBall p) :=
  NormedSpace.isVonNBounded_of_isBounded ℝ isBounded_closedBall

theorem sub_mem_translatedBall (p x : E) :
    x - p ∈ translatedBall p ↔ x ∈ closedBall (0 : E) 1 := by
  simp [translatedBall, mem_closedBall, dist_eq_norm]

theorem add_mem_disk (p x : E) :
    x + p ∈ closedBall (0 : E) 1 ↔ x ∈ translatedBall p := by
  simp [translatedBall, mem_closedBall, dist_eq_norm]

theorem add_mem_sphere (p x : E) :
    x + p ∈ sphere (0 : E) 1 ↔ x ∈ frontier (translatedBall p) := by
  simp [translatedBall, frontier_closedBall (-p) one_ne_zero]

theorem sub_mem_frontier (p x : E) :
    x - p ∈ frontier (translatedBall p) ↔ x ∈ sphere (0 : E) 1 := by
  rw [← add_mem_sphere, sub_add_cancel]

def translation (p : E) : Space p ≃ₜ PuncturedConvexCell.Space (translatedBall p) where
  toFun x := ⟨x.val - p, (sub_mem_translatedBall p x.val).mpr x.property.1,
    sub_ne_zero.mpr x.property.2⟩
  invFun x := ⟨x.val + p, (add_mem_disk p x.val).mpr x.property.1, by
    intro h
    apply x.property.2
    simpa only [add_sub_cancel_right, sub_self] using congrArg (fun y : E ↦ y - p) h⟩
  left_inv x := Subtype.ext (sub_add_cancel x.val p)
  right_inv x := Subtype.ext (add_sub_cancel_right x.val p)
  continuous_toFun := (continuous_subtype_val.sub continuous_const).subtype_mk _
  continuous_invFun := (continuous_subtype_val.add continuous_const).subtype_mk _

def boundaryTranslation (p : E) : frontier (translatedBall p) ≃ₜ sphere (0 : E) 1 where
  toFun x := ⟨x.val + p, (add_mem_sphere p x.val).mpr x.property⟩
  invFun x := ⟨x.val - p, (sub_mem_frontier p x.val).mpr x.property⟩
  left_inv x := Subtype.ext (add_sub_cancel_right x.val p)
  right_inv x := Subtype.ext (sub_add_cancel x.val p)
  continuous_toFun := (continuous_subtype_val.add continuous_const).subtype_mk _
  continuous_invFun := (continuous_subtype_val.sub continuous_const).subtype_mk _

def inclusion (p : E) (hp : ‖p‖ < 1) : C(sphere (0 : E) 1, Space p) :=
  ⟨fun x ↦ ⟨x.val, sphere_subset_closedBall x.property, by
    intro he
    have hn : ‖x.val‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
    exact hp.ne (he ▸ hn)⟩, continuous_subtype_val.subtype_mk _⟩

def retraction (p : E) (hp : ‖p‖ < 1) : C(Space p, sphere (0 : E) 1) :=
  (boundaryTranslation p : C(_, _)).comp
    ((PuncturedConvexCell.retraction (translatedBall p) (convex_closedBall (-p) 1)
      (translatedBall_nhds p hp) (translatedBall_bounded p)).comp (translation p : C(_, _)))

theorem retraction_val (p : E) (hp : ‖p‖ < 1) (x : Space p) :
    (retraction p hp x).val =
      PuncturedConvexCell.radial (translatedBall p) (x.val - p) + p := rfl

theorem retraction_inclusion (p : E) (hp : ‖p‖ < 1) (x : sphere (0 : E) 1) :
    retraction p hp (inclusion p hp x) = x := by
  apply Subtype.ext
  rw [retraction_val]
  change PuncturedConvexCell.radial (translatedBall p) (x.val - p) + p = x.val
  have hx : x.val - p ∈ frontier (translatedBall p) :=
    (boundaryTranslation p).symm x |>.property
  rw [PuncturedConvexCell.radial_of_mem_frontier (translatedBall p)
    (convex_closedBall (-p) 1) (translatedBall_nhds p hp) hx, sub_add_cancel]

def deformation (p : E) (hp : ‖p‖ < 1) :
    (ContinuousMap.id (Space p)).Homotopy ((inclusion p hp).comp (retraction p hp)) where
  toFun q := (translation p).symm
    (PuncturedConvexCell.deformation (translatedBall p) (convex_closedBall (-p) 1)
      isClosed_closedBall (translatedBall_nhds p hp) (translatedBall_bounded p)
        (q.1, translation p q.2))
  continuous_toFun := (translation p).symm.continuous.comp
    ((PuncturedConvexCell.deformation (translatedBall p) (convex_closedBall (-p) 1)
      isClosed_closedBall (translatedBall_nhds p hp) (translatedBall_bounded p)).continuous.comp
        (continuous_fst.prodMk ((translation p).continuous.comp continuous_snd)))
  map_zero_left x := by
    rw [ContinuousMap.Homotopy.apply_zero]
    exact (translation p).symm_apply_apply x
  map_one_left x := by
    rw [ContinuousMap.Homotopy.apply_one]
    apply Subtype.ext
    rfl

theorem deformation_fixed (p : E) (hp : ‖p‖ < 1) (t : I) (x : Space p)
    (hx : x.val ∈ sphere (0 : E) 1) : deformation p hp (t, x) = x := by
  change (translation p).symm
    (PuncturedConvexCell.deformation (translatedBall p) (convex_closedBall (-p) 1)
      isClosed_closedBall (translatedBall_nhds p hp) (translatedBall_bounded p)
        (t, translation p x)) = x
  rw [PuncturedConvexCell.deformation_fixed]
  · exact (translation p).symm_apply_apply x
  · exact ((boundaryTranslation p).symm ⟨x.val, hx⟩).property

def deformationRel (p : E) (hp : ‖p‖ < 1) :
    (ContinuousMap.id (Space p)).HomotopyRel ((inclusion p hp).comp (retraction p hp))
      (Set.range (inclusion p hp)) :=
  ⟨deformation p hp, by
    rintro t x ⟨y, rfl⟩
    exact deformation_fixed p hp t _ y.property⟩

end NoExoticSixSphere.PuncturedDiskRetraction
