import Wikipedia.SmoothSixDPoincare.FaceAttachmentExact
import Wikipedia.SmoothSixDPoincare.FaceAttachmentCommute

/-!
# Exact designated boundary updates inside whole-piece attachment quotients

An update removes the specified old face interior and adds the specified
new face of the whole piece. For disjoint attaching regions, the actual
whole-piece interchange preserves these boundary sets and all point maps.
-/

noncomputable section

open Set Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.FaceAttachment

variable {K L X : Type*} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
  {B : Set K} {C : Set L} (b : C(B, X)) (c : C(C, X))

def updateBoundary (S U : Set X) (V : Set K) : Set (Space b) :=
  oldMap b '' (S \ U) ∪ handleMap b '' V

theorem oldImage_disjoint_handleImage (hb : Injective b) (U : Set X) (V : Set K)
    (hU : Disjoint U (range b)) : Disjoint (oldMap b '' U) (handleMap b '' V) := by
  rw [disjoint_left]
  rintro z ⟨x, hx, rfl⟩ ⟨k, _, hk⟩
  obtain ⟨u, hu, -⟩ := (oldMap_eq_handleMap b hb x k).mp hk.symm
  exact disjoint_left.mp hU hx ⟨u, hu⟩

theorem updateBoundary_sdiff_oldImage (hb : Injective b) (S U W : Set X) (V : Set K)
    (hW : Disjoint W (range b)) :
    updateBoundary b S U V \ (oldMap b '' W) =
      oldMap b '' (S \ (U ∪ W)) ∪ handleMap b '' V := by
  have hi : Injective (oldMap b) := fun x y h => (oldMap_eq_oldMap b hb x y).mp h
  have hd := (oldImage_disjoint_handleImage b hb W V hW).symm
  ext z
  constructor
  · rintro ⟨hz, hw⟩
    rcases hz with ⟨x, ⟨hx, hu⟩, rfl⟩ | hv
    · exact Or.inl ⟨x, ⟨hx, fun h => h.elim hu (fun hxw => hw ⟨x, hxw, rfl⟩)⟩, rfl⟩
    · exact Or.inr hv
  · rintro (⟨x, ⟨hx, hUW⟩, rfl⟩ | hv)
    · refine ⟨Or.inl ⟨x, ⟨hx, fun hu => hUW (Or.inl hu)⟩, rfl⟩, ?_⟩
      rintro ⟨y, hy, he⟩
      have hyx : y = x := hi he
      exact hUW (Or.inr (hyx ▸ hy))
    · exact ⟨Or.inr hv, fun hw => disjoint_left.mp hd hv hw⟩

theorem updateBoundary_twice (hb : Injective b)
    (S U W : Set X) (V : Set K) (Z : Set L) (hW : Disjoint W (range b)) :
    updateBoundary ((oldMap b).comp c) (updateBoundary b S U V) (oldMap b '' W) Z =
      (oldMap ((oldMap b).comp c) ∘ oldMap b) '' (S \ (U ∪ W)) ∪
        (oldMap ((oldMap b).comp c) ∘ handleMap b) '' V ∪
          handleMap ((oldMap b).comp c) '' Z := by
  unfold updateBoundary at ⊢
  rw [show (oldMap b '' (S \ U) ∪ handleMap b '' V) \ (oldMap b '' W) =
      oldMap b '' (S \ (U ∪ W)) ∪ handleMap b '' V from
        updateBoundary_sdiff_oldImage b hb S U W V hW]
  rw [image_union, image_image, image_image]
  rfl

theorem commute_updateBoundary (hb : Injective b) (hc : Injective c)
    (S U W : Set X) (V : Set K) (Z : Set L)
    (hU : Disjoint U (range c)) (hW : Disjoint W (range b)) :
    commute b c ''
      updateBoundary ((oldMap b).comp c) (updateBoundary b S U V) (oldMap b '' W) Z =
    updateBoundary ((oldMap c).comp b) (updateBoundary c S W Z) (oldMap c '' U) V := by
  rw [updateBoundary_twice b c hb S U W V Z hW,
    updateBoundary_twice c b hc S W U Z V hU]
  rw [image_union, image_union, image_image, image_image, image_image]
  change (oldMap ((oldMap c).comp b) ∘ oldMap c) '' (S \ (U ∪ W)) ∪
      handleMap ((oldMap c).comp b) '' V ∪
        (oldMap ((oldMap c).comp b) ∘ handleMap c) '' Z = _
  rw [union_comm U W]
  exact union_right_comm _ _ _

end Wikipedia.SmoothSixDPoincare.FaceAttachment
