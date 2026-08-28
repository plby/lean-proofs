import Wikipedia.SmoothSixDPoincare.FaceAttachmentMaps

/-!
# Interchange two whole attachments whose face maps land in the same old space

The iterated quotients in the two orders are homeomorphic. The homeomorphism
fixes the original old-space point and every coordinate of both entire
attached pieces. The statement uses the actual face maps, not just equivalent
attaching homotopy classes.
-/

noncomputable section

open Set ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.FaceAttachment

variable {K L X : Type*} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
  {B₁ : Set K} {B₂ : Set L} (b₁ : C(B₁, X)) (b₂ : C(B₂, X))

def swapOldMap : C(Space b₁, Space ((oldMap b₂).comp b₁)) :=
  desc b₁ ((oldMap ((oldMap b₂).comp b₁)).comp (oldMap b₂))
    (handleMap ((oldMap b₂).comp b₁)) (fun u => face_identification _ u)

def swapMap : C(Space ((oldMap b₁).comp b₂), Space ((oldMap b₂).comp b₁)) :=
  desc ((oldMap b₁).comp b₂) (swapOldMap b₁ b₂)
    ((oldMap ((oldMap b₂).comp b₁)).comp (handleMap b₂))
    (fun u => congrArg (oldMap ((oldMap b₂).comp b₁)) (face_identification b₂ u))

theorem swapMap_old_old (x : X) :
    swapMap b₁ b₂ (oldMap ((oldMap b₁).comp b₂) (oldMap b₁ x)) =
      oldMap ((oldMap b₂).comp b₁) (oldMap b₂ x) := rfl

theorem swapMap_old_handle (k : K) :
    swapMap b₁ b₂ (oldMap ((oldMap b₁).comp b₂) (handleMap b₁ k)) =
      handleMap ((oldMap b₂).comp b₁) k := rfl

theorem swapMap_handle (l : L) :
    swapMap b₁ b₂ (handleMap ((oldMap b₁).comp b₂) l) =
      oldMap ((oldMap b₂).comp b₁) (handleMap b₂ l) := rfl

theorem swapMap_involutive (z : Space ((oldMap b₁).comp b₂)) :
    swapMap b₂ b₁ (swapMap b₁ b₂ z) = z := by
  refine induction_on _ z (P := fun w => swapMap b₂ b₁ (swapMap b₁ b₂ w) = w) ?_ ?_
  · intro q
    refine induction_on _ q (P := fun w =>
      swapMap b₂ b₁ (swapMap b₁ b₂ (oldMap ((oldMap b₁).comp b₂) w)) =
        oldMap ((oldMap b₁).comp b₂) w) ?_ ?_
    · intro x
      rfl
    · intro k
      rfl
  · intro l
    rfl

def commute : Space ((oldMap b₁).comp b₂) ≃ₜ Space ((oldMap b₂).comp b₁) where
  toFun := swapMap b₁ b₂
  invFun := swapMap b₂ b₁
  left_inv := swapMap_involutive b₁ b₂
  right_inv := swapMap_involutive b₂ b₁
  continuous_toFun := (swapMap b₁ b₂).continuous
  continuous_invFun := (swapMap b₂ b₁).continuous

theorem commute_old (x : X) :
    commute b₁ b₂ (oldMap ((oldMap b₁).comp b₂) (oldMap b₁ x)) =
      oldMap ((oldMap b₂).comp b₁) (oldMap b₂ x) := rfl

theorem commute_first (k : K) :
    commute b₁ b₂ (oldMap ((oldMap b₁).comp b₂) (handleMap b₁ k)) =
      handleMap ((oldMap b₂).comp b₁) k := rfl

theorem commute_second (l : L) :
    commute b₁ b₂ (handleMap ((oldMap b₁).comp b₂) l) =
      oldMap ((oldMap b₂).comp b₁) (handleMap b₂ l) := rfl

end Wikipedia.SmoothSixDPoincare.FaceAttachment
