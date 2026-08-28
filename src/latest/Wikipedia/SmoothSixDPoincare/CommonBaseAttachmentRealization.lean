import Wikipedia.SmoothSixDPoincare.FaceAttachmentCommute

/-!
# Realize and interchange two original quotients through an exact common-base factorization

The second face must factor through the retained first quotient realization
and its original old-space map. This actual equality constructs both ordered
quotient realizations, preserving the maps of the whole old space and both
whole attached pieces into the original final space.
-/

noncomputable section

open Set ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.FaceAttachment

section Congr

variable {K X : Type*} [TopologicalSpace K] [TopologicalSpace X] {B : Set K}
  {b c : C(B, X)}

def congrFaceMap (h : b = c) : Space b ≃ₜ Space c := by
  subst c
  exact Homeomorph.refl _

theorem congrFaceMap_old (h : b = c) (x : X) :
    congrFaceMap h (oldMap b x) = oldMap c x := by
  subst c
  rfl

theorem congrFaceMap_handle (h : b = c) (k : K) :
    congrFaceMap h (handleMap b k) = handleMap c k := by
  subst c
  rfl

end Congr

variable {K L X Y Z : Type*} [TopologicalSpace K] [TopologicalSpace L]
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {B₁ : Set K} {B₂ : Set L} (b₁ : C(B₁, X)) (b₂ : C(B₂, X)) (c : C(B₂, Y))
  (r₁ : Space b₁ ≃ₜ Y) (r₂ : Space c ≃ₜ Z)
  (h : r₁.toHomotopyEquiv.toFun.comp ((oldMap b₁).comp b₂) = c)

def commonBaseRealization : Space ((oldMap b₁).comp b₂) ≃ₜ Z :=
  (baseCongr ((oldMap b₁).comp b₂) r₁).trans ((congrFaceMap h).trans r₂)

theorem commonBaseRealization_old (x : Space b₁) :
    commonBaseRealization b₁ b₂ c r₁ r₂ h (oldMap ((oldMap b₁).comp b₂) x) =
      r₂ (oldMap c (r₁ x)) := by
  change r₂ (congrFaceMap h (baseCongr ((oldMap b₁).comp b₂) r₁
    (oldMap ((oldMap b₁).comp b₂) x))) = _
  rw [baseCongr_old, congrFaceMap_old]

theorem commonBaseRealization_handle (l : L) :
    commonBaseRealization b₁ b₂ c r₁ r₂ h (handleMap ((oldMap b₁).comp b₂) l) =
      r₂ (handleMap c l) := by
  change r₂ (congrFaceMap h (baseCongr ((oldMap b₁).comp b₂) r₁
    (handleMap ((oldMap b₁).comp b₂) l))) = _
  rw [baseCongr_handle, congrFaceMap_handle]

def interchangedRealization : Space ((oldMap b₂).comp b₁) ≃ₜ Z :=
  (commute b₁ b₂).symm.trans (commonBaseRealization b₁ b₂ c r₁ r₂ h)

theorem interchangedRealization_old (x : X) :
    interchangedRealization b₁ b₂ c r₁ r₂ h
        (oldMap ((oldMap b₂).comp b₁) (oldMap b₂ x)) =
      r₂ (oldMap c (r₁ (oldMap b₁ x))) := by
  change commonBaseRealization b₁ b₂ c r₁ r₂ h
    (commute b₂ b₁ (oldMap ((oldMap b₂).comp b₁) (oldMap b₂ x))) = _
  rw [commute_old, commonBaseRealization_old]

theorem interchangedRealization_first (k : K) :
    interchangedRealization b₁ b₂ c r₁ r₂ h (handleMap ((oldMap b₂).comp b₁) k) =
      r₂ (oldMap c (r₁ (handleMap b₁ k))) := by
  change commonBaseRealization b₁ b₂ c r₁ r₂ h
    (commute b₂ b₁ (handleMap ((oldMap b₂).comp b₁) k)) = _
  rw [commute_second, commonBaseRealization_old]

theorem interchangedRealization_second (l : L) :
    interchangedRealization b₁ b₂ c r₁ r₂ h
        (oldMap ((oldMap b₂).comp b₁) (handleMap b₂ l)) =
      r₂ (handleMap c l) := by
  change commonBaseRealization b₁ b₂ c r₁ r₂ h
    (commute b₂ b₁ (oldMap ((oldMap b₂).comp b₁) (handleMap b₂ l))) = _
  rw [commute_first, commonBaseRealization_handle]

end Wikipedia.SmoothSixDPoincare.FaceAttachment
