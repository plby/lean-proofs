import Wikipedia.SmoothSixDPoincare.FaceAttachmentMaps

/-! # An actual attachment along an empty face is a disjoint union -/

noncomputable section

open Set Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.FaceAttachment

variable {K X : Type*} [TopologicalSpace K] [TopologicalSpace X]
  {B : Set K} (b : C(B, X)) [IsEmpty B]

def emptyFaceHomeomorph : Space b ≃ₜ X ⊕ K where
  toFun := desc b ⟨Sum.inl, continuous_inl⟩ ⟨Sum.inr, continuous_inr⟩
    (fun u => isEmptyElim u)
  invFun := Sum.elim (oldMap b) (handleMap b)
  left_inv := by
    intro z
    refine induction_on b z (P := fun w => Sum.elim (oldMap b) (handleMap b)
      (desc b ⟨Sum.inl, continuous_inl⟩ ⟨Sum.inr, continuous_inr⟩
        (fun u => isEmptyElim u) w) = w) (fun _ => rfl) (fun _ => rfl)
  right_inv := fun z => by cases z <;> rfl
  continuous_toFun := (desc b ⟨Sum.inl, continuous_inl⟩ ⟨Sum.inr, continuous_inr⟩
    (fun u => isEmptyElim u)).continuous
  continuous_invFun := continuous_sum_dom.mpr ⟨(oldMap b).continuous, (handleMap b).continuous⟩

theorem emptyFaceHomeomorph_old (x : X) :
    emptyFaceHomeomorph b (oldMap b x) = Sum.inl x := rfl

theorem emptyFaceHomeomorph_handle (k : K) :
    emptyFaceHomeomorph b (handleMap b k) = Sum.inr k := rfl

theorem emptyFaceHomeomorph_symm_old (x : X) :
    (emptyFaceHomeomorph b).symm (Sum.inl x) = oldMap b x := rfl

theorem emptyFaceHomeomorph_symm_handle (k : K) :
    (emptyFaceHomeomorph b).symm (Sum.inr k) = handleMap b k := rfl

end Wikipedia.SmoothSixDPoincare.FaceAttachment
