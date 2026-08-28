import Wikipedia.SmoothSixDPoincare.FaceAttachment
import Wikipedia.SmoothSixDPoincare.ClosedAttachment

/-!
# The actual embedded attachment equals its face-map quotient

The relation is unchanged: precisely the designated face is identified with
its original image in the old subspace. The identity on both pieces gives
the quotient homeomorphism, retaining every point of each parametrization.
-/

noncomputable section

open Set ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.ClosedAttachment

variable {K M : Type*} [TopologicalSpace K] [TopologicalSpace M]
  (A : Set M) (B : Set K) (h : C(K, M)) (hface : ∀ k ∈ B, h k ∈ A)

def faceMap : C(B, A) where
  toFun k := ⟨h k.val, hface k.val k.property⟩
  continuous_toFun := (h.continuous.comp continuous_subtype_val).subtype_mk _

def faceQuotientHomeomorph : FaceAttachment.Space (faceMap A B h hface) ≃ₜ Space A B h := by
  apply Homeomorph.Quot.congr (Homeomorph.refl (A ⊕ K))
  intro x y
  cases x with
  | inl x =>
      cases y with
      | inl y => exact Iff.rfl
      | inr k =>
          change (∃ hk : k ∈ B, x = faceMap A B h hface ⟨k, hk⟩) ↔
            k ∈ B ∧ x.val = h k
          constructor
          · rintro ⟨hk, hx⟩
            exact ⟨hk, congrArg Subtype.val hx⟩
          · rintro ⟨hk, hx⟩
            exact ⟨hk, Subtype.ext hx⟩
  | inr k => cases y <;> exact Iff.rfl

theorem faceQuotientHomeomorph_old (x : A) :
    faceQuotientHomeomorph A B h hface (FaceAttachment.oldMap (faceMap A B h hface) x) =
      Quot.mk _ (Sum.inl x) := rfl

theorem faceQuotientHomeomorph_handle (k : K) :
    faceQuotientHomeomorph A B h hface (FaceAttachment.handleMap (faceMap A B h hface) k) =
      Quot.mk _ (Sum.inr k) := rfl

end Wikipedia.SmoothSixDPoincare.ClosedAttachment
