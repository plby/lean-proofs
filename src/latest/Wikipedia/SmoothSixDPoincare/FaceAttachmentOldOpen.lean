import Wikipedia.SmoothSixDPoincare.FaceAttachmentExact

/-! # Open old-body sets disjoint from the attaching face remain open -/

noncomputable section

open Set Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.FaceAttachment

variable {K X : Type*} [TopologicalSpace K] [TopologicalSpace X]
  {B : Set K} (b : C(B, X)) (hb : Injective b)

include hb in
theorem old_image_open (s : Set X) (hs : IsOpen s) (havoid : Disjoint s (range b)) :
    IsOpen (oldMap b '' s) := by
  have heq : Quot.mk (Rel b) ⁻¹' (oldMap b '' s) = Sum.inl '' s := by
    ext q
    cases q with
    | inl x =>
        constructor
        · rintro ⟨y, hy, h⟩
          have hyx : y = x := (oldMap_eq_oldMap b hb y x).mp h
          exact ⟨y, hy, congrArg Sum.inl hyx⟩
        · rintro ⟨y, hy, h⟩
          cases Sum.inl.inj h
          exact ⟨x, hy, rfl⟩
    | inr k =>
        constructor
        · rintro ⟨x, hx, h⟩
          obtain ⟨u, hu, -⟩ := (oldMap_eq_handleMap b hb x k).mp h
          exact (Set.disjoint_left.mp havoid hx ⟨u, hu⟩).elim
        · rintro ⟨x, _, h⟩
          cases h
  apply isQuotientMap_quot_mk.isOpen_preimage.mp
  rw [heq]
  exact isOpenMap_inl _ hs

end Wikipedia.SmoothSixDPoincare.FaceAttachment
