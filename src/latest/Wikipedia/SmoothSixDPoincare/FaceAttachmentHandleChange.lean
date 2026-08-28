import Wikipedia.SmoothSixDPoincare.FaceAttachment

/-!
# Reparametrize a whole attached piece while fixing its prescribed face

The old space is unchanged pointwise. A homeomorphism of the entire piece
fixed on the attaching face descends to a homeomorphism of the actual
attachment quotient with exactly that whole-piece point map.
-/

noncomputable section

open Set Function ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.FaceAttachment

variable {K X : Type*} [TopologicalSpace K] [TopologicalSpace X]
  {B : Set K} (b : C(B, X)) (q : K ≃ₜ K) (hfix : ∀ k ∈ B, q k = k)

include hfix in
theorem handleChange_mem_iff (k : K) : q k ∈ B ↔ k ∈ B := by
  constructor
  · intro h
    have he : q k = k := q.injective (hfix (q k) h)
    exact he ▸ h
  · intro h
    exact (hfix k h).symm ▸ h

def handleChange : Space b ≃ₜ Space b := by
  apply Homeomorph.Quot.congr ((Homeomorph.refl X).sumCongr q)
  rintro (x | k) (x' | k')
  · exact Iff.rfl
  · change (∃ hk : k' ∈ B, x = b ⟨k', hk⟩) ↔
      ∃ hk : q k' ∈ B, x = b ⟨q k', hk⟩
    constructor
    · rintro ⟨hk, hx⟩
      have he := hfix k' hk
      exact ⟨(handleChange_mem_iff q hfix k').mpr hk,
        hx.trans (congrArg b (Subtype.ext he.symm))⟩
    · rintro ⟨hk, hx⟩
      have hk' := (handleChange_mem_iff q hfix k').mp hk
      exact ⟨hk', hx.trans (congrArg b (Subtype.ext (hfix k' hk')))⟩
  · exact Iff.rfl
  · exact Iff.rfl

theorem handleChange_old (x : X) : handleChange b q hfix (oldMap b x) = oldMap b x := rfl

theorem handleChange_handle (k : K) :
    handleChange b q hfix (handleMap b k) = handleMap b (q k) := rfl

theorem handleChange_symm_old (x : X) :
    (handleChange b q hfix).symm (oldMap b x) = oldMap b x := rfl

theorem handleChange_symm_handle (k : K) :
    (handleChange b q hfix).symm (handleMap b k) = handleMap b (q.symm k) := rfl

end Wikipedia.SmoothSixDPoincare.FaceAttachment
