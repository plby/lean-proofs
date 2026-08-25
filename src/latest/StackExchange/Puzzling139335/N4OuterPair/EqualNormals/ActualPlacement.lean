import StackExchange.Puzzling139335.N4OuterPair.EqualNormals.SourceCoordinates
import StackExchange.Puzzling139335.N4OuterPair.SourceEndpoints
import StackExchange.Puzzling139335.N4OuterPair.PlacementFrames

/-!
# Transporting the equal-normal relative map to the actual middle pieces

Source extraction permits a common horizontal reflection and either order
of the two middle labels.  The relative congruence is conjugated by that
same reflection, so the image statement below is about the actual pieces.
-/

open Set

namespace Puzzling139335.N4OuterPair.EqualNormals

open SourceFaceBridge

noncomputable section

def modelRelative (d : UpperFaceData) (reversed : Bool) : Plane ≃ᵃⁱ[ℝ] Plane :=
  d.rightIsometry.symm.trans (d.leftIsometry reversed)

theorem modelRelative_apply_right (d : UpperFaceData) (reversed : Bool) (p : Plane) :
    modelRelative d reversed (d.right p) = d.left reversed p := by
  rw [← d.coe_rightIsometry]
  change (d.leftIsometry reversed) (d.rightIsometry.symm (d.rightIsometry p)) = _
  rw [d.rightIsometry.symm_apply_apply]
  exact congrFun (d.coe_leftIsometry reversed) p

def actualRelative (d : UpperFaceData) (reversed σ : Bool) : Plane ≃ᵃⁱ[ℝ] Plane :=
  (postReflect σ).trans ((modelRelative d reversed).trans (postReflect σ))

theorem actualRelative_apply (d : UpperFaceData) (reversed σ : Bool) (p : Plane) :
    actualRelative d reversed σ p =
      postReflect σ (modelRelative d reversed (postReflect σ p)) := rfl

theorem actualRelative_apply_reflected_right
    (d : UpperFaceData) (reversed σ : Bool) (p : Plane) :
    actualRelative d reversed σ (postReflect σ (d.right p)) =
      postReflect σ (d.left reversed p) := by
  rw [actualRelative_apply, postReflect_involutive, modelRelative_apply_right]

theorem actualRelative_image (d : UpperFaceData) (reversed σ : Bool)
    {P R T : Set Plane}
    (hR : d.right '' P = postReflect σ '' R)
    (hT : d.left reversed '' P = postReflect σ '' T) :
    actualRelative d reversed σ '' R = T := by
  have hR' : postReflect σ '' (d.right '' P) = R := by
    rw [hR, image_image]
    simp only [postReflect_involutive, image_id']
  have hT' : postReflect σ '' (d.left reversed '' P) = T := by
    rw [hT, image_image]
    simp only [postReflect_involutive, image_id']
  calc
    actualRelative d reversed σ '' R =
        actualRelative d reversed σ '' (postReflect σ '' (d.right '' P)) := by rw [hR']
    _ = (fun p => actualRelative d reversed σ (postReflect σ (d.right p))) '' P := by
      simp only [image_image]
    _ = (fun p => postReflect σ (d.left reversed p)) '' P := by
      congr 1
      funext p
      exact actualRelative_apply_reflected_right d reversed σ p
    _ = postReflect σ '' (d.left reversed '' P) := by rw [image_image]
    _ = T := hT'

variable {d : UpperFaceData} {P : Set Plane}

theorem modelRelative_proper_coordinates
    (h : UpperSupportedSource d false P) (heq : d.φ = d.ψ) (x : Plane) :
    modelRelative d false x 0 = 1 - x 0 ∧
      modelRelative d false x 1 = 1 - x 1 +
        (d.tangent₁ d.M₂ - d.tangent₁ d.M₁) := by
  obtain ⟨p, hp⟩ := d.rightIsometry.surjective x
  have hp' : d.right p = x := by simpa only [d.coe_rightIsometry] using hp
  subst x
  simpa only [d.coe_rightIsometry, modelRelative_apply_right, UpperFaceData.left,
    Bool.false_eq_true, ↓reduceIte] using
    h.leftProper_coordinates_of_equal_normals heq p

theorem modelRelative_glide_coordinates
    (h : UpperSupportedSource d true P) (heq : d.φ = d.ψ) (x : Plane) :
    modelRelative d true x 0 = 1 - x 0 ∧
      modelRelative d true x 1 = x 1 +
        (d.tangent₁ d.M₁ - d.tangent₁ d.M₂) := by
  obtain ⟨p, hp⟩ := d.rightIsometry.surjective x
  have hp' : d.right p = x := by simpa only [d.coe_rightIsometry] using hp
  subst x
  simpa only [d.coe_rightIsometry, modelRelative_apply_right, UpperFaceData.left,
    ↓reduceIte] using
    h.leftGlide_coordinates_of_equal_normals heq p

/-- The common normalization reflection changes only the sign of the
vertical offset in the proper relative map. -/
theorem actualRelative_proper_coordinates
    (h : UpperSupportedSource d false P) (heq : d.φ = d.ψ) (σ : Bool) :
    ∃ δ : ℝ, ∀ x : Plane, actualRelative d false σ x 0 = 1 - x 0 ∧
      actualRelative d false σ x 1 = 1 - x 1 + δ := by
  let δ := d.tangent₁ d.M₂ - d.tangent₁ d.M₁
  refine ⟨if σ then -δ else δ, ?_⟩
  intro x
  have hxy := modelRelative_proper_coordinates h heq (postReflect σ x)
  rw [actualRelative_apply]
  constructor
  · simpa only [postReflect_apply_zero] using hxy.1
  · cases σ
    · simpa only [postReflect_apply_one, Bool.false_eq_true, if_false] using hxy.2
    · simp only [postReflect_apply_one, ↓reduceIte] at hxy ⊢
      change 1 - modelRelative d false (postReflect true x) 1 = 1 - x 1 + -δ
      linarith only [hxy.2]

/-- The common normalization reflection changes only the sign of the
vertical glide in the reversed relative map. -/
theorem actualRelative_glide_coordinates
    (h : UpperSupportedSource d true P) (heq : d.φ = d.ψ) (σ : Bool) :
    ∃ δ : ℝ, ∀ x : Plane, actualRelative d true σ x 0 = 1 - x 0 ∧
      actualRelative d true σ x 1 = x 1 + δ := by
  let δ := d.tangent₁ d.M₁ - d.tangent₁ d.M₂
  refine ⟨if σ then -δ else δ, ?_⟩
  intro x
  have hxy := modelRelative_glide_coordinates h heq (postReflect σ x)
  rw [actualRelative_apply]
  constructor
  · simpa only [postReflect_apply_zero] using hxy.1
  · cases σ
    · simpa only [postReflect_apply_one, Bool.false_eq_true, if_false] using hxy.2
    · simp only [postReflect_apply_one, ↓reduceIte] at hxy ⊢
      change 1 - modelRelative d true (postReflect true x) 1 = x 1 + -δ
      linarith only [hxy.2]

end

end Puzzling139335.N4OuterPair.EqualNormals
