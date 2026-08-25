import StackExchange.Puzzling139335.SourceFaceBridge.UpperDefs

/-!
# The reversed source as a case of general upper support normals

When the first normal points left and the second points right, the angle
change `α = π - φ`, `β = ψ` gives the earlier reversed-source coordinates.
The placement functions agree exactly.  Only the two labels on the first
support face are exchanged; all actual source and image sets stay fixed.
-/

open Set

namespace Puzzling139335.SourceFaceBridge

noncomputable section

namespace UpperFaceData

/-- Convert the upper-normal angles to the reversed-source convention. -/
def reversedData (d : UpperFaceData) : FaceData where
  α := Real.pi - d.φ
  β := d.ψ
  a := d.a
  b := d.b
  M₁ := d.M₁
  M₂ := d.M₂

@[simp] theorem reversedData_alpha (d : UpperFaceData) :
    d.reversedData.α = Real.pi - d.φ := rfl

@[simp] theorem reversedData_beta (d : UpperFaceData) : d.reversedData.β = d.ψ := rfl
@[simp] theorem reversedData_a (d : UpperFaceData) : d.reversedData.a = d.a := rfl
@[simp] theorem reversedData_b (d : UpperFaceData) : d.reversedData.b = d.b := rfl
@[simp] theorem reversedData_M₁ (d : UpperFaceData) : d.reversedData.M₁ = d.M₁ := rfl
@[simp] theorem reversedData_M₂ (d : UpperFaceData) : d.reversedData.M₂ = d.M₂ := rfl

@[simp] theorem reversedData_normal₁ (d : UpperFaceData) :
    d.reversedData.normal₁ = d.normal₁ := by
  funext p
  simp [FaceData.normal₁, reversedData, normal₁, Real.cos_pi_sub, Real.sin_pi_sub]

@[simp] theorem reversedData_tangent₁ (d : UpperFaceData) :
    d.reversedData.tangent₁ = d.tangent₁ := by
  funext p
  simp [FaceData.tangent₁, reversedData, tangent₁, Real.cos_pi_sub, Real.sin_pi_sub]

@[simp] theorem reversedData_normal₂ (d : UpperFaceData) :
    d.reversedData.normal₂ = d.normal₂ := rfl

@[simp] theorem reversedData_tangent₂ (d : UpperFaceData) :
    d.reversedData.tangent₂ = d.tangent₂ := rfl

@[simp] theorem reversedData_right (d : UpperFaceData) :
    d.reversedData.right = d.right := by
  funext p
  simp [FaceData.right, right]

@[simp] theorem reversedData_leftProper (d : UpperFaceData) :
    d.reversedData.leftProper = d.leftProper := rfl

@[simp] theorem reversedData_leftGlide (d : UpperFaceData) :
    d.reversedData.leftGlide = d.leftGlide := rfl

@[simp] theorem reversedData_left (d : UpperFaceData) (reversed : Bool) :
    d.reversedData.left reversed = d.left reversed := rfl

@[simp] theorem reversedData_face₁minus (d : UpperFaceData) :
    d.reversedData.face₁minus = d.face₁plus := by
  simp [FaceData.face₁minus, reversedData, face₁plus, Real.cos_pi_sub, Real.sin_pi_sub]

@[simp] theorem reversedData_face₁plus (d : UpperFaceData) :
    d.reversedData.face₁plus = d.face₁minus := by
  simp only [FaceData.face₁plus, reversedData, face₁minus,
    Real.cos_pi_sub, Real.sin_pi_sub]
  simp [sub_eq_add_neg]

@[simp] theorem reversedData_face₂minus (d : UpperFaceData) :
    d.reversedData.face₂minus = d.face₂minus := rfl

@[simp] theorem reversedData_face₂plus (d : UpperFaceData) :
    d.reversedData.face₂plus = d.face₂plus := rfl

end UpperFaceData

namespace UpperSupportedSource

/-- The general actual-source hypotheses imply the old reversed-source
hypotheses when the two horizontal normal signs have the reversed order. -/
theorem toReversedSource {d : UpperFaceData} {reversed : Bool} {P : Set Plane}
    (h : UpperSupportedSource d reversed P)
    (hφ : Real.pi / 2 < d.φ) (hψ : d.ψ < Real.pi / 2) :
    SupportedSource d.reversedData reversed P where
  alpha_pos := sub_pos.mpr h.phi_lt_pi
  alpha_lt_half_pi := by
    change Real.pi - d.φ < Real.pi / 2
    linarith only [hφ]
  beta_pos := h.psi_pos
  beta_lt_half_pi := hψ
  a_pos := h.a_pos
  a_lt_half := h.a_lt_half
  b_pos := h.b_pos
  b_lt_half := h.b_lt_half
  source_subset := h.source_subset
  base_mem := h.base_mem
  left_top_mem := h.left_top_mem
  right_top_mem := h.right_top_mem
  face₁minus_mem := by simpa only [UpperFaceData.reversedData_face₁minus] using h.face₁plus_mem
  face₁plus_mem := by simpa only [UpperFaceData.reversedData_face₁plus] using h.face₁minus_mem
  face₂minus_mem := h.face₂minus_mem
  face₂plus_mem := h.face₂plus_mem
  right_fits := by simpa only [UpperFaceData.reversedData_right] using h.right_fits
  left_fits := h.left_fits

end UpperSupportedSource

end

end Puzzling139335.SourceFaceBridge
