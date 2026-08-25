import StackExchange.Puzzling139335.SourceFaceBridge.ReversedSource
import StackExchange.Puzzling139335.SourceFaceBridge.Placements
import StackExchange.Puzzling139335.SourceFaceBridge.Isometries

/-!
# Recovering actual source-face endpoints from side contacts

The general upper-normal placements are the already bundled reversed-data
isometries.  Their endpoint formulas therefore need no new trigonometric
argument or angular bounds.  Injectivity recovers the four actual source
endpoints from contact of the image pieces with the two gap endpoints on
each vertical side.
-/

open Set

namespace Puzzling139335.SourceFaceBridge

noncomputable section

private theorem mem_of_image_contact {f : Plane → Plane}
    (hf : Function.Injective f) {P : Set Plane} {p q : Plane}
    (hpq : f p = q) (hq : q ∈ f '' P) : p ∈ P := by
  obtain ⟨z, hz, hzq⟩ := hq
  have hzp : z = p := hf (hzq.trans hpq.symm)
  exact hzp ▸ hz

namespace UpperFaceData

/-- The right upper-normal placement as an affine isometry. -/
def rightIsometry (d : UpperFaceData) : Plane ≃ᵃⁱ[ℝ] Plane :=
  d.reversedData.rightIsometry

/-- The proper left upper-normal placement as an affine isometry. -/
def leftProperIsometry (d : UpperFaceData) : Plane ≃ᵃⁱ[ℝ] Plane :=
  d.reversedData.leftProperIsometry

/-- The glide left upper-normal placement as an affine isometry. -/
def leftGlideIsometry (d : UpperFaceData) : Plane ≃ᵃⁱ[ℝ] Plane :=
  d.reversedData.leftGlideIsometry

/-- The left upper-normal placement with either parity. -/
def leftIsometry (d : UpperFaceData) (reversed : Bool) : Plane ≃ᵃⁱ[ℝ] Plane :=
  d.reversedData.leftIsometry reversed

@[simp] theorem coe_rightIsometry (d : UpperFaceData) : ⇑d.rightIsometry = d.right :=
  (FaceData.coe_rightIsometry d.reversedData).trans d.reversedData_right

@[simp] theorem coe_leftProperIsometry (d : UpperFaceData) :
    ⇑d.leftProperIsometry = d.leftProper :=
  (FaceData.coe_leftProperIsometry d.reversedData).trans d.reversedData_leftProper

@[simp] theorem coe_leftGlideIsometry (d : UpperFaceData) :
    ⇑d.leftGlideIsometry = d.leftGlide :=
  (FaceData.coe_leftGlideIsometry d.reversedData).trans d.reversedData_leftGlide

@[simp] theorem coe_leftIsometry (d : UpperFaceData) (reversed : Bool) :
    ⇑(d.leftIsometry reversed) = d.left reversed :=
  (FaceData.coe_leftIsometry d.reversedData reversed).trans (d.reversedData_left reversed)

theorem right_injective (d : UpperFaceData) : Function.Injective d.right := by
  have hi : Function.Injective (d.rightIsometry : Plane → Plane) :=
    d.rightIsometry.toAffineEquiv.toEquiv.injective
  simpa only [coe_rightIsometry] using hi

theorem leftProper_injective (d : UpperFaceData) : Function.Injective d.leftProper := by
  have hi : Function.Injective (d.leftProperIsometry : Plane → Plane) :=
    d.leftProperIsometry.toAffineEquiv.toEquiv.injective
  simpa only [coe_leftProperIsometry] using hi

theorem leftGlide_injective (d : UpperFaceData) : Function.Injective d.leftGlide := by
  have hi : Function.Injective (d.leftGlideIsometry : Plane → Plane) :=
    d.leftGlideIsometry.toAffineEquiv.toEquiv.injective
  simpa only [coe_leftGlideIsometry] using hi

theorem left_injective (d : UpperFaceData) (reversed : Bool) :
    Function.Injective (d.left reversed) := by
  have hi : Function.Injective (d.leftIsometry reversed : Plane → Plane) :=
    (d.leftIsometry reversed).toAffineEquiv.toEquiv.injective
  simpa only [coe_leftIsometry] using hi

theorem right_face₁minus (d : UpperFaceData) :
    d.right d.face₁minus = Schoenflies.Plane.mk 1 d.b := by
  change d.right d.face₁minus = point 1 d.b
  simpa only [reversedData_right, reversedData_face₁plus, reversedData_b] using
    d.reversedData.right_face₁plus

theorem right_face₁plus (d : UpperFaceData) :
    d.right d.face₁plus = Schoenflies.Plane.mk 1 (1 - d.b) := by
  change d.right d.face₁plus = point 1 (1 - d.b)
  simpa only [reversedData_right, reversedData_face₁minus, reversedData_b] using
    d.reversedData.right_face₁minus

theorem leftProper_face₂minus (d : UpperFaceData) :
    d.leftProper d.face₂minus = Schoenflies.Plane.mk 0 (1 - d.a) := by
  change d.leftProper d.face₂minus = point 0 (1 - d.a)
  simpa only [reversedData_leftProper, reversedData_face₂minus, reversedData_a] using
    d.reversedData.leftProper_face₂minus

theorem leftProper_face₂plus (d : UpperFaceData) :
    d.leftProper d.face₂plus = Schoenflies.Plane.mk 0 d.a := by
  change d.leftProper d.face₂plus = point 0 d.a
  simpa only [reversedData_leftProper, reversedData_face₂plus, reversedData_a] using
    d.reversedData.leftProper_face₂plus

theorem leftGlide_face₂minus (d : UpperFaceData) :
    d.leftGlide d.face₂minus = Schoenflies.Plane.mk 0 d.a := by
  change d.leftGlide d.face₂minus = point 0 d.a
  simpa only [reversedData_leftGlide, reversedData_face₂minus, reversedData_a] using
    d.reversedData.leftGlide_face₂minus

theorem leftGlide_face₂plus (d : UpperFaceData) :
    d.leftGlide d.face₂plus = Schoenflies.Plane.mk 0 (1 - d.a) := by
  change d.leftGlide d.face₂plus = point 0 (1 - d.a)
  simpa only [reversedData_leftGlide, reversedData_face₂plus, reversedData_a] using
    d.reversedData.leftGlide_face₂plus

/-- Actual contact with both endpoints of each side gap recovers all four
source-face endpoint memberships, for either left-placement parity. -/
theorem face_endpoints_mem_of_gap_contacts (d : UpperFaceData) (reversed : Bool)
    {P : Set Plane}
    (hR : Schoenflies.Plane.mk 1 d.b ∈ d.right '' P ∧
      Schoenflies.Plane.mk 1 (1 - d.b) ∈ d.right '' P)
    (hL : Schoenflies.Plane.mk 0 d.a ∈ d.left reversed '' P ∧
      Schoenflies.Plane.mk 0 (1 - d.a) ∈ d.left reversed '' P) :
    d.face₁minus ∈ P ∧ d.face₁plus ∈ P ∧ d.face₂minus ∈ P ∧ d.face₂plus ∈ P := by
  have hfirstMinus := mem_of_image_contact d.right_injective d.right_face₁minus hR.1
  have hfirstPlus := mem_of_image_contact d.right_injective d.right_face₁plus hR.2
  cases reversed
  · change Schoenflies.Plane.mk 0 d.a ∈ d.leftProper '' P ∧
      Schoenflies.Plane.mk 0 (1 - d.a) ∈ d.leftProper '' P at hL
    exact ⟨hfirstMinus, hfirstPlus,
      mem_of_image_contact d.leftProper_injective d.leftProper_face₂minus hL.2,
      mem_of_image_contact d.leftProper_injective d.leftProper_face₂plus hL.1⟩
  · change Schoenflies.Plane.mk 0 d.a ∈ d.leftGlide '' P ∧
      Schoenflies.Plane.mk 0 (1 - d.a) ∈ d.leftGlide '' P at hL
    exact ⟨hfirstMinus, hfirstPlus,
      mem_of_image_contact d.leftGlide_injective d.leftGlide_face₂minus hL.1,
      mem_of_image_contact d.leftGlide_injective d.leftGlide_face₂plus hL.2⟩

end UpperFaceData

end

end Puzzling139335.SourceFaceBridge
