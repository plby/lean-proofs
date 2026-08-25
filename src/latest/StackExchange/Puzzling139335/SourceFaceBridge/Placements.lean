import StackExchange.Puzzling139335.SourceFaceBridge.Defs

/-!
# Actual base and support-face endpoint images

The formulas concern the explicit plane maps, not just a scalar relaxation.
The source base is an actual segment in the supported-source hypotheses.
Only endpoint contact, not an unassumed full-face membership assertion, is
deduced from the four face-endpoint hypotheses.
-/

open Set

namespace Puzzling139335.SourceFaceBridge

noncomputable section

def halfTurn (p : Plane) : Plane := point (1 - p 0) (1 - p 1)

def verticalReflection (p : Plane) : Plane := point (1 - p 0) (p 1)

namespace FaceData

theorem right_base (d : FaceData) (t : ℝ) :
    d.right (point t 0) =
      point (1 - d.scalarData.u - t * d.scalarData.c)
        (1 / 2 - d.scalarData.v - t * d.scalarData.s) := by
  apply point_ext <;>
    simp [right, normal₁, tangent₁, scalarData] <;> ring

theorem leftProper_base (d : FaceData) (t : ℝ) :
    d.leftProper (point t 0) =
      point (d.scalarData.w - t * d.scalarData.d)
        (1 / 2 + d.scalarData.z + t * d.scalarData.q) := by
  apply point_ext <;>
    simp [leftProper, normal₂, tangent₂, scalarData] <;> ring

theorem leftGlide_base (d : FaceData) (t : ℝ) :
    d.leftGlide (point t 0) =
      point (d.scalarData.w - t * d.scalarData.d)
        (1 / 2 - d.scalarData.z - t * d.scalarData.q) := by
  apply point_ext <;>
    simp [leftGlide, normal₂, tangent₂, scalarData] <;> ring

theorem halfTurn_right_base (d : FaceData) (t : ℝ) :
    halfTurn (d.right (point t 0)) =
      point (d.scalarData.u + t * d.scalarData.c)
        (1 / 2 + d.scalarData.v + t * d.scalarData.s) := by
  rw [right_base]
  apply point_ext <;> simp [halfTurn] <;> ring

theorem halfTurn_leftProper_base (d : FaceData) (t : ℝ) :
    halfTurn (d.leftProper (point t 0)) =
      point (1 - d.scalarData.w + t * d.scalarData.d)
        (1 / 2 - d.scalarData.z - t * d.scalarData.q) := by
  rw [leftProper_base]
  apply point_ext <;> simp [halfTurn] <;> ring

theorem vertical_right_base (d : FaceData) (t : ℝ) :
    verticalReflection (d.right (point t 0)) =
      point (d.scalarData.u + t * d.scalarData.c)
        (1 / 2 - d.scalarData.v - t * d.scalarData.s) := by
  rw [right_base]
  apply point_ext <;> simp [verticalReflection]
  ring

theorem vertical_leftGlide_base (d : FaceData) (t : ℝ) :
    verticalReflection (d.leftGlide (point t 0)) =
      point (1 - d.scalarData.w + t * d.scalarData.d)
        (1 / 2 - d.scalarData.z - t * d.scalarData.q) := by
  rw [leftGlide_base]
  apply point_ext <;> simp [verticalReflection]
  ring

theorem right_face₁minus (d : FaceData) :
    d.right d.face₁minus = point 1 (1 - d.b) := by
  apply point_ext
  · simp [right, face₁minus, normal₁]
    ring
  · simp [right, face₁minus, tangent₁]
    linear_combination (1 / 2 - d.b) * Real.cos_sq_add_sin_sq d.α

theorem right_face₁plus (d : FaceData) :
    d.right d.face₁plus = point 1 d.b := by
  apply point_ext
  · simp [right, face₁plus, normal₁]
    ring
  · simp [right, face₁plus, tangent₁]
    linear_combination -(1 / 2 - d.b) * Real.cos_sq_add_sin_sq d.α

theorem leftProper_face₂minus (d : FaceData) :
    d.leftProper d.face₂minus = point 0 (1 - d.a) := by
  apply point_ext
  · simp [leftProper, face₂minus, normal₂]
    ring
  · simp [leftProper, face₂minus, tangent₂]
    linear_combination (1 / 2 - d.a) * Real.cos_sq_add_sin_sq d.β

theorem leftProper_face₂plus (d : FaceData) :
    d.leftProper d.face₂plus = point 0 d.a := by
  apply point_ext
  · simp [leftProper, face₂plus, normal₂]
    ring
  · simp [leftProper, face₂plus, tangent₂]
    linear_combination -(1 / 2 - d.a) * Real.cos_sq_add_sin_sq d.β

theorem leftGlide_face₂minus (d : FaceData) :
    d.leftGlide d.face₂minus = point 0 d.a := by
  apply point_ext
  · simp [leftGlide, face₂minus, normal₂]
    ring
  · simp [leftGlide, face₂minus, tangent₂]
    linear_combination -(1 / 2 - d.a) * Real.cos_sq_add_sin_sq d.β

theorem leftGlide_face₂plus (d : FaceData) :
    d.leftGlide d.face₂plus = point 0 (1 - d.a) := by
  apply point_ext
  · simp [leftGlide, face₂plus, normal₂]
    ring
  · simp [leftGlide, face₂plus, tangent₂]
    linear_combination (1 / 2 - d.a) * Real.cos_sq_add_sin_sq d.β

end FaceData

namespace SupportedSource

variable {d : FaceData} {reversed : Bool} {P : Set Plane}

theorem right_base_mem (h : SupportedSource d reversed P) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    point (1 - d.scalarData.u - t * d.scalarData.c)
      (1 / 2 - d.scalarData.v - t * d.scalarData.s) ∈ d.right '' P := by
  rw [← d.right_base]
  exact mem_image_of_mem d.right (h.base_mem t ht)

theorem halfTurn_right_base_mem (h : SupportedSource d reversed P) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    point (d.scalarData.u + t * d.scalarData.c)
      (1 / 2 + d.scalarData.v + t * d.scalarData.s) ∈ halfTurn '' (d.right '' P) := by
  rw [← d.halfTurn_right_base]
  exact mem_image_of_mem halfTurn (mem_image_of_mem d.right (h.base_mem t ht))

theorem halfTurn_leftProper_base_mem (h : SupportedSource d false P) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    point (1 - d.scalarData.w + t * d.scalarData.d)
      (1 / 2 - d.scalarData.z - t * d.scalarData.q) ∈
        halfTurn '' (d.leftProper '' P) := by
  rw [← d.halfTurn_leftProper_base]
  exact mem_image_of_mem halfTurn (mem_image_of_mem d.leftProper (h.base_mem t ht))

theorem vertical_right_base_mem (h : SupportedSource d reversed P) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    point (d.scalarData.u + t * d.scalarData.c)
      (1 / 2 - d.scalarData.v - t * d.scalarData.s) ∈
        verticalReflection '' (d.right '' P) := by
  rw [← d.vertical_right_base]
  exact mem_image_of_mem verticalReflection (mem_image_of_mem d.right (h.base_mem t ht))

theorem vertical_leftGlide_base_mem (h : SupportedSource d true P) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    point (1 - d.scalarData.w + t * d.scalarData.d)
      (1 / 2 - d.scalarData.z - t * d.scalarData.q) ∈
        verticalReflection '' (d.leftGlide '' P) := by
  rw [← d.vertical_leftGlide_base]
  exact mem_image_of_mem verticalReflection (mem_image_of_mem d.leftGlide (h.base_mem t ht))

theorem right_gap_endpoints_mem (h : SupportedSource d reversed P) :
    point 1 d.b ∈ d.right '' P ∧ point 1 (1 - d.b) ∈ d.right '' P := by
  constructor
  · rw [← d.right_face₁plus]
    exact mem_image_of_mem d.right h.face₁plus_mem
  · rw [← d.right_face₁minus]
    exact mem_image_of_mem d.right h.face₁minus_mem

theorem leftProper_gap_endpoints_mem (h : SupportedSource d false P) :
    point 0 d.a ∈ d.leftProper '' P ∧ point 0 (1 - d.a) ∈ d.leftProper '' P := by
  constructor
  · rw [← d.leftProper_face₂plus]
    exact mem_image_of_mem d.leftProper h.face₂plus_mem
  · rw [← d.leftProper_face₂minus]
    exact mem_image_of_mem d.leftProper h.face₂minus_mem

theorem leftGlide_gap_endpoints_mem (h : SupportedSource d true P) :
    point 0 d.a ∈ d.leftGlide '' P ∧ point 0 (1 - d.a) ∈ d.leftGlide '' P := by
  constructor
  · rw [← d.leftGlide_face₂minus]
    exact mem_image_of_mem d.leftGlide h.face₂minus_mem
  · rw [← d.leftGlide_face₂plus]
    exact mem_image_of_mem d.leftGlide h.face₂plus_mem

end SupportedSource

end

end Puzzling139335.SourceFaceBridge
