import StackExchange.Puzzling139335.SourceFaceBridge.Placements
import StackExchange.Puzzling139335.JordanTransport

/-!
# Reflection of an actual supported source

Reflecting the source in the vertical midline exchanges its two angles,
side heights, and distinguished faces.  For the glide placement, the two
new image sets are the half-turn images of the old ones, in reversed order.
Every supported-source hypothesis is transported here from actual set
membership, rather than inferred from a scalar relaxation.
-/

open Set

namespace Puzzling139335.SourceFaceBridge

noncomputable section

private def verticalReflectionLinear : Plane ≃ₗᵢ[ℝ] Plane where
  toFun p := point (-p 0) (p 1)
  invFun p := point (-p 0) (p 1)
  left_inv p := by apply point_ext <;> simp
  right_inv p := by apply point_ext <;> simp
  map_add' p q := by
    apply point_ext
    · change -(p 0 + q 0) = -p 0 + -q 0
      ring
    · rfl
  map_smul' r p := by apply point_ext <;> simp [point]
  norm_map' p := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_two, point]

/-- Reflection in the vertical midline, with the exact coordinate formula. -/
def verticalReflectionIsometry : Plane ≃ᵃⁱ[ℝ] Plane :=
  AffineIsometryEquiv.mk' verticalReflection verticalReflectionLinear
    (0 : Plane) (by
      intro p
      apply point_ext <;>
        simp [verticalReflection, verticalReflectionLinear, point]
      ring)

/-- Rotation through a half turn about the square center. -/
def halfTurnIsometry : Plane ≃ᵃⁱ[ℝ] Plane :=
  AffineIsometryEquiv.mk' halfTurn (LinearIsometryEquiv.neg ℝ)
    (0 : Plane) (by
      intro p
      apply point_ext <;>
        simp [halfTurn, point] <;> ring)

@[simp] theorem coe_verticalReflectionIsometry :
    ⇑verticalReflectionIsometry = verticalReflection := rfl

@[simp] theorem coe_halfTurnIsometry :
    ⇑halfTurnIsometry = halfTurn := rfl

theorem verticalReflection_isometry : Isometry verticalReflection :=
  verticalReflectionIsometry.isometry

theorem halfTurn_isometry : Isometry halfTurn := halfTurnIsometry.isometry

@[simp] theorem verticalReflection_verticalReflection (p : Plane) :
    verticalReflection (verticalReflection p) = p := by
  apply point_ext <;> simp [verticalReflection]

@[simp] theorem halfTurn_halfTurn (p : Plane) : halfTurn (halfTurn p) = p := by
  apply point_ext <;> simp [halfTurn]

theorem verticalReflection_mem_lowerHalfSquare {p : Plane}
    (hp : p ∈ lowerHalfSquare) : verticalReflection p ∈ lowerHalfSquare := by
  change (1 - p 0 ∈ Icc (0 : ℝ) 1) ∧ p 1 ∈ Icc (0 : ℝ) (1 / 2)
  exact ⟨⟨by linarith [hp.1.2], by linarith [hp.1.1]⟩, hp.2⟩

theorem halfTurn_mem_unitSquare {p : Plane} (hp : p ∈ unitSquare) :
    halfTurn p ∈ unitSquare := by
  change (1 - p 0 ∈ Icc (0 : ℝ) 1) ∧ (1 - p 1 ∈ Icc (0 : ℝ) 1)
  exact ⟨⟨by linarith [hp.1.2], by linarith [hp.1.1]⟩,
    ⟨by linarith [hp.2.2], by linarith [hp.2.1]⟩⟩

theorem verticalReflection_isJordanRegion {P : Set Plane} (hP : IsJordanRegion P) :
    IsJordanRegion (verticalReflection '' P) := by
  simpa only [AffineIsometryEquiv.coe_toHomeomorph, coe_verticalReflectionIsometry] using
    hP.image_homeomorph verticalReflectionIsometry.toHomeomorph

namespace FaceData

/-- Reflect the source and exchange its two distinguished support faces. -/
def flip (d : FaceData) : FaceData where
  α := d.β
  β := d.α
  a := d.b
  b := d.a
  M₁ := verticalReflection d.M₂
  M₂ := verticalReflection d.M₁

@[simp] theorem flip_alpha (d : FaceData) : d.flip.α = d.β := rfl
@[simp] theorem flip_beta (d : FaceData) : d.flip.β = d.α := rfl
@[simp] theorem flip_a (d : FaceData) : d.flip.a = d.b := rfl
@[simp] theorem flip_b (d : FaceData) : d.flip.b = d.a := rfl
@[simp] theorem flip_M₁ (d : FaceData) : d.flip.M₁ = verticalReflection d.M₂ := rfl
@[simp] theorem flip_M₂ (d : FaceData) : d.flip.M₂ = verticalReflection d.M₁ := rfl

@[simp] theorem flip_flip (d : FaceData) : d.flip.flip = d := by
  cases d
  simp [flip]

theorem flip_right_verticalReflection (d : FaceData) (p : Plane) :
    d.flip.right (verticalReflection p) = halfTurn (d.leftGlide p) := by
  apply point_ext <;>
    simp [flip, right, leftGlide, normal₁, normal₂, tangent₁, tangent₂,
      verticalReflection, halfTurn] <;> ring

theorem flip_leftGlide_verticalReflection (d : FaceData) (p : Plane) :
    d.flip.leftGlide (verticalReflection p) = halfTurn (d.right p) := by
  apply point_ext <;>
    simp [flip, right, leftGlide, normal₁, normal₂, tangent₁, tangent₂,
      verticalReflection, halfTurn] <;> ring

@[simp] theorem flip_face₁minus (d : FaceData) :
    d.flip.face₁minus = verticalReflection d.face₂minus := by
  apply point_ext
  · simp [flip, face₁minus, face₂minus, verticalReflection]
    ring
  · rfl

@[simp] theorem flip_face₁plus (d : FaceData) :
    d.flip.face₁plus = verticalReflection d.face₂plus := by
  apply point_ext
  · simp [flip, face₁plus, face₂plus, verticalReflection]
    ring
  · rfl

@[simp] theorem flip_face₂minus (d : FaceData) :
    d.flip.face₂minus = verticalReflection d.face₁minus := by
  apply point_ext
  · simp [flip, face₁minus, face₂minus, verticalReflection]
    ring
  · rfl

@[simp] theorem flip_face₂plus (d : FaceData) :
    d.flip.face₂plus = verticalReflection d.face₁plus := by
  apply point_ext
  · simp [flip, face₁plus, face₂plus, verticalReflection]
    ring
  · rfl

theorem flip_right_image (d : FaceData) (P : Set Plane) :
    d.flip.right '' (verticalReflection '' P) = halfTurn '' (d.leftGlide '' P) := by
  rw [image_image, image_image]
  congr 1
  funext p
  exact d.flip_right_verticalReflection p

theorem flip_leftGlide_image (d : FaceData) (P : Set Plane) :
    d.flip.leftGlide '' (verticalReflection '' P) = halfTurn '' (d.right '' P) := by
  rw [image_image, image_image]
  congr 1
  funext p
  exact d.flip_leftGlide_verticalReflection p

theorem flip_inter_nontrivial (d : FaceData) {P : Set Plane}
    (hcommon : ((d.right '' P) ∩ (d.leftGlide '' P)).Nontrivial) :
    ((d.flip.right '' (verticalReflection '' P)) ∩
      (d.flip.leftGlide '' (verticalReflection '' P))).Nontrivial := by
  rw [d.flip_right_image, d.flip_leftGlide_image,
    ← image_inter halfTurn_isometry.injective]
  simpa only [inter_comm] using hcommon.image halfTurn_isometry.injective

theorem flip_disjoint_interiors (d : FaceData) {P : Set Plane}
    (hdisjoint : Disjoint (interior (d.right '' P)) (interior (d.leftGlide '' P))) :
    Disjoint (interior (d.flip.right '' (verticalReflection '' P)))
      (interior (d.flip.leftGlide '' (verticalReflection '' P))) := by
  have himage (S : Set Plane) : halfTurn '' interior S = interior (halfTurn '' S) := by
    simpa only [AffineIsometryEquiv.coe_toHomeomorph, coe_halfTurnIsometry] using
      halfTurnIsometry.toHomeomorph.image_interior S
  rw [d.flip_right_image, d.flip_leftGlide_image, ← himage, ← himage]
  exact disjoint_image_of_injective halfTurn_isometry.injective hdisjoint.symm

end FaceData

namespace SupportedSource

/-- Reflection transports every actual supported-source hypothesis and
exchanges the angles; the glide images are exchanged by a half turn. -/
theorem flip_glide {d : FaceData} {P : Set Plane} (h : SupportedSource d true P) :
    SupportedSource d.flip true (verticalReflection '' P) where
  alpha_pos := h.beta_pos
  alpha_lt_half_pi := h.beta_lt_half_pi
  beta_pos := h.alpha_pos
  beta_lt_half_pi := h.alpha_lt_half_pi
  a_pos := h.b_pos
  a_lt_half := h.b_lt_half
  b_pos := h.a_pos
  b_lt_half := h.a_lt_half
  source_subset := by
    rintro p ⟨q, hq, rfl⟩
    exact verticalReflection_mem_lowerHalfSquare (h.source_subset hq)
  base_mem := by
    intro t ht
    have hs : 1 - t ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    refine ⟨point (1 - t) 0, h.base_mem (1 - t) hs, ?_⟩
    apply point_ext <;> simp [verticalReflection]
  left_top_mem := by
    refine ⟨point 1 d.b, h.right_top_mem, ?_⟩
    apply point_ext <;> simp [verticalReflection]
  right_top_mem := by
    refine ⟨point 0 d.a, h.left_top_mem, ?_⟩
    apply point_ext <;> simp [verticalReflection]
  face₁minus_mem := by
    rw [FaceData.flip_face₁minus]
    exact mem_image_of_mem verticalReflection h.face₂minus_mem
  face₁plus_mem := by
    rw [FaceData.flip_face₁plus]
    exact mem_image_of_mem verticalReflection h.face₂plus_mem
  face₂minus_mem := by
    rw [FaceData.flip_face₂minus]
    exact mem_image_of_mem verticalReflection h.face₁minus_mem
  face₂plus_mem := by
    rw [FaceData.flip_face₂plus]
    exact mem_image_of_mem verticalReflection h.face₁plus_mem
  right_fits := by
    rintro p ⟨q, hq, rfl⟩
    rw [FaceData.flip_right_verticalReflection]
    exact halfTurn_mem_unitSquare (h.left_fits hq)
  left_fits := by
    rintro p ⟨q, hq, rfl⟩
    change d.flip.leftGlide (verticalReflection q) ∈ unitSquare
    rw [FaceData.flip_leftGlide_verticalReflection]
    exact halfTurn_mem_unitSquare (h.right_fits hq)

end SupportedSource

end

end Puzzling139335.SourceFaceBridge
