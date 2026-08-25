import StackExchange.Puzzling139335.SourceFaceBridge.Defs

/-!
# The source-face placement maps are affine isometries

The explicit placements from `Defs` are bundled here as affine isometry
equivalences.  Their formulas need no angle bounds or assumptions about the
source set: the identity `cos θ ^ 2 + sin θ ^ 2 = 1` suffices.
-/

namespace Puzzling139335.SourceFaceBridge

noncomputable section

private def rotationLinear (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    Plane ≃ₗᵢ[ℝ] Plane where
  toFun p := point (c * p 0 - s * p 1) (s * p 0 + c * p 1)
  invFun p := point (c * p 0 + s * p 1) (-s * p 0 + c * p 1)
  left_inv p := by
    apply point_ext
    · change c * (c * p 0 - s * p 1) + s * (s * p 0 + c * p 1) = p 0
      calc
        _ = (c ^ 2 + s ^ 2) * p 0 := by ring
        _ = _ := by rw [h]; ring
    · change -s * (c * p 0 - s * p 1) + c * (s * p 0 + c * p 1) = p 1
      calc
        _ = (c ^ 2 + s ^ 2) * p 1 := by ring
        _ = _ := by rw [h]; ring
  right_inv p := by
    apply point_ext
    · change c * (c * p 0 + s * p 1) - s * (-s * p 0 + c * p 1) = p 0
      calc
        _ = (c ^ 2 + s ^ 2) * p 0 := by ring
        _ = _ := by rw [h]; ring
    · change s * (c * p 0 + s * p 1) + c * (-s * p 0 + c * p 1) = p 1
      calc
        _ = (c ^ 2 + s ^ 2) * p 1 := by ring
        _ = _ := by rw [h]; ring
  map_add' p q := by
    apply point_ext <;> simp [point] <;> ring
  map_smul' r p := by
    apply point_ext <;> simp [point] <;> ring
  norm_map' p := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two]
    change (c * p 0 - s * p 1) ^ 2 + (s * p 0 + c * p 1) ^ 2 = _
    calc
      _ = (c ^ 2 + s ^ 2) * (p 0 ^ 2 + p 1 ^ 2) := by ring
      _ = _ := by rw [h]; ring

private def horizontalReflectionLinear : Plane ≃ₗᵢ[ℝ] Plane where
  toFun p := point (p 0) (-p 1)
  invFun p := point (p 0) (-p 1)
  left_inv p := by apply point_ext <;> simp
  right_inv p := by apply point_ext <;> simp
  map_add' p q := by
    apply point_ext
    · rfl
    · change -(p 1 + q 1) = -p 1 + -q 1
      ring
  map_smul' r p := by apply point_ext <;> simp [point]
  norm_map' p := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_two, point]

namespace FaceData

/-- The right placement, with precisely the coordinate formula `right`. -/
def rightIsometry (d : FaceData) : Plane ≃ᵃⁱ[ℝ] Plane :=
  AffineIsometryEquiv.mk' d.right
    (rotationLinear (-Real.cos d.α) (-Real.sin d.α)
      (by simp)) (0 : Plane) (by
      intro p
      apply point_ext <;>
        simp [right, normal₁, tangent₁, rotationLinear, point] <;> ring)

/-- The orientation-preserving left placement. -/
def leftProperIsometry (d : FaceData) : Plane ≃ᵃⁱ[ℝ] Plane :=
  AffineIsometryEquiv.mk' d.leftProper
    (rotationLinear (-Real.cos d.β) (Real.sin d.β)
      (by simp)) (0 : Plane) (by
      intro p
      apply point_ext <;>
        simp [leftProper, normal₂, tangent₂, rotationLinear, point] <;> ring)

/-- The orientation-reversing left placement. -/
def leftGlideIsometry (d : FaceData) : Plane ≃ᵃⁱ[ℝ] Plane :=
  AffineIsometryEquiv.mk' d.leftGlide
    ((rotationLinear (-Real.cos d.β) (Real.sin d.β)
      (by simp)).trans
        horizontalReflectionLinear) (0 : Plane) (by
      intro p
      apply point_ext <;>
        simp [leftGlide, normal₂, tangent₂, rotationLinear,
          horizontalReflectionLinear, point] <;> ring)

/-- The left placement with either parity. -/
def leftIsometry (d : FaceData) (reversed : Bool) : Plane ≃ᵃⁱ[ℝ] Plane :=
  if reversed then d.leftGlideIsometry else d.leftProperIsometry

@[simp] theorem coe_rightIsometry (d : FaceData) : ⇑d.rightIsometry = d.right := rfl

@[simp] theorem coe_leftProperIsometry (d : FaceData) :
    ⇑d.leftProperIsometry = d.leftProper := rfl

@[simp] theorem coe_leftGlideIsometry (d : FaceData) :
    ⇑d.leftGlideIsometry = d.leftGlide := rfl

@[simp] theorem coe_leftIsometry (d : FaceData) (reversed : Bool) :
    ⇑(d.leftIsometry reversed) = d.left reversed := by
  cases reversed <;> rfl

theorem right_isometry (d : FaceData) : Isometry d.right :=
  d.rightIsometry.isometry

theorem leftProper_isometry (d : FaceData) : Isometry d.leftProper :=
  d.leftProperIsometry.isometry

theorem leftGlide_isometry (d : FaceData) : Isometry d.leftGlide :=
  d.leftGlideIsometry.isometry

theorem left_isometry (d : FaceData) (reversed : Bool) : Isometry (d.left reversed) := by
  simpa only [coe_leftIsometry] using (d.leftIsometry reversed).isometry

theorem right_bijective (d : FaceData) : Function.Bijective d.right :=
  d.rightIsometry.toAffineEquiv.toEquiv.bijective

theorem leftProper_bijective (d : FaceData) : Function.Bijective d.leftProper :=
  d.leftProperIsometry.toAffineEquiv.toEquiv.bijective

theorem leftGlide_bijective (d : FaceData) : Function.Bijective d.leftGlide :=
  d.leftGlideIsometry.toAffineEquiv.toEquiv.bijective

theorem left_bijective (d : FaceData) (reversed : Bool) :
    Function.Bijective (d.left reversed) := by
  cases reversed
  · exact d.leftProper_bijective
  · exact d.leftGlide_bijective

theorem right_map_lineMap (d : FaceData) (p q : Plane) (t : ℝ) :
    d.right (AffineMap.lineMap p q t) =
      AffineMap.lineMap (d.right p) (d.right q) t :=
  d.rightIsometry.toAffineEquiv.apply_lineMap p q t

theorem leftProper_map_lineMap (d : FaceData) (p q : Plane) (t : ℝ) :
    d.leftProper (AffineMap.lineMap p q t) =
      AffineMap.lineMap (d.leftProper p) (d.leftProper q) t :=
  d.leftProperIsometry.toAffineEquiv.apply_lineMap p q t

theorem leftGlide_map_lineMap (d : FaceData) (p q : Plane) (t : ℝ) :
    d.leftGlide (AffineMap.lineMap p q t) =
      AffineMap.lineMap (d.leftGlide p) (d.leftGlide q) t :=
  d.leftGlideIsometry.toAffineEquiv.apply_lineMap p q t

theorem left_map_lineMap (d : FaceData) (reversed : Bool) (p q : Plane) (t : ℝ) :
    d.left reversed (AffineMap.lineMap p q t) =
      AffineMap.lineMap (d.left reversed p) (d.left reversed q) t := by
  cases reversed
  · exact d.leftProper_map_lineMap p q t
  · exact d.leftGlide_map_lineMap p q t

end FaceData

end

end Puzzling139335.SourceFaceBridge
