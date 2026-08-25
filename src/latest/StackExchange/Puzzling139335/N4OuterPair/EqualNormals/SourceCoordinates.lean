import StackExchange.Puzzling139335.SourceFaceBridge.UpperDefs

/-!
# Equal source normals give exact axial relative coordinates

The two support levels agree because actual endpoints of both selected
faces belong to the prototype.  Substitution into the placement formulas
then identifies the relative map, including its horizontal translation.
-/

open Set

namespace Puzzling139335.SourceFaceBridge

namespace UpperFaceData

theorem normal₁_face₁minus (d : UpperFaceData) :
    d.normal₁ d.face₁minus = d.normal₁ d.M₁ := by
  simp only [normal₁, face₁minus, point, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

theorem normal₂_face₂minus (d : UpperFaceData) :
    d.normal₂ d.face₂minus = d.normal₂ d.M₂ := by
  simp only [normal₂, face₂minus, point, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

theorem normal₂_eq_normal₁ (d : UpperFaceData) (heq : d.φ = d.ψ) (p : Plane) :
    d.normal₂ p = d.normal₁ p := by
  simp only [normal₁, normal₂, heq]

theorem tangent₂_eq_tangent₁ (d : UpperFaceData) (heq : d.φ = d.ψ) (p : Plane) :
    d.tangent₂ p = d.tangent₁ p := by
  simp only [tangent₁, tangent₂, heq]

end UpperFaceData

namespace UpperSupportedSource

variable {d : UpperFaceData} {reversed : Bool} {P : Set Plane}

/-- The selected actual faces with the same normal have the same support
value; no equality of the midpoints themselves is asserted. -/
theorem support_levels_eq_of_equal_normals (h : UpperSupportedSource d reversed P)
    (heq : d.φ = d.ψ) : d.normal₁ d.M₁ = d.normal₂ d.M₂ := by
  have h₁ := (h.source_supports h.face₁minus_mem).2
  have h₂ := (h.source_supports h.face₂minus_mem).1
  rw [d.normal₂_eq_normal₁ heq d.face₁minus, d.normal₁_face₁minus] at h₁
  rw [← d.normal₂_eq_normal₁ heq d.face₂minus, d.normal₂_face₂minus] at h₂
  exact le_antisymm h₁ h₂

/-- In proper parity, equal normals give a half-turn with horizontal
center coordinate exactly one half. -/
theorem leftProper_coordinates_of_equal_normals (h : UpperSupportedSource d reversed P)
    (heq : d.φ = d.ψ) (p : Plane) :
    d.leftProper p 0 = 1 - d.right p 0 ∧
      d.leftProper p 1 = 1 - d.right p 1 +
        (d.tangent₁ d.M₂ - d.tangent₁ d.M₁) := by
  have hlevel := h.support_levels_eq_of_equal_normals heq
  constructor
  · change d.normal₂ d.M₂ - d.normal₂ p =
      1 - (1 + d.normal₁ p - d.normal₁ d.M₁)
    rw [d.normal₂_eq_normal₁ heq p, ← hlevel]
    ring
  · change 1 / 2 - d.tangent₂ p + d.tangent₂ d.M₂ =
      1 - (1 / 2 + d.tangent₁ p - d.tangent₁ d.M₁) +
        (d.tangent₁ d.M₂ - d.tangent₁ d.M₁)
    rw [d.tangent₂_eq_tangent₁ heq p, d.tangent₂_eq_tangent₁ heq d.M₂]
    ring

/-- In reversed parity, equal normals give a vertical-axis reflection
with a possible vertical glide. -/
theorem leftGlide_coordinates_of_equal_normals (h : UpperSupportedSource d reversed P)
    (heq : d.φ = d.ψ) (p : Plane) :
    d.leftGlide p 0 = 1 - d.right p 0 ∧
      d.leftGlide p 1 = d.right p 1 +
        (d.tangent₁ d.M₁ - d.tangent₁ d.M₂) := by
  have hlevel := h.support_levels_eq_of_equal_normals heq
  constructor
  · change d.normal₂ d.M₂ - d.normal₂ p =
      1 - (1 + d.normal₁ p - d.normal₁ d.M₁)
    rw [d.normal₂_eq_normal₁ heq p, ← hlevel]
    ring
  · change 1 / 2 + d.tangent₂ p - d.tangent₂ d.M₂ =
      (1 / 2 + d.tangent₁ p - d.tangent₁ d.M₁) +
        (d.tangent₁ d.M₁ - d.tangent₁ d.M₂)
    rw [d.tangent₂_eq_tangent₁ heq p, d.tangent₂_eq_tangent₁ heq d.M₂]
    ring

end UpperSupportedSource

end Puzzling139335.SourceFaceBridge
