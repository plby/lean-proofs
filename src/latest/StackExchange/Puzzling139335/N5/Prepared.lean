import StackExchange.Puzzling139335.N5.Normalized
import StackExchange.Puzzling139335.N5.StrictFrame.Placement.Form

/-!
# Actual data for the final five-incidence support calculation

The accompanying preparation theorem constructs these data from a
normalized dissection with a protected center.  The fields record actual
placements, source coordinates, and exact side contact sets.
-/

open Set

namespace Puzzling139335.N5

structure Prepared (d : SquareDissection) where
  normalized : Normalized d
  eR : Plane ≃ᵃⁱ[ℝ] Plane
  eD : Plane ≃ᵃⁱ[ℝ] Plane
  image_R : eR '' d.piece 0 = d.piece 2
  image_D : eD '' d.piece 0 = d.piece 3
  C : Plane
  C_eq : C = eR.symm (corner 2)
  θ : ℝ
  angle : θ ∈ Ioo (0 : ℝ) (Real.pi / 4)
  C_height_pos : 0 < C 1
  C_height_lt_first : C 1 < C 0
  C_first_lt_cos : C 0 < Real.cos θ
  cos_lt_one : Real.cos θ < 1
  transverse_pos : 0 < Real.cos θ * C 1 - Real.sin θ * C 0
  support_lt_one : Real.cos θ * C 0 + Real.sin θ * C 1 < 1
  b : ℝ
  m : ℝ
  b_pos : 0 < b
  b_lt_half : b < 1 / 2
  b_lt_ratio : b < Real.sin θ / (1 + Real.cos θ)
  b_lt_m : b < m
  m_lt_one : m < 1
  R_form : ∀ p, eR p =
    !₂[1 + Real.sin θ * C 0 - Real.cos θ * C 1 - Real.sin θ * p 0 + Real.cos θ * p 1,
       1 - Real.cos θ * C 0 - Real.sin θ * C 1 + Real.cos θ * p 0 + Real.sin θ * p 1]
  right_source : ∀ y : ℝ,
    Schoenflies.Plane.mk 1 y ∈ d.piece 0 ↔ 0 ≤ y ∧ y ≤ b
  right_singleton : ∀ y : ℝ,
    Schoenflies.Plane.mk 1 y ∈ d.piece 2 ↔ b ≤ y ∧ y ≤ 1
  top_singleton : ∀ x : ℝ,
    Schoenflies.Plane.mk x 1 ∈ d.piece 2 ↔ m ≤ x ∧ x ≤ 1
  top_fourth : ∀ x : ℝ,
    Schoenflies.Plane.mk x 1 ∈ d.piece 3 ↔ b ≤ x ∧ x ≤ m
  center_fourth : squareCenter ∈ interior (d.piece 3)

end Puzzling139335.N5
