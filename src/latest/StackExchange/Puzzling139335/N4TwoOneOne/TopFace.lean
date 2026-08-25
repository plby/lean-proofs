import StackExchange.Puzzling139335.N4TwoOneOne.Defs
import StackExchange.Puzzling139335.PlaneIsometries.Matrix

/-!
# Pulling an actual top interval back to its source support face

The endpoints and opposite support bound below follow from an actual affine
isometry fitting the source inside the square. No boundary tangent or hull
length is supplied as an additional assumption.
-/

open Set

namespace Puzzling139335.N4TwoOneOne

open PlaneIsometries ThreeCorners

theorem affine_direction_coordinate (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (p w : Plane) (t : ℝ) (i : Fin 2) :
    e (p + t • w) i = e p i + t *
      (linearMatrix e i 0 * w 0 + linearMatrix e i 1 * w 1) := by
  rw [affine_apply_eq_matrix_coordinates e (p + t • w),
    affine_apply_eq_matrix_coordinates e p]
  fin_cases i <;> simp <;> ring

/-- Orthogonality leaves exactly two possible horizontal rows once the
top normal has been specified. -/
theorem first_row_of_top_normal (e : Plane ≃ᵃⁱ[ℝ] Plane) (φ : ℝ)
    (h₀ : linearMatrix e 1 0 = Real.cos φ)
    (h₁ : linearMatrix e 1 1 = Real.sin φ) :
    (linearMatrix e 0 0 = -Real.sin φ ∧ linearMatrix e 0 1 = Real.cos φ) ∨
      (linearMatrix e 0 0 = Real.sin φ ∧ linearMatrix e 0 1 = -Real.cos φ) := by
  obtain ⟨c, s, _, hm | hm⟩ := linearMatrix_classification e
  · right
    rw [hm] at h₀ h₁ ⊢
    change s = Real.cos φ at h₀
    change c = Real.sin φ at h₁
    change c = Real.sin φ ∧ -s = -Real.cos φ
    exact ⟨h₁, congrArg Neg.neg h₀⟩
  · left
    rw [hm] at h₀ h₁ ⊢
    change s = Real.cos φ at h₀
    change -c = Real.sin φ at h₁
    change c = -Real.sin φ ∧ s = Real.cos φ
    constructor
    · linarith
    · exact h₀

theorem top_projection_formula (e : Plane ≃ᵃⁱ[ℝ] Plane) (φ : ℝ)
    (h₀ : linearMatrix e 1 0 = Real.cos φ)
    (h₁ : linearMatrix e 1 1 = Real.sin φ) (p : Plane) :
    e p 1 = eCoord φ p + e 0 1 := by
  rw [affine_apply_eq_matrix_coordinates e p]
  simp [eCoord, h₀, h₁]

theorem top_tangent_step (e : Plane ≃ᵃⁱ[ℝ] Plane) (φ : ℝ)
    (h₀ : linearMatrix e 1 0 = Real.cos φ)
    (h₁ : linearMatrix e 1 1 = Real.sin φ)
    (hrow : linearMatrix e 0 0 = -Real.sin φ ∧
      linearMatrix e 0 1 = Real.cos φ) (p : Plane) (t : ℝ) :
    e (p + t • perpRay φ) = !₂[e p 0 + t, e p 1] := by
  have hsq := Real.sin_sq_add_cos_sq φ
  apply plane_ext
  · rw [affine_direction_coordinate]
    simp only [hrow.1, hrow.2, perpRay, Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith only [congrArg (fun z : ℝ => t * z) hsq]
  · rw [affine_direction_coordinate]
    simp only [h₀, h₁, perpRay, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

theorem top_negative_tangent_step (e : Plane ≃ᵃⁱ[ℝ] Plane) (φ : ℝ)
    (h₀ : linearMatrix e 1 0 = Real.cos φ)
    (h₁ : linearMatrix e 1 1 = Real.sin φ)
    (hrow : linearMatrix e 0 0 = Real.sin φ ∧
      linearMatrix e 0 1 = -Real.cos φ) (p : Plane) (t : ℝ) :
    e (p + t • perpRay φ) = !₂[e p 0 - t, e p 1] := by
  have hsq := Real.sin_sq_add_cos_sq φ
  apply plane_ext
  · rw [affine_direction_coordinate]
    simp only [hrow.1, hrow.2, perpRay, Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith only [congrArg (fun z : ℝ => t * z) hsq]
  · rw [affine_direction_coordinate]
    simp only [h₀, h₁, perpRay, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

/-- An actual central top interval gives an ordered source support segment,
including the full opposite support bound imposed by the fitted square. -/
theorem exists_top_face_endpoints {P : Set Plane} (e : Plane ≃ᵃⁱ[ℝ] Plane)
    {φ T : ℝ} (hfit : e '' P ⊆ unitSquare)
    (h₀ : linearMatrix e 1 0 = Real.cos φ)
    (h₁ : linearMatrix e 1 1 = Real.sin φ)
    (hleft : (!₂[T, 1] : Plane) ∈ e '' P)
    (hright : (!₂[1 - T, 1] : Plane) ∈ e '' P) :
    ∃ X Y : Plane, X ∈ P ∧ Y ∈ P ∧
      Y = X + (1 - 2 * T) • perpRay φ ∧
      (∀ p ∈ P, eCoord φ p ≤ eCoord φ X) ∧
      (∀ p ∈ P, eCoord φ X - 1 ≤ eCoord φ p) := by
  obtain ⟨L, hL, heL⟩ := hleft
  obtain ⟨R, hR, heR⟩ := hright
  have hsupp (X : Plane) (hX : e X 1 = 1) :
      (∀ p ∈ P, eCoord φ p ≤ eCoord φ X) ∧
      (∀ p ∈ P, eCoord φ X - 1 ≤ eCoord φ p) := by
    have hXeq := top_projection_formula e φ h₀ h₁ X
    rw [hX] at hXeq
    constructor
    · intro p hp
      have hb := (hfit (mem_image_of_mem e hp)).2.2
      rw [top_projection_formula e φ h₀ h₁ p] at hb
      linarith
    · intro p hp
      have hb := (hfit (mem_image_of_mem e hp)).2.1
      rw [top_projection_formula e φ h₀ h₁ p] at hb
      linarith
  rcases first_row_of_top_normal e φ h₀ h₁ with hrow | hrow
  · refine ⟨L, R, hL, hR, ?_, hsupp L ?_⟩
    · apply e.injective
      rw [top_tangent_step e φ h₀ h₁ hrow, heL, heR]
      ext i
      fin_cases i <;> simp <;> ring
    · rw [heL]
      rfl
  · refine ⟨R, L, hR, hL, ?_, hsupp R ?_⟩
    · apply e.injective
      rw [top_negative_tangent_step e φ h₀ h₁ hrow, heL, heR]
      ext i
      fin_cases i <;> simp <;> ring
    · rw [heR]
      rfl

end Puzzling139335.N4TwoOneOne
