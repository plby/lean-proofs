import StackExchange.Puzzling139335.PlaneIsometries.Matrix

/-!
# Coordinate forms and endpoint differences for an actual top-face placement

Fixing the second row of an actual Euclidean isometry leaves exactly two
possibilities for its first row.  Both orientations are retained throughout
the inverse-endpoint formulas.
-/

namespace Puzzling139335.N5

open PlaneIsometries

/-- The specified second row of an actual isometry is a unit vector. -/
theorem eD_top_row_unit (e : Plane ≃ᵃⁱ[ℝ] Plane) (nx ny : ℝ)
    (hrow0 : linearMatrix e 1 0 = nx) (hrow1 : linearMatrix e 1 1 = ny) :
    nx ^ 2 + ny ^ 2 = 1 := by
  simpa [hrow0, hrow1, pow_two] using linearMatrix_row_dot e 1 1

/-- The actual matrix classification gives the two full coordinate forms
compatible with the specified second row. -/
theorem eD_top_row_forms (e : Plane ≃ᵃⁱ[ℝ] Plane) (nx ny : ℝ)
    (hrow0 : linearMatrix e 1 0 = nx) (hrow1 : linearMatrix e 1 1 = ny) :
    (∀ p, e p =
      !₂[ny * p 0 - nx * p 1 + (e 0) 0,
         nx * p 0 + ny * p 1 + (e 0) 1]) ∨
    (∀ p, e p =
      !₂[-ny * p 0 + nx * p 1 + (e 0) 0,
         nx * p 0 + ny * p 1 + (e 0) 1]) := by
  obtain ⟨c, s, _hcs, hm | hm⟩ := linearMatrix_classification e
  · have hs : s = nx := by simpa [hm] using hrow0
    have hc : c = ny := by simpa [hm] using hrow1
    left
    intro p
    rw [affine_apply_eq_matrix_coordinates e p, hm]
    apply plane_ext <;> simp [hs, hc] <;> ring
  · have hs : s = nx := by simpa [hm] using hrow0
    have hcneg : -c = ny := by simpa [hm] using hrow1
    have hc : c = -ny := by linarith only [hcneg]
    right
    intro p
    rw [affine_apply_eq_matrix_coordinates e p, hm]
    apply plane_ext <;> simp [hs, hc] <;> ring

/-- In the first row order, a horizontal image displacement pulls back
to the source direction `(ny, -nx)`. -/
theorem eD_top_difference_first
    {e : Plane ≃ᵃⁱ[ℝ] Plane} {nx ny : ℝ} {p q : Plane} {j : ℝ}
    (hunit : nx ^ 2 + ny ^ 2 = 1)
    (hform : ∀ r, e r =
      !₂[ny * r 0 - nx * r 1 + (e 0) 0,
         nx * r 0 + ny * r 1 + (e 0) 1])
    (hgap0 : (e q) 0 - (e p) 0 = j)
    (hgap1 : (e q) 1 - (e p) 1 = 0) :
    q 0 = p 0 + j * ny ∧ q 1 = p 1 - j * nx := by
  have hA : ny * (q 0 - p 0) - nx * (q 1 - p 1) = j := by
    calc
      _ = (e q) 0 - (e p) 0 := by
        rw [hform q, hform p]
        change ny * (q 0 - p 0) - nx * (q 1 - p 1) =
          (ny * q 0 - nx * q 1 + (e 0) 0) -
            (ny * p 0 - nx * p 1 + (e 0) 0)
        ring
      _ = j := hgap0
  have hB : nx * (q 0 - p 0) + ny * (q 1 - p 1) = 0 := by
    calc
      _ = (e q) 1 - (e p) 1 := by
        rw [hform q, hform p]
        change nx * (q 0 - p 0) + ny * (q 1 - p 1) =
          (nx * q 0 + ny * q 1 + (e 0) 1) -
            (nx * p 0 + ny * p 1 + (e 0) 1)
        ring
      _ = 0 := hgap1
  constructor
  · linear_combination ny * hA + nx * hB - (q 0 - p 0) * hunit
  · linear_combination (-nx) * hA + ny * hB - (q 1 - p 1) * hunit

/-- In the second row order, a horizontal image displacement pulls back
to the source direction `(-ny, nx)`. -/
theorem eD_top_difference_second
    {e : Plane ≃ᵃⁱ[ℝ] Plane} {nx ny : ℝ} {p q : Plane} {j : ℝ}
    (hunit : nx ^ 2 + ny ^ 2 = 1)
    (hform : ∀ r, e r =
      !₂[-ny * r 0 + nx * r 1 + (e 0) 0,
         nx * r 0 + ny * r 1 + (e 0) 1])
    (hgap0 : (e q) 0 - (e p) 0 = j)
    (hgap1 : (e q) 1 - (e p) 1 = 0) :
    q 0 = p 0 - j * ny ∧ q 1 = p 1 + j * nx := by
  have hA : -ny * (q 0 - p 0) + nx * (q 1 - p 1) = j := by
    calc
      _ = (e q) 0 - (e p) 0 := by
        rw [hform q, hform p]
        change -ny * (q 0 - p 0) + nx * (q 1 - p 1) =
          (-ny * q 0 + nx * q 1 + (e 0) 0) -
            (-ny * p 0 + nx * p 1 + (e 0) 0)
        ring
      _ = j := hgap0
  have hB : nx * (q 0 - p 0) + ny * (q 1 - p 1) = 0 := by
    calc
      _ = (e q) 1 - (e p) 1 := by
        rw [hform q, hform p]
        change nx * (q 0 - p 0) + ny * (q 1 - p 1) =
          (nx * q 0 + ny * q 1 + (e 0) 1) -
            (nx * p 0 + ny * p 1 + (e 0) 1)
        ring
      _ = 0 := hgap1
  constructor
  · linear_combination (-ny) * hA + nx * hB - (q 0 - p 0) * hunit
  · linear_combination nx * hA + ny * hB - (q 1 - p 1) * hunit

/-- Actual inverse endpoints on the same top side in the first row order.
The identity holds without an order assumption on the two coordinates. -/
theorem eD_top_inverse_endpoints_first
    {e : Plane ≃ᵃⁱ[ℝ] Plane} {nx ny : ℝ}
    (hunit : nx ^ 2 + ny ^ 2 = 1)
    (hform : ∀ r, e r =
      !₂[ny * r 0 - nx * r 1 + (e 0) 0,
         nx * r 0 + ny * r 1 + (e 0) 1]) (b m : ℝ) :
    (e.symm (Schoenflies.Plane.mk m 1)) 0 =
        (e.symm (Schoenflies.Plane.mk b 1)) 0 + (m - b) * ny ∧
      (e.symm (Schoenflies.Plane.mk m 1)) 1 =
        (e.symm (Schoenflies.Plane.mk b 1)) 1 - (m - b) * nx := by
  apply eD_top_difference_first
    (p := e.symm (Schoenflies.Plane.mk b 1))
    (q := e.symm (Schoenflies.Plane.mk m 1)) (j := m - b) hunit hform
  · simp [e.apply_symm_apply, Schoenflies.Plane.mk]
  · simp [e.apply_symm_apply, Schoenflies.Plane.mk]

/-- Actual inverse endpoints on the same top side in the second row order. -/
theorem eD_top_inverse_endpoints_second
    {e : Plane ≃ᵃⁱ[ℝ] Plane} {nx ny : ℝ}
    (hunit : nx ^ 2 + ny ^ 2 = 1)
    (hform : ∀ r, e r =
      !₂[-ny * r 0 + nx * r 1 + (e 0) 0,
         nx * r 0 + ny * r 1 + (e 0) 1]) (b m : ℝ) :
    (e.symm (Schoenflies.Plane.mk m 1)) 0 =
        (e.symm (Schoenflies.Plane.mk b 1)) 0 - (m - b) * ny ∧
      (e.symm (Schoenflies.Plane.mk m 1)) 1 =
        (e.symm (Schoenflies.Plane.mk b 1)) 1 + (m - b) * nx := by
  apply eD_top_difference_second
    (p := e.symm (Schoenflies.Plane.mk b 1))
    (q := e.symm (Schoenflies.Plane.mk m 1)) (j := m - b) hunit hform
  · simp [e.apply_symm_apply, Schoenflies.Plane.mk]
  · simp [e.apply_symm_apply, Schoenflies.Plane.mk]

end Puzzling139335.N5
