import Mathlib

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Algebraic extraction of a lattice discrepancy from expanded-cell packing
-/

namespace Erdos394

/-- A sharp-leading expanded-cell packing bound, together with a reduced-cell
radius estimate and the first Minkowski bound, implies the standard planar
lattice discrepancy with an explicit absolute constant. -/
theorem expanded_cell_discrepancy
    {N D Y ρ L : ℝ}
    (hN : 0 ≤ N) (hD : 0 < D) (hY : 0 ≤ Y) (hρ : 0 ≤ ρ) (hL : 0 < L)
    (hpack : N * D ≤ (Y + 2 * ρ) ^ 2)
    (hreduced : ρ ≤ D / L + 2 * L)
    (hminkowski : L ^ 2 ≤ D) :
    N ≤ Y ^ 2 / D + 32 * (Y / L + D / L ^ 2 + 1) := by
  have hD0 : 0 ≤ D := hD.le
  have hL0 : 0 ≤ L := hL.le
  have hLD : L / D ≤ 1 / L := by
    apply (div_le_div_iff₀ hD hL).mpr
    field_simp [ne_of_gt hL]
    nlinarith
  have hYL : Y * L / D ≤ Y / L := by
    calc
      Y * L / D = Y * (L / D) := by ring
      _ ≤ Y * (1 / L) := mul_le_mul_of_nonneg_left hLD hY
      _ = Y / L := by ring
  have hyrho : Y * ρ / D ≤ 3 * (Y / L) := by
    have := mul_le_mul_of_nonneg_left hreduced hY
    have hdiv := (div_le_div_iff_of_pos_right hD).mpr this
    calc
      Y * ρ / D ≤ Y * (D / L + 2 * L) / D := hdiv
      _ = Y / L + 2 * (Y * L / D) := by field_simp
      _ ≤ Y / L + 2 * (Y / L) := by gcongr
      _ = 3 * (Y / L) := by ring
  have hrhoSq : ρ ^ 2 / D ≤ D / L ^ 2 + 8 := by
    have hsquare : ρ ^ 2 ≤ (D / L + 2 * L) ^ 2 := by
      exact (sq_le_sq₀ hρ (by positivity)).mpr hreduced
    have hdiv := (div_le_div_iff_of_pos_right hD).mpr hsquare
    have hLratio : L ^ 2 / D ≤ 1 := (div_le_one hD).mpr hminkowski
    calc
      ρ ^ 2 / D ≤ (D / L + 2 * L) ^ 2 / D := hdiv
      _ = D / L ^ 2 + 4 + 4 * (L ^ 2 / D) := by field_simp; ring
      _ ≤ D / L ^ 2 + 4 + 4 * 1 := by gcongr
      _ = D / L ^ 2 + 8 := by ring
  have hdivide : N ≤ (Y + 2 * ρ) ^ 2 / D := by
    apply (le_div_iff₀ hD).mpr
    simpa [mul_comm] using hpack
  calc
    N ≤ (Y + 2 * ρ) ^ 2 / D := hdivide
    _ = Y ^ 2 / D + 4 * (Y * ρ / D) + 4 * (ρ ^ 2 / D) := by
      field_simp
      ring
    _ ≤ Y ^ 2 / D + 4 * (3 * (Y / L)) +
          4 * (D / L ^ 2 + 8) := by gcongr
    _ ≤ Y ^ 2 / D + 32 * (Y / L + D / L ^ 2 + 1) := by
      have hyL0 : 0 ≤ Y / L := div_nonneg hY hL0
      have hdL0 : 0 ≤ D / L ^ 2 := div_nonneg hD0 (sq_nonneg L)
      nlinarith

end Erdos394
