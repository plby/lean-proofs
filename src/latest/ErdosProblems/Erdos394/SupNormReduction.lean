import ErdosProblems.Erdos394.BasisZonotopeCount

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Elementary two-dimensional sup-norm basis reduction
-/

open Module
open scoped Matrix

namespace Erdos394

/-- If the first coordinate realizes the height of `u`, the corresponding
coordinate of `v` has been reduced modulo `u`, and `v` is no shorter than `u`,
then the usual reduced-basis and Hermite bounds follow. -/
theorem reduced_pair_bounds_coord_zero
    {u v : Fin 2 → ℝ} {L D : ℝ}
    (hL : 0 < L) (hu : supHeight2 u = L)
    (hucoord : |u 1| ≤ |u 0|)
    (hD : |u 0 * v 1 - u 1 * v 0| = D)
    (hvred : |v 0| ≤ L / 2)
    (hmin : L ≤ supHeight2 v) :
    supHeight2 v ≤ D / L + L / 2 ∧ L ^ 2 ≤ 2 * D := by
  have hu0 : |u 0| = L := by
    simpa [supHeight2, max_eq_left hucoord] using hu
  have hu1 : |u 1| ≤ L := hu0 ▸ hucoord
  have hD0 : 0 ≤ D := by rw [← hD]; positivity
  have hrev : |u 0 * v 1| - |u 1 * v 0| ≤ D := by
    rw [← hD]
    exact abs_sub_abs_le_abs_sub _ _
  rw [abs_mul, abs_mul, hu0] at hrev
  have hcross : L * |v 1| ≤ D + L * (L / 2) := by
    have huv0 : |u 1| * |v 0| ≤ L * (L / 2) :=
      mul_le_mul hu1 hvred (abs_nonneg _) hL.le
    linarith
  have hbound1 : |v 1| ≤ D / L + L / 2 := by
    rw [show D / L + L / 2 = (D + L * (L / 2)) / L by
      field_simp]
    exact (le_div_iff₀ hL).mpr (by simpa [mul_comm] using hcross)
  have hbound0 : |v 0| ≤ D / L + L / 2 := by
    have : 0 ≤ D / L := div_nonneg hD0 hL.le
    linarith
  have hvbound : supHeight2 v ≤ D / L + L / 2 :=
    max_le hbound0 hbound1
  have hv1lower : L ≤ |v 1| := by
    rw [supHeight2, le_max_iff] at hmin
    rcases hmin with h0 | h1
    · nlinarith [hvred]
    · exact h1
  have hmain : L ^ 2 ≤ L * |v 1| := by nlinarith
  have hsmall : |u 1| * |v 0| ≤ L ^ 2 / 2 := by
    nlinarith [mul_le_mul hu1 hvred (abs_nonneg _) hL.le]
  exact ⟨hvbound, by nlinarith⟩

/-- Symmetric version when the second coordinate realizes the height. -/
theorem reduced_pair_bounds_coord_one
    {u v : Fin 2 → ℝ} {L D : ℝ}
    (hL : 0 < L) (hu : supHeight2 u = L)
    (hucoord : |u 0| ≤ |u 1|)
    (hD : |u 0 * v 1 - u 1 * v 0| = D)
    (hvred : |v 1| ≤ L / 2)
    (hmin : L ≤ supHeight2 v) :
    supHeight2 v ≤ D / L + L / 2 ∧ L ^ 2 ≤ 2 * D := by
  have hu1 : |u 1| = L := by
    simpa [supHeight2, max_eq_right hucoord] using hu
  have hu0 : |u 0| ≤ L := hu1 ▸ hucoord
  have hD0 : 0 ≤ D := by rw [← hD]; positivity
  have hrev : |u 1 * v 0| - |u 0 * v 1| ≤ D := by
    rw [← hD, abs_sub_comm]
    exact abs_sub_abs_le_abs_sub _ _
  rw [abs_mul, abs_mul, hu1] at hrev
  have hcross : L * |v 0| ≤ D + L * (L / 2) := by
    have huv1 : |u 0| * |v 1| ≤ L * (L / 2) :=
      mul_le_mul hu0 hvred (abs_nonneg _) hL.le
    linarith
  have hbound0 : |v 0| ≤ D / L + L / 2 := by
    rw [show D / L + L / 2 = (D + L * (L / 2)) / L by
      field_simp]
    exact (le_div_iff₀ hL).mpr (by simpa [mul_comm] using hcross)
  have hbound1 : |v 1| ≤ D / L + L / 2 := by
    have : 0 ≤ D / L := div_nonneg hD0 hL.le
    linarith
  have hvbound : supHeight2 v ≤ D / L + L / 2 :=
    max_le hbound0 hbound1
  have hv0lower : L ≤ |v 0| := by
    rw [supHeight2, le_max_iff] at hmin
    rcases hmin with h0 | h1
    · exact h0
    · nlinarith [hvred]
  have hmain : L ^ 2 ≤ L * |v 0| := by nlinarith
  have hsmall : |u 0| * |v 1| ≤ L ^ 2 / 2 := by
    nlinarith [mul_le_mul hu0 hvred (abs_nonneg _) hL.le]
  exact ⟨hvbound, by nlinarith⟩

/-- The factor-two Hermite estimate from the preceding reduction still gives
the required sharp-leading discrepancy. -/
theorem reduced_basis_square_discrepancy_two
    (b : Basis (Fin 2) ℝ (Fin 2 → ℝ))
    (A : Finset (Submodule.span ℤ (Set.range b))) {Y D L : ℝ}
    (hY : 0 < Y) (hD : 0 < D) (hL : 0 < L)
    (hdet : |(Pi.basisFun ℝ (Fin 2)).det ![b 0, b 1]| = D)
    (hu : supHeight2 (b 0) ≤ L)
    (hv : supHeight2 (b 1) ≤ D / L + L / 2)
    (hmink : L ^ 2 ≤ 2 * D)
    (hpoint : ∀ g ∈ A, ∀ i, 0 ≤ (g : Fin 2 → ℝ) i ∧ (g : Fin 2 → ℝ) i ≤ Y) :
    (A.card : ℝ) ≤ Y ^ 2 / D + 40 * (Y / L) + 4 := by
  have hcount := basis_square_card_mul_det_le_height b A hY hpoint
  rw [hdet] at hcount
  have hY0 := hY.le
  have hND : (A.card : ℝ) * D ≤
      Y ^ 2 + 16 * Y * L + 8 * Y * (D / L) + 4 * D := by
    have hhu := mul_le_mul_of_nonneg_left hu (by positivity : (0 : ℝ) ≤ 12 * Y)
    have hhv := mul_le_mul_of_nonneg_left hv (by positivity : (0 : ℝ) ≤ 8 * Y)
    nlinarith
  have hLD : L / D ≤ 2 / L := by
    apply (div_le_div_iff₀ hD hL).mpr
    field_simp [ne_of_gt hL]
    nlinarith
  have hYL : Y * L / D ≤ 2 * (Y / L) := by
    calc
      Y * L / D = Y * (L / D) := by ring
      _ ≤ Y * (2 / L) := mul_le_mul_of_nonneg_left hLD hY0
      _ = 2 * (Y / L) := by ring
  have hdivide : (A.card : ℝ) ≤
      (Y ^ 2 + 16 * Y * L + 8 * Y * (D / L) + 4 * D) / D := by
    apply (le_div_iff₀ hD).mpr
    simpa [mul_comm] using hND
  calc
    (A.card : ℝ) ≤
        (Y ^ 2 + 16 * Y * L + 8 * Y * (D / L) + 4 * D) / D := hdivide
    _ = Y ^ 2 / D + 16 * (Y * L / D) + 8 * (Y / L) + 4 := by
      field_simp
    _ ≤ Y ^ 2 / D + 40 * (Y / L) + 4 := by nlinarith

end Erdos394
