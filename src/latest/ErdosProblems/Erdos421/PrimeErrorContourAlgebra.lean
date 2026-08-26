import ErdosProblems.Erdos421.PerronContourAlgebra

/-! # Collecting the error terms after the prime-counting contour choice -/

namespace Erdos421

theorem primeError_contour_expression_bound {x E L H B C A d : ℝ}
    (hx : 0 ≤ x) (hE : 0 ≤ E) (hL : 1 ≤ L) (hH : 0 < H)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hA : 0 ≤ A) (hAH : A * H ≤ x * E)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) :
    (1 / (2 * Real.pi)) *
      (4 * Real.pi * A * (C * H) + 2 * d * (Real.exp 1 * x * (C * H) / H ^ 2) +
        2 * (Real.exp 1 * x * (2 * L + B)) / H) ≤
      x * (4 * Real.pi * C + 2 * Real.exp 1 * C + 2 * Real.exp 1 * (B + 2)) * (E + L / H) := by
  have hL0 : 0 ≤ L := by linarith
  have hc : 1 / (2 * Real.pi) ≤ 1 := (div_le_one (by positivity)).mpr (by
    linarith [Real.pi_gt_three])
  have hS : 0 ≤ 4 * Real.pi * A * (C * H) +
      2 * d * (Real.exp 1 * x * (C * H) / H ^ 2) +
        2 * (Real.exp 1 * x * (2 * L + B)) / H := by positivity
  have hfirst : 4 * Real.pi * A * (C * H) ≤ 4 * Real.pi * C * (x * E) := by
    have hb := mul_le_mul_of_nonneg_left hAH (by positivity : 0 ≤ 4 * Real.pi * C)
    calc
      _ = (4 * Real.pi * C) * (A * H) := by ring
      _ ≤ _ := hb
  have hsecond : 2 * d * (Real.exp 1 * x * (C * H) / H ^ 2) ≤
      2 * Real.exp 1 * x * C / H := by
    calc
      _ ≤ 2 * (Real.exp 1 * x * (C * H) / H ^ 2) := by gcongr; linarith
      _ = _ := by field_simp
  have hLB : 2 * L + B ≤ (B + 2) * L := by nlinarith
  have hthird : 2 * (Real.exp 1 * x * (2 * L + B)) / H ≤
      2 * (Real.exp 1 * x * ((B + 2) * L)) / H := by gcongr
  let C₁ := 4 * Real.pi * C
  let C₂ := 2 * Real.exp 1 * C
  let C₃ := 2 * Real.exp 1 * (B + 2)
  have hC₁ : 0 ≤ C₁ := by dsimp only [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := by dsimp only [C₂]; positivity
  have hC₃ : 0 ≤ C₃ := by dsimp only [C₃]; positivity
  have hfrac : 1 / H ≤ L / H := div_le_div_of_nonneg_right hL hH.le
  calc
    _ ≤ 4 * Real.pi * A * (C * H) + 2 * d * (Real.exp 1 * x * (C * H) / H ^ 2) +
        2 * (Real.exp 1 * x * (2 * L + B)) / H := mul_le_of_le_one_left hS hc
    _ ≤ 4 * Real.pi * C * (x * E) + 2 * Real.exp 1 * x * C / H +
        2 * (Real.exp 1 * x * ((B + 2) * L)) / H :=
      add_le_add (add_le_add hfirst hsecond) hthird
    _ = x * (C₁ * E + C₂ * (1 / H) + C₃ * (L / H)) := by dsimp only [C₁, C₂, C₃]; ring
    _ ≤ x * (C₁ * E + C₂ * (L / H) + C₃ * (L / H)) := by
      apply mul_le_mul_of_nonneg_left _ hx
      exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hfrac hC₂)) le_rfl
    _ ≤ x * (C₁ + C₂ + C₃) * (E + L / H) := by
      have h₁ := mul_nonneg hC₁ (div_nonneg hL0 hH.le)
      have h₂ := mul_nonneg hC₂ hE
      have h₃ := mul_nonneg hC₃ hE
      apply (mul_le_mul_of_nonneg_left (show
        C₁ * E + C₂ * (L / H) + C₃ * (L / H) ≤ (C₁ + C₂ + C₃) * (E + L / H) by
        nlinarith) hx).trans_eq
      ring
    _ = _ := rfl

end Erdos421
