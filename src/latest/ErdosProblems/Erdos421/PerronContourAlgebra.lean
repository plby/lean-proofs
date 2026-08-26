import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! # Collecting the three error terms in the chosen Perron contour -/

namespace Erdos421

theorem perron_contour_expression_bound {x E L T B Q A Z d : ℝ}
    (hx : 0 ≤ x) (hE : 0 ≤ E) (hL : 1 ≤ L) (hT : 1 ≤ T) (hB : 0 ≤ B)
    (hQ : 0 ≤ Q) (hA : 0 ≤ A) (hAx : A ≤ x * E) (hZ : 0 ≤ Z)
    (hZQ : Z ≤ Q * L ^ 2) (hd : 0 ≤ d) (hd2 : d ≤ 2) :
    (1 / (2 * Real.pi)) *
      (4 * Real.pi * A * Z + 2 * d * (Real.exp 1 * x * Z / (T / 2) ^ 2) +
        2 * (Real.exp 1 * x * (L + B)) / (T / 2)) ≤
      x * (4 * Real.pi * Q + 16 * Real.exp 1 * Q + 4 * Real.exp 1 * (B + 1)) *
        (E * L ^ 2 + L ^ 2 / T) := by
  have hTp : 0 < T := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hc : 1 / (2 * Real.pi) ≤ 1 := (div_le_one (by positivity)).mpr (by
    linarith [Real.pi_gt_three])
  have hS : 0 ≤ 4 * Real.pi * A * Z +
      2 * d * (Real.exp 1 * x * Z / (T / 2) ^ 2) +
        2 * (Real.exp 1 * x * (L + B)) / (T / 2) := by positivity
  have hfirst : 4 * Real.pi * A * Z ≤ 4 * Real.pi * (x * E) * (Q * L ^ 2) := by
    gcongr
  have hsecond : 2 * d * (Real.exp 1 * x * Z / (T / 2) ^ 2) ≤
      4 * (Real.exp 1 * x * (Q * L ^ 2) / (T / 2) ^ 2) := by
    gcongr
    linarith
  have hT2 : T ≤ T ^ 2 := by nlinarith
  have hfrac : L ^ 2 / T ^ 2 ≤ L ^ 2 / T :=
    div_le_div_of_nonneg_left (sq_nonneg L) hTp hT2
  have hLB : L + B ≤ (B + 1) * L ^ 2 := by
    have h := mul_nonneg hB (show 0 ≤ L ^ 2 - 1 by nlinarith)
    nlinarith
  have htail : (L + B) / T ≤ (B + 1) * (L ^ 2 / T) := by
    have h := div_le_div_of_nonneg_right hLB hTp.le
    simpa only [mul_div_assoc] using h
  let C₁ := 4 * Real.pi * Q
  let C₂ := 16 * Real.exp 1 * Q
  let C₃ := 4 * Real.exp 1 * (B + 1)
  have hC₁ : 0 ≤ C₁ := by dsimp only [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := by dsimp only [C₂]; positivity
  have hC₃ : 0 ≤ C₃ := by dsimp only [C₃]; positivity
  calc
    _ ≤ 4 * Real.pi * A * Z + 2 * d * (Real.exp 1 * x * Z / (T / 2) ^ 2) +
        2 * (Real.exp 1 * x * (L + B)) / (T / 2) := mul_le_of_le_one_left hS hc
    _ ≤ 4 * Real.pi * (x * E) * (Q * L ^ 2) +
        4 * (Real.exp 1 * x * (Q * L ^ 2) / (T / 2) ^ 2) +
          2 * (Real.exp 1 * x * (L + B)) / (T / 2) :=
      add_le_add (add_le_add hfirst hsecond) le_rfl
    _ = x * (C₁ * (E * L ^ 2) + C₂ * (L ^ 2 / T ^ 2) +
        4 * Real.exp 1 * ((L + B) / T)) := by dsimp only [C₁, C₂]; field_simp; ring
    _ ≤ x * (C₁ * (E * L ^ 2) + C₂ * (L ^ 2 / T) + C₃ * (L ^ 2 / T)) := by
      apply mul_le_mul_of_nonneg_left _ hx
      apply add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hfrac hC₂))
      exact (mul_le_mul_of_nonneg_left htail (by positivity)).trans_eq
        (by dsimp only [C₃]; ring)
    _ ≤ x * (C₁ + C₂ + C₃) * (E * L ^ 2 + L ^ 2 / T) := by
      have h₁ := mul_nonneg hC₁ (div_nonneg (sq_nonneg L) hTp.le)
      have h₂ := mul_nonneg hC₂ (mul_nonneg hE (sq_nonneg L))
      have h₃ := mul_nonneg hC₃ (mul_nonneg hE (sq_nonneg L))
      apply (mul_le_mul_of_nonneg_left (show
        C₁ * (E * L ^ 2) + C₂ * (L ^ 2 / T) + C₃ * (L ^ 2 / T) ≤
          (C₁ + C₂ + C₃) * (E * L ^ 2 + L ^ 2 / T) by nlinarith) hx).trans_eq
      ring
    _ = _ := rfl

end Erdos421
