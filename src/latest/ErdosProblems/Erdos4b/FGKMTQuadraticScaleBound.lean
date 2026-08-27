/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTQuadraticModulusScale

/-! # A polynomial envelope for the exact finite quadratic error -/

namespace Erdos4b.FGKMT

noncomputable section

theorem sieveProfileScale_le_square (k : ℕ) : sieveProfileScale k ≤ (k : ℝ) ^ 2 := by
  simpa only [sieveProfileScale, pow_two] using
    mul_le_mul_of_nonneg_left (Real.log_le_self (Nat.cast_nonneg k)) (Nat.cast_nonneg k)

theorem sieveQuadraticErrorScale_le_polynomial {k M R x : ℕ} {A b : ℝ}
    (hA : 0 ≤ A) (hb : 0 < b) (hL : 0 < Real.log (x : ℝ))
    (hmod : modulusLogScale (M * R ^ (2 * k)) ≤ A * dimensionLogLossScale x)
    (hR : b * Real.log (x : ℝ) ≤ Real.log (R : ℝ)) :
    sieveQuadraticErrorScale k M R ≤
      ((A ^ 3 + 1) / b) * (k : ℝ) ^ 5 * dimensionLogLossScale x ^ 3 / Real.log (x : ℝ) := by
  let T := sieveProfileScale k
  let V := modulusLogScale (M * R ^ (2 * k))
  let S := dimensionLogLossScale x
  have hT0 : 0 ≤ T := mul_nonneg (Nat.cast_nonneg k) (Real.log_natCast_nonneg k)
  have hV0 : 0 ≤ V := zero_le_one.trans (one_le_modulusLogScale _)
  have hS1 : 1 ≤ S := one_le_dimensionLogLossScale x
  have hS0 : 0 ≤ S := zero_le_one.trans hS1
  have hT : T ≤ (k : ℝ) ^ 2 := sieveProfileScale_le_square k
  have hV : V ≤ A * S := hmod
  have hnum1 : (k : ℝ) * T ^ 2 * V ^ 3 ≤ A ^ 3 * (k : ℝ) ^ 5 * S ^ 3 := by
    calc
      _ ≤ (k : ℝ) * ((k : ℝ) ^ 2) ^ 2 * (A * S) ^ 3 := by gcongr
      _ = _ := by ring
  have hnum2 : (k : ℝ) ^ 3 * T ≤ (k : ℝ) ^ 5 * S ^ 3 := by
    calc
      _ ≤ (k : ℝ) ^ 3 * (k : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hT (by positivity)
      _ = (k : ℝ) ^ 5 * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (one_le_pow₀ hS1) (by positivity)
  have hRpos : 0 < Real.log (R : ℝ) := (mul_pos hb hL).trans_le hR
  calc
    _ = ((k : ℝ) * T ^ 2 * V ^ 3 + (k : ℝ) ^ 3 * T) / Real.log (R : ℝ) := by
      dsimp only [sieveQuadraticErrorScale, T, V]
      ring
    _ ≤ ((A ^ 3 + 1) * (k : ℝ) ^ 5 * S ^ 3) / Real.log (R : ℝ) :=
      div_le_div_of_nonneg_right (by nlinarith) hRpos.le
    _ ≤ ((A ^ 3 + 1) * (k : ℝ) ^ 5 * S ^ 3) / (b * Real.log (x : ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hb hL) hR
    _ = _ := by ring

theorem fifthPower_le_log_rpow_of_dimension {x k : ℕ}
    (hk : (k : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ)) :
    (k : ℝ) ^ 5 ≤ Real.log (x : ℝ) ^ (1 / 2 : ℝ) := by
  calc
    _ ≤ (Real.log (x : ℝ) ^ (1 / 10 : ℝ)) ^ 5 :=
      pow_le_pow_left₀ (Nat.cast_nonneg k) hk 5
    _ = (Real.log (x : ℝ) ^ (1 / 10 : ℝ)) ^ ((5 : ℕ) : ℝ) :=
      (Real.rpow_natCast _ 5).symm
    _ = _ := by rw [← Real.rpow_mul (Real.log_natCast_nonneg x)]; norm_num

theorem sieveQuadraticErrorScale_le_logEnvelope {k M R x : ℕ} {A b : ℝ}
    (hA : 0 ≤ A) (hb : 0 < b) (hL : 0 < Real.log (x : ℝ))
    (hmod : modulusLogScale (M * R ^ (2 * k)) ≤ A * dimensionLogLossScale x)
    (hR : b * Real.log (x : ℝ) ≤ Real.log (R : ℝ))
    (hk : (k : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ)) :
    sieveQuadraticErrorScale k M R ≤
      ((A ^ 3 + 1) / b) * dimensionLogLossScale x ^ 3 *
        Real.log (x : ℝ) ^ (-1 / 2 : ℝ) := by
  calc
    _ ≤ ((A ^ 3 + 1) / b) * (k : ℝ) ^ 5 *
        dimensionLogLossScale x ^ 3 / Real.log (x : ℝ) :=
      sieveQuadraticErrorScale_le_polynomial hA hb hL hmod hR
    _ ≤ ((A ^ 3 + 1) / b) * Real.log (x : ℝ) ^ (1 / 2 : ℝ) *
        dimensionLogLossScale x ^ 3 / Real.log (x : ℝ) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (fifthPower_le_log_rpow_of_dimension hk) (by positivity))
          (pow_nonneg (zero_le_one.trans (one_le_dimensionLogLossScale x)) 3)) hL.le
    _ = _ := by
      have heq : Real.log (x : ℝ) ^ (1 / 2 : ℝ) / Real.log (x : ℝ) =
          Real.log (x : ℝ) ^ (-1 / 2 : ℝ) := by
        rw [show (-1 / 2 : ℝ) = 1 / 2 - 1 by norm_num, Real.rpow_sub hL, Real.rpow_one]
      calc
        _ = ((A ^ 3 + 1) / b) * dimensionLogLossScale x ^ 3 *
            (Real.log (x : ℝ) ^ (1 / 2 : ℝ) / Real.log (x : ℝ)) := by ring
        _ = _ := by rw [heq]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sieveQuadraticErrorScale_le_logEnvelope
