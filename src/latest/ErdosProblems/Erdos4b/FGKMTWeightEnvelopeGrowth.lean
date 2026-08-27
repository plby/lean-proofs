/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPreSieveRange
import ErdosProblems.Erdos4b.FGKMTCommonWeightBound

/-! # Subpower losses in the literal weight and endpoint-error bounds -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem log_one_add_log_radius_le_scale {R x : ℕ} (hR : 0 < R) (hRx : R ≤ x) :
    Real.log (1 + Real.log (R : ℝ)) ≤ dimensionLogLossScale x := by
  have hlog : Real.log (R : ℝ) ≤ Real.log (x : ℝ) :=
    Real.log_le_log (by exact_mod_cast hR) (by exact_mod_cast hRx)
  have h := Real.log_le_log (by positivity : 0 < 1 + Real.log (R : ℝ))
    (add_le_add le_rfl hlog)
  dsimp only [dimensionLogLossScale]
  linarith

theorem dimensionWeightLogFactor_le_exp {x k B R : ℕ}
    (hk : 1 ≤ k) (hR : 0 < R) (hRx : R ≤ x) :
    (dimensionPreSieveModulus k B : ℝ) * (1 + Real.log (R : ℝ)) ^ (2 * k) ≤
      Real.exp (10 * (k : ℝ) ^ 2 * dimensionLogLossScale x) := by
  let S := dimensionLogLossScale x
  have hS1 : 1 ≤ S := one_le_dimensionLogLossScale x
  have hS0 : 0 ≤ S := zero_le_one.trans hS1
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog := log_one_add_log_radius_le_scale hR hRx
  have hVpos : 0 < 1 + Real.log (R : ℝ) := by positivity
  have hpow : (1 + Real.log (R : ℝ)) ^ (2 * k) ≤ Real.exp (2 * (k : ℝ) * S) := by
    calc
      _ = Real.exp (((2 * k : ℕ) : ℝ) * Real.log (1 + Real.log (R : ℝ))) := by
        rw [Real.exp_nat_mul, Real.exp_log hVpos]
      _ ≤ _ := by
        apply Real.exp_monotone
        push_cast
        exact mul_le_mul_of_nonneg_left hlog (by positivity)
  have hcost : 8 * (k : ℝ) ^ 2 + 2 * (k : ℝ) * S ≤ 10 * (k : ℝ) ^ 2 * S := by
    have hk2 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    have hfirst := mul_le_mul_of_nonneg_left hS1 (by positivity : 0 ≤ 8 * (k : ℝ) ^ 2)
    have hsecond := mul_le_mul_of_nonneg_right hk2 hS0
    nlinarith
  calc
    _ ≤ Real.exp (8 * (k : ℝ) ^ 2) * Real.exp (2 * (k : ℝ) * S) :=
      mul_le_mul (dimensionPreSieveModulus_le_exp k B) hpow (by positivity) (Real.exp_pos _).le
    _ ≤ _ := by rw [← Real.exp_add]; exact Real.exp_monotone hcost

theorem dimensionSieveRadius_cube_le_rpow (x : ℕ) :
    (dimensionSieveRadius x : ℝ) ^ 3 ≤ (x : ℝ) ^ (1 / 3 : ℝ) := by
  calc
    _ ≤ ((x : ℝ) ^ (1 / 9 : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (dimensionSieveRadius_le_rpow x) 3
    _ = ((x : ℝ) ^ (1 / 9 : ℝ)) ^ ((3 : ℕ) : ℝ) := (Real.rpow_natCast _ 3).symm
    _ = _ := by rw [← Real.rpow_mul (Nat.cast_nonneg x)]; norm_num

theorem eventually_dimensionWeightEnvelope_le_rpow {e : ℝ} (he : 0 < e) :
    ∀ᶠ x : ℕ in atTop, ∀ k B : ℕ, 1 ≤ k →
      (k : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) →
      (dimensionPreSieveModulus k B : ℝ) *
        ((dimensionSieveRadius x : ℝ) ^ 3 *
          (1 + Real.log (dimensionSieveRadius x : ℝ)) ^ (2 * k)) ≤
        (x : ℝ) ^ (1 / 3 + e : ℝ) := by
  filter_upwards [eventually_dimensionSieveRadius_window,
    eventually_uniform_squareDimension_loss (by norm_num : (0 : ℝ) < 10)
      (by norm_num : (0 : ℝ) < 1), eventually_exp_mul_sqrtLog_le_rpow 1 he,
    eventually_ge_atTop (1 : ℕ)] with x hR hcost heX hx
  intro k B hk hdim
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hV := dimensionWeightLogFactor_le_exp (B := B) hk (by omega) hR.2.1
  have hcost' := hcost k hk hdim
  simp only [one_mul] at hcost' heX
  calc
    _ = ((dimensionPreSieveModulus k B : ℝ) *
        (1 + Real.log (dimensionSieveRadius x : ℝ)) ^ (2 * k)) *
        (dimensionSieveRadius x : ℝ) ^ 3 := by ring
    _ ≤ Real.exp (10 * (k : ℝ) ^ 2 * dimensionLogLossScale x) * (x : ℝ) ^ (1 / 3 : ℝ) :=
      mul_le_mul hV (dimensionSieveRadius_cube_le_rpow x) (by positivity) (Real.exp_pos _).le
    _ ≤ Real.exp (Real.sqrt (Real.log (x : ℝ))) * (x : ℝ) ^ (1 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right (Real.exp_monotone hcost') (by positivity)
    _ ≤ (x : ℝ) ^ e * (x : ℝ) ^ (1 / 3 : ℝ) := mul_le_mul_of_nonneg_right heX (by positivity)
    _ = _ := by rw [← Real.rpow_add hxpos]; congr 1; ring

theorem eventually_commonPrimeSieveWeight_pointwise {e : ℝ} (he : 0 < e) :
    ∀ᶠ x : ℕ in atTop, ∀ k B : ℕ, 2 ≤ k →
      (k : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) →
      ∀ y : ℝ, ∀ h : Fin k → ℕ, ∀ p : ℕ, ∀ n : ℤ,
        commonPrimeSieveWeight k (dimensionPreSieveModulus k B)
          (B * dimensionPreSieveModulus k B) (dimensionSieveRadius x) y h p n ≤
            (x : ℝ) ^ (1 / 3 + e : ℝ) := by
  filter_upwards [eventually_dimensionSieveRadius_window,
    eventually_dimensionWeightEnvelope_le_rpow he] with x hR hbound
  intro k B hk hdim y h p n
  have hW1 : (1 : ℝ) ≤ dimensionPreSieveModulus k B := by
    exact_mod_cast dimensionPreSieveModulus_pos k B
  have hE0 : 0 ≤ (dimensionSieveRadius x : ℝ) ^ 3 *
      (1 + Real.log (dimensionSieveRadius x : ℝ)) ^ (2 * k) := by positivity
  calc
    _ ≤ (dimensionSieveRadius x : ℝ) ^ 3 *
        (1 + Real.log (dimensionSieveRadius x : ℝ)) ^ (2 * k) :=
      commonPrimeSieveWeight_le_radius_envelope hk hR.1
        (fun _q hq hqk => small_prime_dvd_dimensionPreSieve hq hqk) y h p n
    _ ≤ (dimensionPreSieveModulus k B : ℝ) *
        ((dimensionSieveRadius x : ℝ) ^ 3 *
          (1 + Real.log (dimensionSieveRadius x : ℝ)) ^ (2 * k)) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hW1 hE0
    _ ≤ _ := hbound k B (by omega) hdim

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.eventually_dimensionWeightEnvelope_le_rpow
#print axioms Erdos4b.FGKMT.eventually_commonPrimeSieveWeight_pointwise
