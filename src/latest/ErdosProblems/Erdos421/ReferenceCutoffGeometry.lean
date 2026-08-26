import ErdosProblems.Erdos421.RoundedTransferSupport
import ErdosProblems.Erdos421.RoughCofactorParameters

/-! # Elementary scale and support bounds for the actual reference windows -/

namespace Erdos421

theorem nat_div_real_lt_add_one (B : ℕ) {p : ℕ} (hp : 0 < p) :
    (B : ℝ) / p < (B / p : ℕ) + 1 := by
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hrem := Nat.mod_lt B hp
  have hdiv := Nat.mod_add_div B p
  have hnat : B < p * (B / p + 1) := by nlinarith
  apply (div_lt_iff₀ hpr).mpr
  have hcast : (B : ℝ) < (p : ℝ) * ((B / p : ℕ) + 1) := by exact_mod_cast hnat
  simpa only [mul_comm] using hcast

theorem reference_parent_endpoint {X x δ : ℝ} (hx : 0 ≤ x) (hxX : x ≤ 2 * X)
    (hδ : δ ≤ 1 / 2) : (1 + δ) * x ≤ 3 * X := by
  have h := mul_le_mul_of_nonneg_right hδ hx
  nlinarith

theorem reference_cofactor_scale_lower {X x p : ℝ} (hX : 1 ≤ X) (hXx : X ≤ x)
    (hp : 0 < p) (hpX : p ≤ X ^ (51 / 100 : ℝ)) : X ^ (9 / 20 : ℝ) ≤ x / p := by
  have hXp : 0 < X := by linarith
  apply (le_div_iff₀ hp).mpr
  calc
    _ ≤ X ^ (9 / 20 : ℝ) * X ^ (51 / 100 : ℝ) :=
      mul_le_mul_of_nonneg_left hpX (Real.rpow_nonneg hXp.le _)
    _ = X ^ (24 / 25 : ℝ) := by rw [← Real.rpow_add hXp]; norm_num
    _ ≤ X := Real.rpow_le_self_of_one_le hX (by norm_num)
    _ ≤ x := hXx

theorem intermediate_square_le_reference_scale {X : ℝ} (hX : 1 ≤ X)
    (hZ : (intermediatePrimeCutoff X : ℝ) ≤ X ^ (79 / 400 : ℝ)) :
    (intermediatePrimeCutoff X : ℝ) ^ 2 ≤ X ^ (9 / 20 : ℝ) := by
  have hXp : 0 < X := by linarith
  calc
    _ ≤ (X ^ (79 / 400 : ℝ)) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hZ 2
    _ = X ^ (79 / 200 : ℝ) := by rw [← Real.rpow_mul_natCast hXp.le]; norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hX (by norm_num)

theorem reference_main_argument_range {X x : ℝ} (hX : 1 < X) (hXx : X ≤ x)
    (hxX : x ≤ 2 * X) (hZ2 : 2 ≤ intermediatePrimeCutoff X)
    (hZ : (intermediatePrimeCutoff X : ℝ) ≤ X ^ (79 / 400 : ℝ))
    (hZpow : 3 * X ≤ (intermediatePrimeCutoff X : ℝ) ^ 6) :
    Real.log x / Real.log (intermediatePrimeCutoff X) ∈ Set.Icc (5 / 2 : ℝ) 6 := by
  have hXp : 0 < X := by linarith
  have hxp : 0 < x := hXp.trans_le hXx
  have hLX := Real.log_pos hX
  have hZ1 : (1 : ℝ) < intermediatePrimeCutoff X :=
    by exact_mod_cast (show 1 < intermediatePrimeCutoff X by omega)
  have hZp : (0 : ℝ) < intermediatePrimeCutoff X := by linarith
  have hLZ := Real.log_pos hZ1
  have hlogXx := Real.log_le_log hXp hXx
  have hlogZ := Real.log_le_log hZp hZ
  rw [Real.log_rpow hXp] at hlogZ
  have hxZpow : x ≤ (intermediatePrimeCutoff X : ℝ) ^ 6 := by linarith
  have hlogupper := log_le_nat_power_scale hxp hxZpow
  norm_num only [Nat.cast_ofNat] at hlogupper
  exact ⟨(le_div_iff₀ hLZ).mpr (by nlinarith), (div_le_iff₀ hLZ).mpr hlogupper⟩

end Erdos421
