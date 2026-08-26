/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceDyadicCutoff

/-!
# Arithmetic ranges for dyadic source normalization

The interval multiplier is arbitrary and fixed. Cofactor bounds and
integer division are retained exactly, rather than replaced by real
endpoint asymptotics.
-/

namespace Erdos4b.SmoothParameters

noncomputable section

open Filter
open scoped Topology

theorem two_mul_self_le_primaryExponent (a r : ℕ) : 2 * r ≤ primaryExponent a r := by
  calc
    _ ≤ 2 ^ (2 * r) := (2 * r).lt_two_pow_self.le
    _ ≤ 2 ^ (a + 2 * r) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ _ := Nat.le_mul_of_pos_right _ (core_pos r)

theorem residualPrimeFrontier_le_scaled_interval_div
    {a r D m : ℕ} (hm : 0 < m) (hmB : m ≤ D * fullResidualCofactorCutoff r) :
    residualPrimeFrontier a r ≤ D * intervalLength a r / m := by
  apply (Nat.le_div_iff_mul_le hm).mpr
  calc
    _ ≤ residualPrimeFrontier a r * (D * fullResidualCofactorCutoff r) :=
      Nat.mul_le_mul_left _ hmB
    _ = _ := by rw [intervalLength_eq_residualPrimeFrontier_mul_cutoff]; ring

theorem exp_half_ambient_le_residualPrimeFrontier (a r : ℕ) :
    Real.exp (dyadicAmbientScale a r / 2) ≤ (residualPrimeFrontier a r : ℝ) := by
  apply (Real.le_log_iff_exp_le (by exact_mod_cast residualPrimeFrontier_pos a r)).mp
  rw [log_residualPrimeFrontier, Nat.cast_sub (self_le_primaryExponent a r), dyadicAmbientScale_eq]
  have hE : 2 * (r : ℝ) ≤ primaryExponent a r := by
    exact_mod_cast two_mul_self_le_primaryExponent a r
  have h := mul_le_mul_of_nonneg_right hE (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  linarith

theorem source_auxiliary_log_bounds {a r q : ℕ} (hq : 0 < q)
    (hlo : primaryFrontier a r ≤ 2 * q) (hhi : q ≤ primaryFrontier a r) :
    Real.log q ≤ dyadicAmbientScale a r ∧
      dyadicAmbientScale a r / 2 ≤ Real.log q ∧ sourcePreSieveCutoff r < q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlog : dyadicAmbientScale a r ≤ Real.log 2 + Real.log q := by
    have h := Real.log_le_log (by exact_mod_cast primaryFrontier_pos a r)
      (show (primaryFrontier a r : ℝ) ≤ 2 * q by exact_mod_cast hlo)
    rw [Real.log_mul (by norm_num) hqR.ne'] at h
    exact h
  have hE : 2 ≤ primaryExponent a r :=
    (two_le_dyadicCore r).trans (Nat.le_mul_of_pos_left _ (by positivity))
  have hV : 2 * Real.log 2 ≤ dyadicAmbientScale a r := by
    rw [dyadicAmbientScale_eq]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hE) (Real.log_nonneg (by norm_num))
  refine ⟨Real.log_le_log hqR (by exact_mod_cast hhi), by linarith, ?_⟩
  have hX : primaryExponent a r < primaryFrontier a r :=
    (primaryExponent a r).lt_two_pow_self
  have htwo := two_mul_self_le_primaryExponent a r
  have hw : sourcePreSieveCutoff r ≤ r := Nat.div_le_self r 100
  omega

theorem eventually_smoothExponent_le_primaryExponent (a : ℕ) :
    ∀ᶠ r in atTop, smoothExponent r ≤ primaryExponent a r := by
  filter_upwards [eventually_dyadicCompanionScale_small a 1] with r hr
  have hV := one_le_dyadicAmbientScale a r
  simp only [Nat.cast_one, one_mul] at hr
  have hLE : dyadicCompanionScale r ≤ dyadicAmbientScale a r := by linarith
  rw [dyadicCompanionScale_eq, dyadicAmbientScale_eq] at hLE
  exact_mod_cast (mul_le_mul_iff_left₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp hLE

theorem eventually_fixed_mul_nat_le_twoPow (D : ℕ) :
    ∀ᶠ n : ℕ in atTop, D * n ≤ 2 ^ n := by
  have hbase : Tendsto (fun n : ℕ ↦ (n : ℝ) / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [pow_one] using tendsto_pow_const_div_const_pow_of_one_lt 1
      (by norm_num : (1 : ℝ) < 2)
  have h : Tendsto (fun n : ℕ ↦ (D : ℝ) * ((n : ℝ) / (2 : ℝ) ^ n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hbase.const_mul (D : ℝ)
  filter_upwards [h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn
  rw [← mul_div_assoc, div_lt_one (by positivity)] at hn
  exact_mod_cast hn.le

theorem eventually_scaled_cofactor_cutoff_le_primary (a D : ℕ) :
    ∀ᶠ r in atTop, D * fullResidualCofactorCutoff r ≤ primaryFrontier a r := by
  have hE : Tendsto (primaryExponent a) atTop atTop :=
    tendsto_atTop_mono (self_le_primaryExponent a) tendsto_id
  filter_upwards [eventually_smoothExponent_le_primaryExponent a,
    hE.eventually (eventually_fixed_mul_nat_le_twoPow D)] with r hS hlarge
  have hB : fullResidualCofactorCutoff r = smoothExponent r := by
    unfold fullResidualCofactorCutoff smoothExponent rankinDenominator
    ring
  rw [hB]
  exact (Nat.mul_le_mul_left D hS).trans hlarge

end

end Erdos4b.SmoothParameters
