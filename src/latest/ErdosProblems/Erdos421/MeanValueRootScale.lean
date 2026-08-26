import ErdosProblems.Erdos421.MeanValueRecurrence
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # An integer root scale with explicit rounding bounds -/

namespace Erdos421

noncomputable def meanValueRootScale (k N : ℕ) : ℕ :=
  ⌈(N : ℝ) ^ ((k : ℝ)⁻¹)⌉₊

theorem meanValue_real_root_pow {k : ℕ} (hk : 0 < k) (N : ℕ) :
    ((N : ℝ) ^ ((k : ℝ)⁻¹)) ^ k = (N : ℝ) :=
  Real.rpow_inv_natCast_pow (Nat.cast_nonneg N) hk.ne'

theorem one_le_meanValue_real_root (k : ℕ) {N : ℕ} (hN : 0 < N) :
    1 ≤ (N : ℝ) ^ ((k : ℝ)⁻¹) :=
  Real.one_le_rpow (by exact_mod_cast hN) (inv_nonneg.mpr (Nat.cast_nonneg k))

theorem meanValueRootScale_lower (k N : ℕ) :
    (N : ℝ) ^ ((k : ℝ)⁻¹) ≤ (meanValueRootScale k N : ℝ) := Nat.le_ceil _

theorem meanValueRootScale_upper (k : ℕ) {N : ℕ} (hN : 0 < N) :
    (meanValueRootScale k N : ℝ) ≤ 2 * (N : ℝ) ^ ((k : ℝ)⁻¹) := by
  have hroot := one_le_meanValue_real_root k hN
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg N) ((k : ℝ)⁻¹))
  change (meanValueRootScale k N : ℝ) < (N : ℝ) ^ ((k : ℝ)⁻¹) + 1 at hc
  linarith

theorem meanValueRootScale_le_endpoint {k N : ℕ} (hk : 0 < k) (hN : 0 < N) :
    meanValueRootScale k N ≤ N := by
  apply Nat.ceil_le.mpr
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  apply Real.rpow_le_self_of_one_le (by exact_mod_cast hN)
  rw [inv_le_one₀ hkR]
  exact_mod_cast hk

theorem endpoint_le_meanValueRootScale_pow {k : ℕ} (hk : 0 < k) (N : ℕ) :
    N ≤ meanValueRootScale k N ^ k := by
  have h := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg N) ((k : ℝ)⁻¹))
    (meanValueRootScale_lower k N) k
  rw [meanValue_real_root_pow hk N] at h
  exact_mod_cast h

theorem degree_le_meanValueRootScale {k N : ℕ} (hk : 0 < k) (hN : k ^ k ≤ N) :
    k ≤ meanValueRootScale k N := by
  have hroot : (k : ℝ) ≤ (N : ℝ) ^ ((k : ℝ)⁻¹) := by
    apply (pow_le_pow_iff_left₀ (Nat.cast_nonneg k)
      (Real.rpow_nonneg (Nat.cast_nonneg N) ((k : ℝ)⁻¹)) hk.ne').mp
    rw [meanValue_real_root_pow hk N]
    exact_mod_cast hN
  exact_mod_cast hroot.trans (meanValueRootScale_lower k N)

theorem quotient_add_one_real_le {M N : ℕ} (hM : 0 < M) (hMN : M ≤ N) :
    ((N / M + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) / M := by
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hdiv : (1 : ℝ) ≤ (N : ℝ) / M := by
    apply (le_div_iff₀ hMpos).mpr
    simpa only [one_mul] using (Nat.cast_le.mpr hMN : (M : ℝ) ≤ N)
  have hcast : ((N / M : ℕ) : ℝ) ≤ (N : ℝ) / M := Nat.cast_div_le
  push_cast
  rw [mul_div_assoc]
  linarith

end Erdos421
