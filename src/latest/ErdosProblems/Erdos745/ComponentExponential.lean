import ErdosProblems.Erdos745.ComponentCountUpper
import Mathlib.Data.Nat.Choose.Bounds

/-! # Exponential component-count estimates in the supercritical model -/

namespace Erdos745

noncomputable section

theorem choose_mul_treeCount_le {n k : ℕ} (hk : 0 < k) :
    (n.choose k : ℝ) * labelledTreeCount k ≤ (n : ℝ) ^ k * Real.exp k := by
  have hτ : (labelledTreeCount k : ℝ) ≤ (k : ℝ) ^ k := by
    exact_mod_cast labelledTreeCount_upper hk
  calc
    _ ≤ ((n : ℝ) ^ k / k.factorial) * (k : ℝ) ^ k :=
      mul_le_mul (Nat.choose_le_pow_div k n) hτ (Nat.cast_nonneg _) (by positivity)
    _ = (n : ℝ) ^ k * ((k : ℝ) ^ k / k.factorial) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg k) k) (by positivity)

theorem absence_pow_le_exp {p : ℝ} (hp : p ≤ 1) (m : ℕ) :
    (1 - p) ^ m ≤ Real.exp (-p * m) := by
  have hbase : 1 - p ≤ Real.exp (-p) := by
    have h := Real.add_one_le_exp (-p)
    linarith
  calc
    _ ≤ Real.exp (-p) ^ m := pow_le_pow_left₀ (sub_nonneg.mpr hp) hbase m
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem component_prefactor_identity {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    {lam : ℝ} (hlam : 0 < lam) :
    (n : ℝ) ^ k * Real.exp k * (lam / n) ^ (k - 1) =
      (n : ℝ) / lam * Real.exp ((1 + Real.log lam) * k) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpow : (n : ℝ) ^ k * (lam / n) ^ (k - 1) =
      (n : ℝ) / lam * lam ^ k := by
    have hk1 : 1 ≤ k := hk
    have hnPow : (n : ℝ) ^ k = (n : ℝ) ^ (k - 1) * n := by
      conv_lhs => arg 2; rw [← Nat.sub_add_cancel hk1]
      rw [pow_succ]
    have hlamPow : lam ^ k = lam ^ (k - 1) * lam := by
      conv_lhs => arg 2; rw [← Nat.sub_add_cancel hk1]
      rw [pow_succ]
    rw [hnPow, hlamPow, div_pow]
    field_simp
  have hexp : Real.exp ((1 + Real.log lam) * k) = Real.exp k * lam ^ k := by
    rw [add_mul, one_mul, Real.exp_add, mul_comm (Real.log lam), Real.exp_nat_mul,
      Real.exp_log hlam]
  rw [hexp]
  calc
    _ = ((n : ℝ) ^ k * (lam / n) ^ (k - 1)) * Real.exp k := by ring
    _ = _ := by rw [hpow]; ring

theorem componentUpper_le_exp {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n)
    {lam : ℝ} (hlam : 0 < lam) (hlamn : lam ≤ n) :
    componentUpper lam n k ≤ (n : ℝ) / lam *
      Real.exp (-logarithmicDecay lam * k + lam * (k : ℝ) ^ 2 / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 ≤ lam / n := by positivity
  have hp1 : lam / n ≤ 1 := (div_le_one hnR).mpr hlamn
  have hcut := absence_pow_le_exp hp1 (k * (n - k))
  have hcutCast : ((k * (n - k) : ℕ) : ℝ) = (k : ℝ) * ((n : ℝ) - k) := by
    rw [Nat.cast_mul, Nat.cast_sub hkn]
  rw [hcutCast] at hcut
  unfold componentUpper
  rw [coe_edgeProbability hlam.le hn hlamn]
  calc
    _ ≤ ((n : ℝ) ^ k * Real.exp k) * (lam / n) ^ (k - 1) *
        Real.exp (-(lam / n) * ((k : ℝ) * ((n : ℝ) - k))) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right (choose_mul_treeCount_le hk)
        (pow_nonneg hp _)) hcut (pow_nonneg (sub_nonneg.mpr hp1) _) (by positivity)
    _ = (n : ℝ) / lam * Real.exp (((1 + Real.log lam) * k) -
        (lam / n) * ((k : ℝ) * ((n : ℝ) - k))) := by
      rw [component_prefactor_identity hn hk hlam, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ = _ := by
      congr 2
      unfold logarithmicDecay
      field_simp
      ring

theorem componentUpper_le_exp_linear {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hkn : k ≤ n) {lam δ : ℝ} (hlam : 0 < lam) (hlamn : lam ≤ n)
    (hkδ : (k : ℝ) ≤ δ * n) :
    componentUpper lam n k ≤ (n : ℝ) / lam *
      Real.exp (-(logarithmicDecay lam - lam * δ) * k) := by
  apply (componentUpper_le_exp hn hk hkn hlam hlamn).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h : lam * (k : ℝ) ^ 2 / n ≤ lam * δ * k := by
    rw [div_le_iff₀ hnR]
    have hm := mul_le_mul_of_nonneg_left hkδ (mul_nonneg hlam.le (Nat.cast_nonneg k))
    nlinarith
  nlinarith

end

end Erdos745
