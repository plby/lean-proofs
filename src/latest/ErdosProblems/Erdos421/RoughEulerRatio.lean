import ErdosProblems.Erdos421.RoughEulerProduct
import ErdosProblems.Erdos421.PrimeLogHarmonicBound

/-! # Elementary uniform comparison of sieve Euler products -/

namespace Erdos421

theorem prime_euler_factor_inv_le_exp {p : ℕ} (hp : p.Prime) :
    (1 - (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (2 / (p : ℝ)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have ha : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hb : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith : 0 < (p : ℝ))]
    linarith
  calc
    _ ≤ 1 + 2 * (p : ℝ)⁻¹ := by
      rw [inv_eq_one_div, div_le_iff₀ (by linarith : 0 < 1 - (p : ℝ)⁻¹)]
      nlinarith
    _ ≤ Real.exp (2 * (p : ℝ)⁻¹) := by
      simpa only [add_comm] using Real.add_one_le_exp (2 * (p : ℝ)⁻¹)
    _ = _ := by rw [div_eq_mul_inv]

theorem finite_prime_harmonic_interval_le (S : Finset ℕ) {w z : ℝ}
    (hw : 1 < w) (hz : 2 ≤ z)
    (hS : ∀ p ∈ S, p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) ≤ z) :
    (∑ p ∈ S, (p : ℝ)⁻¹) ≤ 16 * Real.log z / Real.log w := by
  have hlog : 0 < Real.log w := Real.log_pos hw
  apply (le_div_iff₀ hlog).mpr
  calc
    _ = ∑ p ∈ S, Real.log w / (p : ℝ) := by rw [Finset.sum_mul]; simp [div_eq_mul_inv, mul_comm]
    _ ≤ ∑ p ∈ S, Real.log (p : ℝ) / (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      apply div_le_div_of_nonneg_right
        (Real.log_le_log (by linarith) (hS p hp).2.1) (Nat.cast_nonneg p)
    _ ≤ _ := finite_prime_log_harmonic_le S hz (fun p hp ↦ ⟨(hS p hp).1, (hS p hp).2.2⟩)

theorem roughEulerProduct_split {w z : ℕ} (hwz : w ≤ z) :
    roughEulerProduct w * (∏ p ∈ sievePrimes w z, (1 - (p : ℝ)⁻¹)) =
      roughEulerProduct z := by
  simpa only [roughEulerProduct, sievePrimes, Finset.prod_filter] using
    Finset.prod_Ico_consecutive (fun p : ℕ ↦ if p.Prime then (1 - (p : ℝ)⁻¹) else 1)
      (Nat.zero_le w) hwz

theorem roughEulerProduct_ratio {w z : ℕ} (hwz : w ≤ z) :
    roughEulerProduct w / roughEulerProduct z =
      ∏ p ∈ sievePrimes w z, (1 - (p : ℝ)⁻¹)⁻¹ := by
  rw [Finset.prod_inv_distrib, ← roughEulerProduct_split hwz]
  exact div_mul_cancel_left₀ (roughEulerProduct_pos w).ne' _

theorem roughEulerProduct_ratio_le_exp {w z : ℕ} (hw : 2 ≤ w) (hwz : w ≤ z) :
    roughEulerProduct w / roughEulerProduct z ≤
      Real.exp (32 * Real.log (z : ℝ) / Real.log (w : ℝ)) := by
  have hz : (2 : ℝ) ≤ z := by exact_mod_cast hw.trans hwz
  have hw1 : (1 : ℝ) < w := by exact_mod_cast (by omega : 1 < w)
  have hsum := finite_prime_harmonic_interval_le (sievePrimes w z) hw1 hz (by
    intro p hp
    obtain ⟨hinterval, hprime⟩ := Finset.mem_filter.mp hp
    obtain ⟨hwp, hpz⟩ := Finset.mem_Ico.mp hinterval
    exact ⟨hprime, by exact_mod_cast hwp, by exact_mod_cast hpz.le⟩)
  rw [roughEulerProduct_ratio hwz]
  calc
    _ ≤ ∏ p ∈ sievePrimes w z, Real.exp (2 / (p : ℝ)) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp1 : (1 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
        exact inv_nonneg.mpr (sub_nonneg.mpr
          ((inv_lt_one₀ (by linarith)).mpr hp1).le)
      · intro p hp
        exact prime_euler_factor_inv_le_exp (Finset.mem_filter.mp hp).2
    _ = Real.exp (2 * ∑ p ∈ sievePrimes w z, (p : ℝ)⁻¹) := by
      rw [Finset.mul_sum, Real.exp_sum]
      simp only [div_eq_mul_inv]
    _ ≤ Real.exp (2 * (16 * Real.log (z : ℝ) / Real.log (w : ℝ))) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum (by norm_num))
    _ = _ := by congr 1; ring

end Erdos421
