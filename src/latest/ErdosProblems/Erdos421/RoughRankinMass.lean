import ErdosProblems.Erdos421.RoughEulerRatio

/-! # A relative bound for the summed Buchstab sieve errors -/

namespace Erdos421

theorem exp_neg_mul_le_div {t r : ℝ} (ht : 1 ≤ t) (hr : 1 ≤ r) :
    Real.exp (-t * r) ≤ Real.exp (-t) / r := by
  have hr0 : 0 < r := by linarith
  apply (le_div_iff₀ hr0).mpr
  calc
    _ = Real.exp (Real.log r - t * r) := by
      rw [Real.exp_sub, Real.exp_log hr0, div_eq_mul_inv, ← Real.exp_neg]
      ring
    _ ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by
      have hlog := Real.log_le_sub_one_of_pos hr0
      have hm := mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hr)
      nlinarith)

theorem rankin_euler_factor_bound {z L : ℝ} (hz : 1 < z)
    (hL : 33 ≤ L / Real.log z) {p : ℕ} (hp : p.Prime) (hpz : (p : ℝ) ≤ z) :
    Real.exp (32 * Real.log z / Real.log p) * Real.exp (-L / Real.log p) ≤
      Real.exp (32 - L / Real.log z) * (Real.log p / Real.log z) := by
  have hzlog : 0 < Real.log z := Real.log_pos hz
  have hplog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlog := Real.log_le_log (by exact_mod_cast hp.pos) hpz
  have hr : 1 ≤ Real.log z / Real.log p := (le_div_iff₀ hplog).mpr (by simpa using hlog)
  have hb := exp_neg_mul_le_div (by linarith : 1 ≤ L / Real.log z - 32) hr
  calc
    _ = Real.exp (-(L / Real.log z - 32) * (Real.log z / Real.log p)) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    _ ≤ Real.exp (-(L / Real.log z - 32)) / (Real.log z / Real.log p) := hb
    _ = _ := by rw [neg_sub]; field_simp

theorem rough_rankin_mass_le {z : ℕ} (hz : 2 ≤ z) {L : ℝ}
    (hL : 33 ≤ L / Real.log (z : ℝ)) :
    (∑ p ∈ sievePrimes 0 z,
      roughEulerProduct p / (p : ℝ) * Real.exp (-L / Real.log p)) ≤
        16 * roughEulerProduct z * Real.exp (32 - L / Real.log (z : ℝ)) := by
  have hz1 : (1 : ℝ) < z := by exact_mod_cast (by omega : 1 < z)
  have hzlog : 0 < Real.log (z : ℝ) := Real.log_pos hz1
  have hV := roughEulerProduct_pos z
  have hterm (p : ℕ) (hp : p ∈ sievePrimes 0 z) :
      roughEulerProduct p / (p : ℝ) * Real.exp (-L / Real.log p) ≤
        (roughEulerProduct z * Real.exp (32 - L / Real.log (z : ℝ)) / Real.log z) *
          (Real.log (p : ℝ) / p) := by
    have hprime := (Finset.mem_filter.mp hp).2
    have hpz := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).2.le
    have hratio := (div_le_iff₀ hV).mp (roughEulerProduct_ratio_le_exp hprime.two_le hpz)
    have he := rankin_euler_factor_bound hz1 hL hprime (by exact_mod_cast hpz)
    calc
      _ ≤ (roughEulerProduct z * Real.exp (32 * Real.log (z : ℝ) / Real.log p)) /
          (p : ℝ) * Real.exp (-L / Real.log p) := by
        gcongr
        simpa only [mul_comm] using hratio
      _ = roughEulerProduct z / (p : ℝ) *
          (Real.exp (32 * Real.log (z : ℝ) / Real.log p) * Real.exp (-L / Real.log p)) := by ring
      _ ≤ roughEulerProduct z / (p : ℝ) *
          (Real.exp (32 - L / Real.log (z : ℝ)) * (Real.log p / Real.log (z : ℝ))) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ p ∈ sievePrimes 0 z,
        (roughEulerProduct z * Real.exp (32 - L / Real.log (z : ℝ)) / Real.log z) *
          (Real.log (p : ℝ) / p) := Finset.sum_le_sum hterm
    _ = (roughEulerProduct z * Real.exp (32 - L / Real.log (z : ℝ)) / Real.log z) *
        ∑ p ∈ sievePrimes 0 z, Real.log (p : ℝ) / p := by rw [Finset.mul_sum]
    _ ≤ (roughEulerProduct z * Real.exp (32 - L / Real.log (z : ℝ)) / Real.log z) *
        (16 * Real.log z) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply finite_prime_log_harmonic_le _ (by exact_mod_cast hz)
      intro p hp
      exact ⟨(Finset.mem_filter.mp hp).2,
        by exact_mod_cast (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).2.le⟩
    _ = _ := by field_simp

end Erdos421
