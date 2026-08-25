import Util.Bernays.LogKernelCutoffs

/-!
# The small-index contribution to the logarithmic kernel
-/

open scoped Classical

namespace Bernays

theorem logarithmicKernel_le_of_le_sqrt {x y : ℝ} (hx : 1 ≤ x) (hy : 0 < y)
    (hyx : y ≤ Real.sqrt x) :
    (1 + (1 / (2 * Real.pi) * Real.log (y / x)) ^ 2)⁻¹ ≤
      (1 + (Real.log x / (4 * Real.pi)) ^ 2)⁻¹ := by
  have hx₀ := zero_lt_one.trans_le hx
  have hlog := Real.log_le_log hy hyx
  rw [Real.log_sqrt hx₀.le] at hlog
  rw [Real.log_div hy.ne' hx₀.ne']
  have hπ : 0 < 2 * Real.pi := by positivity
  have hmul := mul_le_mul_of_nonneg_left (show Real.log y - Real.log x ≤ -(Real.log x / 2) by linarith)
    (inv_nonneg.mpr hπ.le)
  have hlt : (1 / (2 * Real.pi)) * (Real.log y - Real.log x) ≤ -(Real.log x / (4 * Real.pi)) := by
    calc
      _ ≤ (2 * Real.pi)⁻¹ * -(Real.log x / 2) := by simpa only [one_div] using hmul
      _ = _ := by ring
  have hnonneg : 0 ≤ Real.log x / (4 * Real.pi) := div_nonneg (Real.log_nonneg hx) (by positivity)
  apply inv_anti₀ (by positivity)
  nlinarith

theorem logarithmicKernelMass_lower_le {a : ℕ → ℂ} (ha : ∀ n : ℕ, ‖a n‖ ≤ 1)
    {x : ℝ} (hx : 1 ≤ x) :
    logarithmicKernelMass (normLowerPart a (Real.sqrt x)) x ≤
      (1 + Real.log x) * (1 + (Real.log x / (4 * Real.pi)) ^ 2)⁻¹ := by
  let B := (1 + (Real.log x / (4 * Real.pi)) ^ 2)⁻¹
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hroot : Real.sqrt x ≤ x := Real.sqrt_le_self_iff.mpr (Or.inr hx)
  have hxs : 0 ≤ x := zero_le_one.trans hx
  rw [logarithmicKernelMass, tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊)]
  · calc
      _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ)⁻¹ * B := by
        apply Finset.sum_le_sum
        intro n hn
        have hn₀ : 0 < n := (Finset.mem_Icc.mp hn).1
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn₀
        by_cases hsmall : (n : ℝ) < Real.sqrt x
        · rw [normLowerPart, if_pos hsmall]
          simpa only [one_div, logarithmicKernel, B] using
            mul_le_mul (div_le_div_of_nonneg_right (ha n) hnR.le)
              (logarithmicKernel_le_of_le_sqrt hx hnR hsmall.le) (by positivity) (by positivity)
        · rw [normLowerPart, if_neg hsmall, norm_zero, zero_div, zero_mul]
          positivity
      _ = (harmonic ⌊x⌋₊ : ℝ) * B := by
        rw [← Finset.sum_mul, harmonic_eq_sum_Icc, Rat.cast_sum]
        simp only [Rat.cast_inv, Rat.cast_natCast]
      _ ≤ (1 + Real.log x) * B := mul_le_mul_of_nonneg_right (harmonic_floor_le_one_add_log x hx) hB
  · intro n hn
    by_cases hn₀ : n = 0
    · simp only [hn₀, Nat.cast_zero, div_zero, zero_mul]
    · have hn₁ : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn₀
      have hnx : ¬ n ≤ ⌊x⌋₊ := fun h => hn (Finset.mem_Icc.mpr ⟨hn₁, h⟩)
      have hnot : ¬ (n : ℝ) < Real.sqrt x := by
        intro h
        exact hnx ((Nat.le_floor_iff hxs).mpr (h.le.trans hroot))
      rw [normLowerPart, if_neg hnot, norm_zero, zero_div, zero_mul]

theorem logarithmicKernelMass_upper_le {a : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ N : ℕ, cumsum (fun n => ‖a n‖) N ≤
      C * N / (1 + Real.sqrt (Real.log (N : ℝ))))
    {x : ℝ} (hx : 1 < x) :
    logarithmicKernelMass (normUpperPart a (Real.sqrt x)) x ≤
      (2 * C / Real.sqrt (Real.log x)) * (1 + 2 * Real.pi ^ 2) :=
  bound_sum_log' (normUpperPart_cheby_logBound hC hcount hx) hx.le

theorem logarithmicKernelMass_le {a : ℕ → ℂ} (ha : ∀ n : ℕ, ‖a n‖ ≤ 1)
    (hcheby : cheby a) {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ N : ℕ, cumsum (fun n => ‖a n‖) N ≤
      C * N / (1 + Real.sqrt (Real.log (N : ℝ))))
    {x : ℝ} (hx : 1 < x) :
    logarithmicKernelMass a x ≤
      (1 + Real.log x) * (1 + (Real.log x / (4 * Real.pi)) ^ 2)⁻¹ +
        (2 * C / Real.sqrt (Real.log x)) * (1 + 2 * Real.pi ^ 2) := by
  rw [logarithmicKernelMass_split hcheby (Real.sqrt x) (zero_lt_one.trans hx)]
  exact add_le_add (logarithmicKernelMass_lower_le ha hx.le)
    (logarithmicKernelMass_upper_le hC hcount hx)

end Bernays
