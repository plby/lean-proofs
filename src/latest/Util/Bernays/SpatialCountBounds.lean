import Util.Bernays.LogKernelCutoffs

/-!
# Uniform counting bounds on fixed multiples of a moving endpoint
-/

namespace Bernays

theorem count_mul_sqrt_log_le {A : ℕ → ℝ} (hA : ∀ N : ℕ, A N ≤ N)
    {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ N : ℕ, A N ≤ C * N / (1 + Real.sqrt (Real.log (N : ℝ))))
    {b x : ℝ} (hb : 0 ≤ b) (hx : 1 < x) {N : ℕ} (hN : (N : ℝ) ≤ b * x) :
    A N * Real.sqrt (Real.log x) ≤ (1 + 2 * C * b) * x := by
  have hx₀ : 0 < x := zero_lt_one.trans hx
  have hsx : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr (Real.log_pos hx)
  by_cases hsmall : (N : ℝ) ≤ Real.sqrt x
  · have hlog : Real.sqrt (Real.log x) ≤ Real.sqrt x := Real.sqrt_le_sqrt (Real.log_le_self hx₀.le)
    have h₁ := mul_le_mul_of_nonneg_right ((hA N).trans hsmall) hsx.le
    have h₂ := mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg x)
    have hsquare := Real.sq_sqrt hx₀.le
    have hCb : 0 ≤ 2 * C * b * x := by positivity
    nlinarith
  · have hslog := sqrt_log_le_twice_sqrt_log hx.le (le_of_not_ge hsmall)
    have hden : 0 < 1 + Real.sqrt (Real.log (N : ℝ)) := by positivity
    have hscalar : C / (1 + Real.sqrt (Real.log (N : ℝ))) ≤ 2 * C / Real.sqrt (Real.log x) := by
      apply (div_le_div_iff₀ hden hsx).mpr
      have hmul := mul_le_mul_of_nonneg_left hslog hC
      nlinarith
    have hAN : A N ≤ (2 * C * N) / Real.sqrt (Real.log x) := by
      apply (hcount N).trans
      have hmul := mul_le_mul_of_nonneg_right hscalar (Nat.cast_nonneg N)
      convert hmul using 1 <;> ring
    have hAlog := (le_div_iff₀ hsx).mp hAN
    have hlarge := mul_le_mul_of_nonneg_left hN (show 0 ≤ 2 * C by positivity)
    nlinarith

theorem count_scaled_exponential_le {A : ℕ → ℝ} (hA : ∀ N : ℕ, A N ≤ N)
    {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ N : ℕ, A N ≤ C * N / (1 + Real.sqrt (Real.log (N : ℝ))))
    {b δ : ℝ} (hb : 0 ≤ b) (hδ : 0 < δ) {N : ℕ}
    (hN : (N : ℝ) ≤ b * Real.exp (1 / δ)) :
    A N / (Real.exp (1 / δ) * Real.sqrt δ) ≤ 1 + 2 * C * b := by
  have hx : 1 < Real.exp (1 / δ) := Real.one_lt_exp_iff.mpr (by positivity)
  have hbound := count_mul_sqrt_log_le hA hC hcount hb hx hN
  rw [Real.log_exp, one_div, Real.sqrt_inv, ← div_eq_mul_inv] at hbound
  have hsp : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hstep := (div_le_iff₀ (Real.exp_pos (δ⁻¹))).mpr hbound
  simpa only [one_div, div_div, mul_comm (Real.sqrt δ)] using hstep

theorem spatial_sum_eq_finset {a : ℕ → ℂ} {Ψ : ℝ → ℂ} {b x : ℝ}
    (hx : 0 < x) (hb : ∀ y : ℝ, Ψ y ≠ 0 → y ≤ b) :
    (∑' n : ℕ, a n * Ψ ((n : ℝ) / x)) =
      ∑ n ∈ Finset.range (⌈b * x⌉₊ + 1), a n * Ψ ((n : ℝ) / x) := by
  apply tsum_eq_sum
  intro n hn
  have hzero : Ψ ((n : ℝ) / x) = 0 := by
    by_contra hne
    have hnx : (n : ℝ) ≤ b * x := (div_le_iff₀ hx).mp (hb _ hne)
    have hceil : n ≤ ⌈b * x⌉₊ := by
      exact_mod_cast hnx.trans (Nat.le_ceil (b * x))
    exact hn (Finset.mem_range.mpr (Nat.lt_succ_of_le hceil))
  rw [hzero, mul_zero]

theorem ceil_mul_add_one_le {b x : ℝ} (hb : 0 ≤ b) (hx : 1 ≤ x) :
    ((⌈b * x⌉₊ + 1 : ℕ) : ℝ) ≤ (b + 2) * x := by
  have hceil := Nat.ceil_lt_add_one (mul_nonneg hb (zero_le_one.trans hx))
  push_cast
  nlinarith

end Bernays
