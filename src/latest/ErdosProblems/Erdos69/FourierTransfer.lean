import ErdosProblems.Erdos69.FourierTaylor
import ErdosProblems.Erdos69.FiniteMoments

/-! # Transfer of characteristic functions from finitely many moments -/

open scoped BigOperators

namespace Erdos69.Elementary.FiniteLaw

variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

theorem complexMean_const_mul (μ : FiniteLaw Ω) (c : ℂ) (f : Ω → ℂ) :
    μ.complexMean (fun x ↦ c * f x) = c * μ.complexMean f := by
  simp [complexMean, Finset.mul_sum, mul_left_comm]

theorem complexMean_sum {ι : Type*} (μ : FiniteLaw Ω) (s : Finset ι)
    (f : ι → Ω → ℂ) :
    μ.complexMean (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, μ.complexMean (f i) := by
  simp only [complexMean, Finset.mul_sum]
  exact Finset.sum_comm

theorem complexMean_phaseTaylor (μ : FiniteLaw Ω) (X : Ω → ℝ) (n : ℕ) :
    μ.complexMean (fun x ↦ phaseTaylor n (X x)) =
      ∑ k ∈ Finset.range n, ((2 * Real.pi : ℝ) * Complex.I) ^ k /
        k.factorial * (μ.mean (fun x ↦ X x ^ k) : ℂ) := by
  simp only [phaseTaylor, complexMean_sum, complexMean_const_mul, ← Complex.ofReal_pow,
    complexMean_real]

theorem phaseTaylor_moment_error (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ)
    (X : Ω → ℝ) (Y : Ξ → ℝ) (n : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ k < n, |μ.mean (fun x ↦ X x ^ k) - ν.mean (fun y ↦ Y y ^ k)| ≤ δ) :
    ‖μ.complexMean (fun x ↦ phaseTaylor n (X x)) -
      ν.complexMean (fun y ↦ phaseTaylor n (Y y))‖ ≤
        δ * ∑ k ∈ Finset.range n, (2 * Real.pi) ^ k / k.factorial := by
  rw [complexMean_phaseTaylor, complexMean_phaseTaylor, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.range n,
        ‖((2 * Real.pi : ℝ) * Complex.I) ^ k / k.factorial *
          (μ.mean (fun x ↦ X x ^ k) : ℂ) -
          ((2 * Real.pi : ℝ) * Complex.I) ^ k / k.factorial *
          (ν.mean (fun y ↦ Y y ^ k) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n, ((2 * Real.pi) ^ k / k.factorial) * δ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [← mul_sub, norm_mul, norm_div, norm_pow, ← Complex.ofReal_sub]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
        mul_one, Nat.abs_cast, Complex.norm_natCast, abs_mul, abs_of_pos Real.pi_pos,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_mul_of_nonneg_left (h k (Finset.mem_range.mp hk)) (by positivity)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

theorem mean_phaseTaylor_remainder (μ : FiniteLaw Ω) (X : Ω → ℝ) (n : ℕ) :
    ‖μ.complexMean (fun x ↦ fourierPhase (X x)) -
      μ.complexMean (fun x ↦ phaseTaylor (n + 1) (X x))‖ ≤
        (2 * Real.pi) ^ (n + 1) / n.factorial * μ.mean (fun x ↦ |X x| ^ (n + 1)) := by
  calc
    _ ≤ μ.mean (fun x ↦ ‖fourierPhase (X x) - phaseTaylor (n + 1) (X x)‖) :=
      μ.norm_complexMean_sub_le _ _
    _ ≤ μ.mean (fun x ↦ (2 * Real.pi * |X x|) ^ (n + 1) / n.factorial) :=
      μ.mean_mono (fun x ↦ fourierPhase_taylor_remainder n (X x))
    _ = _ := by simp only [mul_pow, div_eq_mul_inv, mul_right_comm, mean_const_mul]

theorem fourier_moment_transfer (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ)
    (X : Ω → ℝ) (Y : Ξ → ℝ) (n : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ k < n + 1, |μ.mean (fun x ↦ X x ^ k) - ν.mean (fun y ↦ Y y ^ k)| ≤ δ) :
    ‖μ.complexMean (fun x ↦ fourierPhase (X x)) -
      ν.complexMean (fun y ↦ fourierPhase (Y y))‖ ≤
        δ * (∑ k ∈ Finset.range (n + 1), (2 * Real.pi) ^ k / k.factorial) +
        (2 * Real.pi) ^ (n + 1) / n.factorial *
          (μ.mean (fun x ↦ |X x| ^ (n + 1)) + ν.mean (fun y ↦ |Y y| ^ (n + 1))) := by
  have h₁ := μ.mean_phaseTaylor_remainder X n
  have h₂ := phaseTaylor_moment_error μ ν X Y (n + 1) δ hδ h
  have h₃ := ν.mean_phaseTaylor_remainder Y n
  have htri := norm_sub_le_norm_sub_add_norm_sub (μ.complexMean (fun x ↦ fourierPhase (X x)))
    (μ.complexMean (fun x ↦ phaseTaylor (n + 1) (X x)))
    (ν.complexMean (fun y ↦ fourierPhase (Y y)))
  have htri' := norm_sub_le_norm_sub_add_norm_sub (μ.complexMean (fun x ↦ phaseTaylor (n + 1) (X x)))
    (ν.complexMean (fun y ↦ phaseTaylor (n + 1) (Y y)))
    (ν.complexMean (fun y ↦ fourierPhase (Y y)))
  rw [norm_sub_rev (ν.complexMean (fun y ↦ phaseTaylor (n + 1) (Y y)))] at htri'
  nlinarith

theorem mean_abs_power_le_exponential (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (s : ℝ) (hs : 0 < s) (n : ℕ) :
    μ.mean (fun x ↦ |X x| ^ n) ≤
      (n.factorial : ℝ) / s ^ n *
        (μ.mean (fun x ↦ Real.exp (s * X x)) +
          μ.mean (fun x ↦ Real.exp (-s * X x))) := by
  rw [← mean_add, ← mean_const_mul]
  apply μ.mean_mono
  intro x
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hsp : 0 < s ^ n := pow_pos hs n
  have hp := Real.pow_div_factorial_le_exp (s * |X x|)
    (mul_nonneg hs.le (abs_nonneg (X x))) n
  have hexp : Real.exp (s * |X x|) ≤ Real.exp (s * X x) + Real.exp (-s * X x) := by
    rcases le_total 0 (X x) with hx | hx
    · rw [abs_of_nonneg hx]
      linarith [Real.exp_pos (-s * X x)]
    · rw [abs_of_nonpos hx]
      have heq : s * -X x = -s * X x := by ring
      rw [heq]
      linarith [Real.exp_pos (s * X x)]
  have hp' := hp.trans hexp
  rw [mul_pow, div_le_iff₀ hf] at hp'
  calc
    |X x| ^ n = (s ^ n * |X x| ^ n) / s ^ n := by field_simp
    _ ≤ ((Real.exp (s * X x) + Real.exp (-s * X x)) * n.factorial) / s ^ n :=
      div_le_div_of_nonneg_right hp' hsp.le
    _ = _ := by ring

end Erdos69.Elementary.FiniteLaw
