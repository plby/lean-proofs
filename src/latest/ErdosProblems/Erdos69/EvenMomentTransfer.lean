import ErdosProblems.Erdos69.FourierTransfer

/-! # A quantitative Fourier transfer from even moments -/

open scoped BigOperators

namespace Erdos69.Elementary.FiniteLaw

variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

theorem even_moment_mean_le (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ)
    (X : Ω → ℝ) (Y : Ξ → ℝ) (m : ℕ) (hm : Even m) (δ : ℝ)
    (h : |μ.mean (fun x ↦ X x ^ m) - ν.mean (fun y ↦ Y y ^ m)| ≤ δ) :
    μ.mean (fun x ↦ |X x| ^ m) ≤ ν.mean (fun y ↦ |Y y| ^ m) + δ := by
  simp only [hm.pow_abs]
  linarith [(abs_le.mp h).2]

theorem fourier_even_transfer (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ)
    (X : Ω → ℝ) (Y : Ξ → ℝ) (m : ℕ) (hm : 0 < m) (hme : Even m)
    (δ E : ℝ) (hδ : 0 ≤ δ)
    (hmom : ∀ k ≤ m, |μ.mean (fun x ↦ X x ^ k) - ν.mean (fun y ↦ Y y ^ k)| ≤ δ)
    (hplus : ν.mean (fun y ↦ Real.exp ((4 * Real.pi) * Y y)) ≤ E)
    (hminus : ν.mean (fun y ↦ Real.exp (-(4 * Real.pi) * Y y)) ≤ E) :
    ‖μ.complexMean (fun x ↦ fourierPhase (X x)) -
      ν.complexMean (fun y ↦ fourierPhase (Y y))‖ ≤
        δ * (1 + m) * Real.exp (2 * Real.pi) + 4 * m * E * (1 / 2 : ℝ) ^ m := by
  have hmn : m - 1 + 1 = m := by omega
  have htransfer := fourier_moment_transfer μ ν X Y (m - 1) δ hδ
    (fun k hk ↦ hmom k (by omega))
  rw [hmn] at htransfer
  have hactual := even_moment_mean_le μ ν X Y m hme δ (hmom m le_rfl)
  have hmodel := mean_abs_power_le_exponential ν Y (4 * Real.pi) (by positivity) m
  have hfac : (0 : ℝ) < m.factorial := by positivity
  have hscale : 0 ≤ (m.factorial : ℝ) / (4 * Real.pi) ^ m := by positivity
  have hmodel' : ν.mean (fun y ↦ |Y y| ^ m) ≤
      (m.factorial : ℝ) / (4 * Real.pi) ^ m * (2 * E) := by
    exact hmodel.trans (mul_le_mul_of_nonneg_left (by linarith) hscale)
  have hpref : (2 * Real.pi) ^ m / (m - 1).factorial =
      (m : ℝ) * ((2 * Real.pi) ^ m / m.factorial) := by
    have hf : (m.factorial : ℝ) = m * ((m - 1).factorial : ℝ) := by
      nth_rw 1 [← hmn]
      rw [Nat.factorial_succ, Nat.cast_mul]
      congr 1
      exact_mod_cast hmn
    rw [hf]
    field_simp
  have hpref_le : (2 * Real.pi) ^ m / (m - 1).factorial ≤
      m * Real.exp (2 * Real.pi) := by
    rw [hpref]
    exact mul_le_mul_of_nonneg_left
      (Real.pow_div_factorial_le_exp (2 * Real.pi) (by positivity) m) (by positivity)
  have hpoly := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ 2 * Real.pi) m
  have hrem : (2 * Real.pi) ^ m / (m - 1).factorial *
      (μ.mean (fun x ↦ |X x| ^ m) + ν.mean (fun y ↦ |Y y| ^ m)) ≤
        (2 * Real.pi) ^ m / (m - 1).factorial * δ + 4 * m * E * (1 / 2 : ℝ) ^ m := by
    have hsum : μ.mean (fun x ↦ |X x| ^ m) + ν.mean (fun y ↦ |Y y| ^ m) ≤
        δ + 4 * E * (m.factorial : ℝ) / (4 * Real.pi) ^ m := by
      calc
        _ ≤ δ + 2 * ν.mean (fun y ↦ |Y y| ^ m) := by linarith
        _ ≤ δ + 2 * ((m.factorial : ℝ) / (4 * Real.pi) ^ m * (2 * E)) := by
          gcongr
        _ = _ := by ring
    calc
      _ ≤ (2 * Real.pi) ^ m / (m - 1).factorial *
          (δ + 4 * E * (m.factorial : ℝ) / (4 * Real.pi) ^ m) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by
        rw [mul_add]
        congr 1
        have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
        have hratio : (2 * Real.pi) ^ m / (4 * Real.pi) ^ m = (1 / 2 : ℝ) ^ m := by
          rw [← div_pow]
          congr 1
          field_simp
          ring
        calc
          _ = 4 * m * E * ((2 * Real.pi) ^ m / (4 * Real.pi) ^ m) := by
            rw [hpref]
            field_simp
          _ = _ := by rw [hratio]
  have hδpoly := mul_le_mul_of_nonneg_left hpoly hδ
  have hδpref := mul_le_mul_of_nonneg_right hpref_le hδ
  nlinarith

end Erdos69.Elementary.FiniteLaw
