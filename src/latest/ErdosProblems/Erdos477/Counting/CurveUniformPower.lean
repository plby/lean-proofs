/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Absorbing the uniform plane-curve estimate's logarithmic factor.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.CurveUniformLog

namespace Erdos477.Counting

open Filter

lemma eventually_log_add_one_pow_four_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ B : ℝ in atTop, (Real.log B + 1) ^ 4 ≤ B ^ ε := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop 4 hε).bound
      (by norm_num : (0 : ℝ) < 1 / 16),
    Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_ge_atTop (1 : ℝ)] with B h hlog hB
  have hBlog : 0 ≤ Real.log B := by linarith
  have hBpow := Real.rpow_nonneg (by linarith : 0 ≤ B) ε
  have h' : Real.log B ^ 4 ≤ (1 / 16 : ℝ) * B ^ ε := by
    simpa only [show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast,
      Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hBlog 4), abs_of_nonneg hBpow] using h
  calc
    _ ≤ (2 * Real.log B) ^ 4 := by gcongr; linarith
    _ = 16 * Real.log B ^ 4 := by ring
    _ ≤ _ := by linarith

variable {K : Type*} [Field K] [CharZero K]

/-- Uniform in all coefficients. The exponent uses degree in the first
variable; a degree-preserving coordinate choice is a separate geometric step. -/
theorem exists_uniform_curve_power_bound (D d : ℕ) (hd : 1 ≤ d)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop,
      ∀ P : MvPolynomial (Fin 2) K, Irreducible P → P.totalDegree = D →
      P.degreeOf 0 = d → ∀ S : Finset (Fin 2 → ℤ),
      (∀ z ∈ S, MvPolynomial.eval (fun k => (z k : K)) P = 0) →
      (∀ z ∈ S, ∀ k, |(z k : ℝ)| ≤ B) →
      (S.card : ℝ) ≤ C * B ^ (1 / (d : ℝ) + ε) := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨n, hn, hεn⟩ := exists_curve_auxiliary_index (ε / 2) hhalf
  obtain ⟨C, hC, hbound⟩ := exists_uniform_curve_log_bound (K := K)
    D d n hd hn (ε / 2) hhalf.le hεn
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_gt_atTop (2 * Real.log (d * n : ℕ)),
    eventually_log_add_one_pow_four_le_rpow (ε / 2) hhalf] with B hB hlarge hlog
  intro P hP hD hPd S hS hheight
  calc
    _ ≤ C * (Real.log B + 1) ^ 4 * B ^ (1 / (d : ℝ) + ε / 2) :=
      hbound B hB hlarge P hP hD hPd S hS hheight
    _ ≤ C * B ^ (ε / 2) * B ^ (1 / (d : ℝ) + ε / 2) := by gcongr
    _ = C * B ^ (ε / 2 + (1 / (d : ℝ) + ε / 2)) := by
      rw [mul_assoc, ← Real.rpow_add (by linarith : 0 < B)]
    _ = _ := by congr 2; ring

#print axioms exists_uniform_curve_power_bound
-- 'Erdos477.Counting.exists_uniform_curve_power_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
