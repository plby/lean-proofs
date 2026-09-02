/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
/-

Additional Gamma-integral lemmas from teorth/mathlib4 at
 da1f94df976c7cd38117281c57d6ee3046c8d104, extracted from
 Analysis/SpecialFunctions/Gamma/Deriv.lean and NumberTheory/Harmonic/GammaDeriv.lean.
-/
module

public import Mathlib.NumberTheory.Harmonic.GammaDeriv
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section

namespace Erdos327.Mertens

open MeasureTheory Set Filter Topology

open Complex in
theorem complex_hasDerivAt_Gamma {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt Gamma (∫ t : ℝ in Ioi 0, t ^ (s - 1) * (Real.log t * Real.exp (-t))) s := by
  have : IsOpen {s : ℂ | 0 < s.re} := continuous_re.isOpen_preimage _ isOpen_Ioi
  apply (hasDerivAt_GammaIntegral (by simpa using hs)).congr_of_eventuallyEq
  filter_upwards [this.mem_nhds hs] with a using Gamma_eq_integral

open Real

theorem real_hasDerivAt_Gamma {s : ℝ} (hs : 0 < s) :
    HasDerivAt Real.Gamma (∫ t in Ioi 0, t ^ (s - 1) * (log t * exp (-t))) s := by
  convert (complex_hasDerivAt_Gamma (by simpa using hs : 0 < (s:ℂ).re)).real_of_complex
  · simp [Complex.Gamma_ofReal]
  convert (Complex.ofReal_re ?_).symm
  calc
    _ = ∫ (t : ℝ) in Ioi 0, ↑(t ^ (s - 1) * (log t * exp (-t))) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx ↦ ?_)
      simp only [mem_Ioi] at hx
      norm_cast; rw [← Complex.ofReal_cpow hx.le]; norm_cast
    _ = _ := by norm_cast

theorem deriv_Gamma_one_eq_integral_log : deriv Real.Gamma 1 = ∫ t in Ioi 0, log t * exp (-t) := by
  simpa using (real_hasDerivAt_Gamma (by norm_num : 0 < (1 : ℝ))).deriv

theorem integrableOn_log_log_mul_rpow {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun t ↦ log (log t) * t ^ (-s)) (Ioi 1) := by
  rw [← exp_zero, ← integrableOn_comp_exp_Ioi]
  apply Integrable.mono' (g := fun x ↦ (2 * x ^ (- (1 : ℝ) / 2) + x) * exp (-(s - 1) * x))
  · simp only [add_mul, mul_assoc]
    refine (Integrable.const_mul ?_ _).add ?_
    · simpa [IntegrableOn] using integrableOn_rpow_mul_exp_neg_mul_rpow
        (by norm_num : -1 < (-1 : ℝ) / 2) (by norm_num : 0 < (1 : ℝ)) (by linarith : 0 < s - 1)
    simpa [IntegrableOn] using integrableOn_rpow_mul_exp_neg_mul_rpow
        (by norm_num : -1 < (1 : ℝ)) (by norm_num : 0 < (1 : ℝ)) (by linarith : 0 < s - 1)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simp only [mem_Ioi] at hx
  simp only [log_exp, smul_eq_mul, norm_mul, norm_eq_abs, abs_exp, neg_sub, ← exp_mul]
  rw [mul_comm, mul_assoc, ← exp_add]
  gcongr
  · rw [abs_le]; constructor
    · grw [neg_le, ← log_inv, log_le_rpow_div (by positivity) (by positivity : 0 < (1 : ℝ) / 2)]
      simp [← rpow_neg_eq_inv_rpow]; ring_nf; linarith
    grw [log_le_self hx.le, le_add_iff_nonneg_left]
    positivity
  grind

theorem deriv_Gamma_one_eq_integral_log_log {s : ℝ} (hs : 1 < s) :
    deriv Real.Gamma 1 = (s - 1) * (∫ t in Ioi 1, log (log t) * t ^ (-s)) + log (s - 1) := by
  rw [deriv_Gamma_one_eq_integral_log, ← mul_zero (s - 1),
      ← integral_comp_mul_left_Ioi' _ _ (by linarith), ← log_one,
      ← integral_comp_log_Ioi _ zero_lt_one, smul_eq_mul]
  have hs' : s - 1 ≠ 0 := by linarith
  calc
    _ = (s - 1) * ∫ (t : ℝ) in Ioi 1, (log (log t) + log (s - 1)) * t ^ (-s) := by
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx ↦ ?_)
      simp only [mem_Ioi] at hx
      have : x ^ (-(s - 1)) = x ^ (-s) * x := by rw [← rpow_add_one (by positivity)]; ring_nf
      rw [log_mul hs' (log_pos hx).ne', smul_eq_mul, neg_mul_eq_neg_mul, mul_comm _ (log x),
            ← rpow_def_of_pos (by linarith), this]
      field_simp; ring
    _ = (s - 1) * ((∫ t in Ioi 1, log (log t) * t ^ (-s)) + log (s - 1) * (s - 1)⁻¹)  := by
      congr
      simp_rw [add_mul]
      convert integral_add (integrableOn_log_log_mul_rpow hs) (.const_mul ?_ _)
      · rw [integral_const_mul]; congr; symm
        convert! integral_Ioi_rpow_of_lt (a := -s) (c := 1) (by linarith) zero_lt_one using 1
        simp; grind
      exact integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    _ = _ := by field_simp

/-- An integral representation of the Euler–Mascheroni constant, valid for
any `s > 1`. -/
lemma eulerMascheroniConstant_eq_neg_integral_log_log {s : ℝ} (hs : 1 < s) :
    Real.eulerMascheroniConstant =
      -((s - 1) * (∫ t in Ioi 1, log (log t) * t ^ (-s)) + log (s - 1)) := by
  rw [eulerMascheroniConstant_eq_neg_deriv,
    deriv_Gamma_one_eq_integral_log_log hs]

end Erdos327.Mertens
