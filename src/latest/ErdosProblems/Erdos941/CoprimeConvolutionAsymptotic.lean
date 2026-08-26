/- Adapted from the checked repository proof in Erdos1148/CoprimeConvolutionAsymptotic.lean. -/
import ErdosProblems.Erdos941.DirichletHyperbola
import ErdosProblems.Erdos941.CoprimeHyperbolaStrips
import Mathlib.Analysis.SpecificLimits.Basic

/-! # The summatory asymptotic for the restricted zeta-character convolution -/

namespace Erdos941.Analytic

open Finset Filter Topology ArithmeticFunction

theorem coprime_convolution_hyperbola_error_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) {N : ℕ} (hN : 0 < N) :
    ‖(∑ n ∈ Ioc 0 (N * N), realCoprimeZetaConvolution χ n) -
      principalCharacterMean q * (N : ℝ) ^ 2 * realDirichletPartialSum χ 1 N‖ ≤
        9 * q * N := by
  have hle : N ≤ N * N := by nlinarith
  have h := sum_convolution_hyperbola (realCharacterArithmetic χ)
    (realCharacterArithmetic (1 : DirichletCharacter ℝ q)) hle hle le_rfl
    (by nlinarith : N * N < (N + 1) * (N + 1))
  have hconv : realCharacterArithmetic χ * realCharacterArithmetic (1 : DirichletCharacter ℝ q) =
      realCoprimeZetaConvolution χ := mul_comm _ _
  rw [hconv] at h
  have happ (ψ : DirichletCharacter ℝ q) (n : ℕ) (hn : 0 < n) :
      realCharacterArithmetic ψ n = ψ n :=
    (ψ.apply_eq_toArithmeticFunction_apply hn.ne').symm
  have hsum (ψ : DirichletCharacter ℝ q) (L : ℕ) :
      (∑ n ∈ Ioc 0 L, realCharacterArithmetic ψ n) = ∑ n ∈ Ioc 0 L, ψ n :=
    sum_congr rfl (fun n hn => happ ψ n (mem_Ioc.mp hn).1)
  have hmulsum (ψ : DirichletCharacter ℝ q) (g : ℕ → ℝ) (L : ℕ) :
      (∑ n ∈ Ioc 0 L, realCharacterArithmetic ψ n * g n) = ∑ n ∈ Ioc 0 L, ψ n * g n :=
    sum_congr rfl (fun n hn => by rw [happ ψ n (mem_Ioc.mp hn).1])
  simp_rw [hsum, hmulsum] at h
  have hstrips : (∑ n ∈ Ioc 0 (N * N), realCoprimeZetaConvolution χ n) =
      (∑ m ∈ Ioc 0 N, χ m * ∑ n ∈ Ioc 0 (N * N / m), (1 : DirichletCharacter ℝ q) n) +
      (∑ n ∈ Ioc 0 N, (1 : DirichletCharacter ℝ q) n * ∑ m ∈ Ioc 0 (N * N / n), χ m) -
      (∑ m ∈ Ioc 0 N, χ m) * (∑ n ∈ Ioc 0 N, (1 : DirichletCharacter ℝ q) n) := by
    exact h
  rw [hstrips]
  have hmain := coprime_hyperbola_main_strip_error_le χ (N * N) N
  have hsecond := coprime_hyperbola_second_strip_le χ hχ (N * N) N
  have hcross : ‖(∑ m ∈ Ioc 0 N, χ m) *
      (∑ n ∈ Ioc 0 N, (1 : DirichletCharacter ℝ q) n)‖ ≤ 2 * q * N := by
    rw [norm_mul]
    exact mul_le_mul (character_sum_Ioc_norm_le χ hχ N)
      (character_sum_Ioc_norm_le_length _ N) (norm_nonneg _) (by positivity)
  rw [Nat.cast_mul, ← pow_two (N : ℝ)] at hmain
  have hnorm := norm_sub_le
    ((∑ m ∈ Ioc 0 N, χ m * ∑ n ∈ Ioc 0 (N * N / m), (1 : DirichletCharacter ℝ q) n) -
      principalCharacterMean q * (N : ℝ) ^ 2 * realDirichletPartialSum χ 1 N +
      (∑ n ∈ Ioc 0 N, (1 : DirichletCharacter ℝ q) n * ∑ m ∈ Ioc 0 (N * N / n), χ m))
    ((∑ m ∈ Ioc 0 N, χ m) * (∑ n ∈ Ioc 0 N, (1 : DirichletCharacter ℝ q) n))
  have hadd := norm_add_le
    ((∑ m ∈ Ioc 0 N, χ m * ∑ n ∈ Ioc 0 (N * N / m), (1 : DirichletCharacter ℝ q) n) -
      principalCharacterMean q * (N : ℝ) ^ 2 * realDirichletPartialSum χ 1 N)
    (∑ n ∈ Ioc 0 N, (1 : DirichletCharacter ℝ q) n * ∑ m ∈ Ioc 0 (N * N / n), χ m)
  rw [show ∀ A B C T : ℝ, A + B - C - T = (A - T + B) - C by intros; ring]
  linarith

theorem coprime_convolution_sum_div_sq_tendsto {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc 0 (N * N), realCoprimeZetaConvolution χ n) /
      (N : ℝ) ^ 2) atTop (𝓝 (principalCharacterMean q * realDirichletValue χ 1)) := by
  have herr : Tendsto (fun N : ℕ =>
      (∑ n ∈ Ioc 0 (N * N), realCoprimeZetaConvolution χ n) / (N : ℝ) ^ 2 -
        principalCharacterMean q * realDirichletPartialSum χ 1 N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_const_div_atTop_nhds_zero_nat (9 * (q : ℝ)))
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have heq : (∑ n ∈ Ioc 0 (N * N), realCoprimeZetaConvolution χ n) / (N : ℝ) ^ 2 -
        principalCharacterMean q * realDirichletPartialSum χ 1 N =
      ((∑ n ∈ Ioc 0 (N * N), realCoprimeZetaConvolution χ n) -
        principalCharacterMean q * (N : ℝ) ^ 2 * realDirichletPartialSum χ 1 N) /
          (N : ℝ) ^ 2 := by field_simp
    rw [heq, norm_div, Real.norm_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ (9 * q * N) / (N : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (coprime_convolution_hyperbola_error_le χ hχ hN) (sq_nonneg _)
      _ = (9 * q : ℝ) / N := by field_simp
  have hmain := (realDirichletPartialSum_tendsto χ hχ (by norm_num : (0 : ℝ) < 1)).const_mul
    (principalCharacterMean q)
  simpa only [sub_add_cancel, zero_add] using herr.add hmain

end Erdos941.Analytic
