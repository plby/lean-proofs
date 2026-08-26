import ErdosProblems.Erdos1148.ConvolutionStripError
import ErdosProblems.Erdos1148.RealDirichletProduct

/-! # Boundary estimates for the four-factor hyperbola argument -/

namespace Erdos1148.DukeArithmetic

lemma rpow_biquadratic_cross {x : ℝ} (hx : 0 < x) (s : ℝ) :
    x ^ (1 - s) * x ^ (1 / 2 - s) = x ^ (3 / 2 - 2 * s) := by
  rw [← Real.rpow_add hx]
  congr 1
  ring

lemma rpow_biquadratic_main_tail {x : ℝ} (hx : 0 < x) (s : ℝ) :
    (x * x) ^ (1 - s) * x ^ (-(1 / 2) : ℝ) = x ^ (3 / 2 - 2 * s) := by
  rw [Real.mul_rpow hx.le hx.le, ← Real.rpow_add hx, ← Real.rpow_add hx]
  congr 1
  ring

lemma rpow_biquadratic_strip {x : ℝ} (hx : 0 < x) (s : ℝ) :
    (x * x) ^ (1 / 2 - s) * x ^ (5 / 8 : ℝ) = x ^ (13 / 8 - 2 * s) := by
  rw [Real.mul_rpow hx.le hx.le, ← Real.rpow_add hx, ← Real.rpow_add hx]
  congr 1
  ring

theorem realZetaConvolution_sub_constant_norm_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) {s : ℝ} (hs : 1 / 2 ≤ s) (hs1 : s < 1)
    {N : ℕ} (hN : 0 < N) :
    ‖weightedArithmeticPartialSum (realZetaConvolution χ) s N -
        realZetaRegularized s * realDirichletValue χ s‖ ≤
      38 * ((q : ℝ) / (1 - s)) * (N : ℝ) ^ (1 - s) := by
  have hd : 0 < 1 - s := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have herr := realZetaConvolution_nat_error_le χ hχ hs hs1 hN
  have hp : (N : ℝ) ^ (1 / 2 - s) ≤ (N : ℝ) ^ (1 - s) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hmain : ‖(N : ℝ) ^ (1 - s) / (1 - s) * realDirichletValue χ 1‖ ≤
      2 * ((q : ℝ) / (1 - s)) * (N : ℝ) ^ (1 - s) := by
    rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ (N : ℝ) ^ (1 - s) / (1 - s))]
    calc
      _ ≤ (N : ℝ) ^ (1 - s) / (1 - s) * (2 * q) :=
        mul_le_mul_of_nonneg_left (realDirichletValue_norm_le χ hχ zero_lt_one) (by positivity)
      _ = _ := by ring
  calc
    _ = ‖(weightedArithmeticPartialSum (realZetaConvolution χ) s N -
        (realZetaRegularized s * realDirichletValue χ s +
          (N : ℝ) ^ (1 - s) / (1 - s) * realDirichletValue χ 1)) +
        (N : ℝ) ^ (1 - s) / (1 - s) * realDirichletValue χ 1‖ := by congr 1; ring
    _ ≤ ‖weightedArithmeticPartialSum (realZetaConvolution χ) s N -
        (realZetaRegularized s * realDirichletValue χ s +
          (N : ℝ) ^ (1 - s) / (1 - s) * realDirichletValue χ 1)‖ +
        ‖(N : ℝ) ^ (1 - s) / (1 - s) * realDirichletValue χ 1‖ := norm_add_le _ _
    _ ≤ 36 * ((q : ℝ) / (1 - s)) * (N : ℝ) ^ (1 / 2 - s) +
        2 * ((q : ℝ) / (1 - s)) * (N : ℝ) ^ (1 - s) := add_le_add herr hmain
    _ ≤ 36 * ((q : ℝ) / (1 - s)) * (N : ℝ) ^ (1 - s) +
        2 * ((q : ℝ) / (1 - s)) * (N : ℝ) ^ (1 - s) := by gcongr
    _ = _ := by ring

theorem biquadratic_cross_error_le {q r u : ℕ} [NeZero q] [NeZero r] [NeZero u]
    (χ : DirichletCharacter ℝ q) (ψ : DirichletCharacter ℝ r) (ρ : DirichletCharacter ℝ u)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hρ : ρ ≠ 1) {s : ℝ} (hs : 1 / 2 ≤ s) (hs1 : s < 1)
    {N : ℕ} (hN : 0 < N) :
    ‖(weightedArithmeticPartialSum (realZetaConvolution χ) s N -
        realZetaRegularized s * realDirichletValue χ s) *
      (realDirichletValue ψ s * realDirichletValue ρ s -
        weightedArithmeticPartialSum (realCharacterArithmetic ψ * realCharacterArithmetic ρ) s N)‖ ≤
      608 * ((q : ℝ) * r * u / (1 - s)) * (N : ℝ) ^ (3 / 2 - 2 * s) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hd : 0 < 1 - s := by linarith
  have hB : ‖realDirichletValue ψ s * realDirichletValue ρ s -
      weightedArithmeticPartialSum (realCharacterArithmetic ψ * realCharacterArithmetic ρ) s N‖ ≤
      16 * r * u * (N : ℝ) ^ (1 / 2 - s) := by
    rw [norm_sub_rev]
    exact realCharacterConvolution_error_le ψ ρ hψ hρ hs hs1.le hN
  rw [norm_mul]
  calc
    _ ≤ (38 * ((q : ℝ) / (1 - s)) * (N : ℝ) ^ (1 - s)) *
        (16 * r * u * (N : ℝ) ^ (1 / 2 - s)) :=
      mul_le_mul (realZetaConvolution_sub_constant_norm_le χ hχ hs hs1 hN) hB
        (norm_nonneg _) (by positivity)
    _ = _ := by rw [← rpow_biquadratic_cross hN0 s]; ring

theorem biquadratic_residue_tail_error_le {q r u : ℕ} [NeZero q] [NeZero r] [NeZero u]
    (χ : DirichletCharacter ℝ q) (ψ : DirichletCharacter ℝ r) (ρ : DirichletCharacter ℝ u)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hρ : ρ ≠ 1) {s : ℝ} (hs1 : s < 1)
    {N : ℕ} (hN : 0 < N) :
    ‖((N * N : ℕ) : ℝ) ^ (1 - s) / (1 - s) * realDirichletValue χ 1 *
      (realDirichletValue ψ 1 * realDirichletValue ρ 1 -
        weightedArithmeticPartialSum (realCharacterArithmetic ψ * realCharacterArithmetic ρ) 1 N)‖ ≤
      32 * ((q : ℝ) * r * u / (1 - s)) * (N : ℝ) ^ (3 / 2 - 2 * s) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hd : 0 < 1 - s := by linarith
  have hB : ‖realDirichletValue ψ 1 * realDirichletValue ρ 1 -
      weightedArithmeticPartialSum (realCharacterArithmetic ψ * realCharacterArithmetic ρ) 1 N‖ ≤
      16 * r * u * (N : ℝ) ^ (-(1 / 2) : ℝ) := by
    rw [norm_sub_rev]
    have h := realCharacterConvolution_error_le ψ ρ hψ hρ (by norm_num : (1 / 2 : ℝ) ≤ 1) le_rfl hN
    norm_num only [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num] at h
    exact h
  rw [norm_mul, norm_mul, Real.norm_of_nonneg
    (by positivity : 0 ≤ ((N * N : ℕ) : ℝ) ^ (1 - s) / (1 - s))]
  calc
    _ ≤ (((N * N : ℕ) : ℝ) ^ (1 - s) / (1 - s) * (2 * q)) *
        (16 * r * u * (N : ℝ) ^ (-(1 / 2) : ℝ)) := by
      apply mul_le_mul _ hB (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left (realDirichletValue_norm_le χ hχ zero_lt_one) (by positivity)
    _ = _ := by rw [Nat.cast_mul, ← rpow_biquadratic_main_tail hN0 s]; ring

end Erdos1148.DukeArithmetic
