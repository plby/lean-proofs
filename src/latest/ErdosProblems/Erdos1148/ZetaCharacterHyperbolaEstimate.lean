import ErdosProblems.Erdos1148.HyperbolaBoundaryEstimates

/-! # An explicit zeta-character hyperbola estimate below one -/

namespace Erdos1148.DukeArithmetic

open Finset

theorem realZetaConvolution_hyperbola_error_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {N : ℕ} (hN : 0 < N) :
    ‖weightedArithmeticPartialSum (realZetaConvolution χ) s (N * N) -
        (realZetaRegularized s * realDirichletValue χ s +
          ((N * N : ℕ) : ℝ) ^ (1 - s) / (1 - s) * realDirichletValue χ 1)‖ ≤
      12 * ((q : ℝ) / (1 - s)) * (N : ℝ) ^ (1 - 2 * s) := by
  let A := ∑ m ∈ Ioc 0 N, (m : ℝ) ^ (-s) * χ m * realPowerPartialSum s (N * N / m)
  let B := ∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s) * realDirichletPartialSum χ s (N * N / n)
  let R := ((N * N : ℕ) : ℝ) ^ (1 - s) / (1 - s)
  let W := (N : ℝ) ^ (1 - 2 * s)
  let Q := (q : ℝ) / (1 - s)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNN : N ≤ N * N := by nlinarith
  have hW : 0 ≤ W := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hq : (q : ℝ) ≤ Q := by
    apply (le_div_iff₀ (by linarith : 0 < 1 - s)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) q]
  have hQ : 1 ≤ Q := (show (1 : ℝ) ≤ q by exact_mod_cast NeZero.pos q).trans hq
  have hscale : (N : ℝ) * ((N * N : ℕ) : ℝ) ^ (-s) = W := by
    rw [Nat.cast_mul, rpow_hyperbola_square_error hN0]
  have hA : ‖A - (realZetaRegularized s * realDirichletPartialSum χ s N +
        R * realDirichletPartialSum χ 1 N)‖ ≤ 2 * Q * W := by
    calc
      _ ≤ 2 * N * ((N * N : ℕ) : ℝ) ^ (-s) := hyperbola_power_strip_error_le χ hs hs1 hNN
      _ = 2 * W := by rw [mul_assoc, hscale]
      _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hQ) hW]
  have hB : ‖B - realPowerPartialSum s N * realDirichletValue χ s‖ ≤ 2 * Q * W := by
    calc
      _ ≤ 2 * q * N * ((N * N : ℕ) : ℝ) ^ (-s) :=
        hyperbola_character_strip_error_le χ hχ hs N (Nat.mul_pos hN hN)
      _ = 2 * q * W := by rw [mul_assoc (2 * (q : ℝ)), hscale]
      _ ≤ _ := by gcongr
  have hC : ‖(realPowerPartialSum s N - realZetaRegularized s) *
        (realDirichletValue χ s - realDirichletPartialSum χ s N)‖ ≤ 6 * Q * W :=
    hyperbola_cross_error_le χ hχ hs hs1 hN
  have hD : ‖R * (realDirichletValue χ 1 - realDirichletPartialSum χ 1 N)‖ ≤ 2 * Q * W :=
    hyperbola_residue_tail_error_le χ hχ hs1 hN
  have heq : weightedArithmeticPartialSum (realZetaConvolution χ) s (N * N) -
        (realZetaRegularized s * realDirichletValue χ s + R * realDirichletValue χ 1) =
      ((A - (realZetaRegularized s * realDirichletPartialSum χ s N +
          R * realDirichletPartialSum χ 1 N)) +
        (B - realPowerPartialSum s N * realDirichletValue χ s)) +
      (realPowerPartialSum s N - realZetaRegularized s) *
        (realDirichletValue χ s - realDirichletPartialSum χ s N) -
      R * (realDirichletValue χ 1 - realDirichletPartialSum χ 1 N) := by
    rw [realZetaConvolution_hyperbola χ s hN]
    dsimp only [A, B]
    ring
  change ‖weightedArithmeticPartialSum (realZetaConvolution χ) s (N * N) -
    (realZetaRegularized s * realDirichletValue χ s + R * realDirichletValue χ 1)‖ ≤ 12 * Q * W
  rw [heq]
  calc
    _ ≤ (‖A - (realZetaRegularized s * realDirichletPartialSum χ s N +
          R * realDirichletPartialSum χ 1 N)‖ +
        ‖B - realPowerPartialSum s N * realDirichletValue χ s‖) +
      ‖(realPowerPartialSum s N - realZetaRegularized s) *
        (realDirichletValue χ s - realDirichletPartialSum χ s N)‖ +
      ‖R * (realDirichletValue χ 1 - realDirichletPartialSum χ 1 N)‖ := by
        exact (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by linarith

end Erdos1148.DukeArithmetic
