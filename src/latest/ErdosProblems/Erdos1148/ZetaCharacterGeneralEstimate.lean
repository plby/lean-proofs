import ErdosProblems.Erdos1148.GeneralHyperbolaBoundary
import ErdosProblems.Erdos1148.HyperbolaErrorAssembly
import ErdosProblems.Erdos1148.NatSqrtRpow

/-! # The zeta-character estimate at arbitrary integer cutoffs -/

namespace Erdos1148.DukeArithmetic

theorem realZetaConvolution_general_hyperbola_error_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {N X : ℕ} (hN : 0 < N) (hNN : N * N ≤ X) (hX : X < (N + 1) * (N + 1)) :
    ‖weightedArithmeticPartialSum (realZetaConvolution χ) s X -
        (realZetaRegularized s * realDirichletValue χ s +
          (X : ℝ) ^ (1 - s) / (1 - s) * realDirichletValue χ 1)‖ ≤
      18 * ((q : ℝ) / (1 - s)) * (N : ℝ) ^ (1 - 2 * s) := by
  let W := (N : ℝ) ^ (1 - 2 * s)
  let Q := (q : ℝ) / (1 - s)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hW : 0 ≤ W := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hX0 : 0 < X := (Nat.mul_pos hN hN).trans_le hNN
  have hNX : N ≤ X := (show N ≤ N * N by nlinarith).trans hNN
  have hq : (q : ℝ) ≤ Q := by
    apply (le_div_iff₀ (by linarith : 0 < 1 - s)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) q]
  have hQ : 1 ≤ Q := (show (1 : ℝ) ≤ q by exact_mod_cast NeZero.pos q).trans hq
  have hscale : (N : ℝ) * (X : ℝ) ^ (-s) ≤ W := by
    calc
      _ ≤ (N : ℝ) * ((N : ℝ) * N) ^ (-s) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (mul_pos hN0 hN0)
          (by exact_mod_cast hNN) (by linarith)) hN0.le
      _ = _ := rpow_hyperbola_square_error hN0 s
  have hA : 2 * N * (X : ℝ) ^ (-s) ≤ 2 * Q * W := by
    calc
      _ ≤ 2 * W := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hscale (by norm_num)
      _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hQ) hW]
  have hB : 2 * q * N * (X : ℝ) ^ (-s) ≤ 2 * Q * W := by
    calc
      _ ≤ 2 * q * W := by
        rw [mul_assoc (2 * (q : ℝ))]
        exact mul_le_mul_of_nonneg_left hscale (by positivity)
      _ ≤ _ := by gcongr
  rw [realZetaConvolution_hyperbola_general χ s hNX hNN hX]
  have h := norm_hyperbola_error_le
    ((hyperbola_power_strip_error_le χ hs hs1 hNX).trans hA)
    ((hyperbola_character_strip_error_le χ hχ hs N hX0).trans hB)
    (hyperbola_cross_error_le χ hχ hs hs1 hN)
    (hyperbola_general_residue_tail_error_le χ hχ hs hs1 hN hX)
  convert h using 1
  dsimp only [Q, W]
  ring

theorem realZetaConvolution_nat_error_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) {s : ℝ} (hs : 1 / 2 ≤ s) (hs1 : s < 1)
    {X : ℕ} (hX : 0 < X) :
    ‖weightedArithmeticPartialSum (realZetaConvolution χ) s X -
        (realZetaRegularized s * realDirichletValue χ s +
          (X : ℝ) ^ (1 - s) / (1 - s) * realDirichletValue χ 1)‖ ≤
      36 * ((q : ℝ) / (1 - s)) * (X : ℝ) ^ (1 / 2 - s) := by
  calc
    _ ≤ 18 * ((q : ℝ) / (1 - s)) * (X.sqrt : ℝ) ^ (1 - 2 * s) :=
      realZetaConvolution_general_hyperbola_error_le χ hχ (by linarith) hs1
        (Nat.sqrt_pos.mpr hX) (Nat.sqrt_le X) (Nat.lt_succ_sqrt X)
    _ ≤ 18 * ((q : ℝ) / (1 - s)) * (2 * (X : ℝ) ^ (1 / 2 - s)) :=
      mul_le_mul_of_nonneg_left (nat_sqrt_rpow_error_le hX hs hs1.le) (by positivity)
    _ = _ := by ring

end Erdos1148.DukeArithmetic
