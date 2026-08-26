import ErdosProblems.Erdos1148.CharacterConvolutionEstimate
import ErdosProblems.Erdos1148.NatSqrtRpow

/-! # Pair-character convolution estimates at arbitrary real cutoffs -/

namespace Erdos1148.DukeArithmetic

theorem realCharacterConvolution_error_le {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℝ q) (ψ : DirichletCharacter ℝ r) (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    {s : ℝ} (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1) {X : ℕ} (hX : 0 < X) :
    ‖weightedArithmeticPartialSum (realCharacterArithmetic χ * realCharacterArithmetic ψ) s X -
        realDirichletValue χ s * realDirichletValue ψ s‖ ≤
      16 * q * r * (X : ℝ) ^ (1 / 2 - s) := by
  have hN := Nat.sqrt_pos.mpr hX
  calc
    _ ≤ 8 * q * r * (X.sqrt : ℝ) ^ (1 - 2 * s) :=
      realCharacterConvolution_hyperbola_error_le χ ψ hχ hψ (by linarith) hN
        (Nat.sqrt_le X) (Nat.lt_succ_sqrt X)
    _ ≤ 8 * q * r * (2 * (X : ℝ) ^ (1 / 2 - s)) :=
      mul_le_mul_of_nonneg_left (nat_sqrt_rpow_error_le hX hs hs1) (by positivity)
    _ = _ := by ring

theorem realCharacterConvolution_floor_error_le {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℝ q) (ψ : DirichletCharacter ℝ r) (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    {s : ℝ} (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1) {x : ℝ} (hx : 1 ≤ x) :
    ‖weightedArithmeticPartialSum (realCharacterArithmetic χ * realCharacterArithmetic ψ) s ⌊x⌋₊ -
        realDirichletValue χ s * realDirichletValue ψ s‖ ≤
      32 * q * r * x ^ (1 / 2 - s) := by
  have hX : 0 < ⌊x⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hx)
  calc
    _ ≤ 16 * q * r * (⌊x⌋₊ : ℝ) ^ (1 / 2 - s) :=
      realCharacterConvolution_error_le χ ψ hχ hψ hs hs1 hX
    _ ≤ 16 * q * r * (2 * x ^ (1 / 2 - s)) :=
      mul_le_mul_of_nonneg_left (nat_floor_rpow_error_le hx hs hs1) (by positivity)
    _ = _ := by ring

end Erdos1148.DukeArithmetic
