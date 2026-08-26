import ErdosProblems.Erdos1148.HyperbolaBoundaryEstimates

/-! # A cancellation estimate for the convolution of two nonprincipal characters -/

namespace Erdos1148.DukeArithmetic

open Finset ArithmeticFunction

theorem hyperbola_twisted_character_strip_error_le {q r : ℕ} [NeZero r]
    (χ : DirichletCharacter ℝ q) (ψ : DirichletCharacter ℝ r) (hψ : ψ ≠ 1)
    {s : ℝ} (hs : 0 < s) (N : ℕ) {X : ℕ} (hX : 0 < X) :
    ‖(∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s) * χ n * realDirichletPartialSum ψ s (X / n)) -
        realDirichletPartialSum χ s N * realDirichletValue ψ s‖ ≤
      2 * r * N * (X : ℝ) ^ (-s) := by
  rw [realDirichletPartialSum_eq_sum_Ioc, sum_mul, ← sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Ioc 0 N,
        ‖(n : ℝ) ^ (-s) * χ n * realDirichletPartialSum ψ s (X / n) -
          (n : ℝ) ^ (-s) * χ n * realDirichletValue ψ s‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ioc 0 N, 2 * r * (X : ℝ) ^ (-s) := by
      apply sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.mp hn).1
      rw [← mul_sub, norm_mul, norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
      calc
        _ ≤ (n : ℝ) ^ (-s) * 1 * (2 * r * ((X : ℝ) / n) ^ (-s)) := by
          gcongr
          · exact χ.norm_le_one _
          · exact realDirichletPartialSum_div_error_le ψ hψ hs (mem_Ioc.mp hn).1 hX
        _ = _ := by
          rw [show (n : ℝ) ^ (-s) * 1 * (2 * r * ((X : ℝ) / n) ^ (-s)) =
            2 * r * ((n : ℝ) ^ (-s) * ((X : ℝ) / n) ^ (-s)) by ring,
            rpow_hyperbola_error_weight (Nat.cast_nonneg X) hn0]
    _ = _ := by simp only [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]; ring

lemma realCharacterConvolution_hyperbola {q r : ℕ}
    (χ : DirichletCharacter ℝ q) (ψ : DirichletCharacter ℝ r) (s : ℝ)
    {N X : ℕ} (hNX : N ≤ X) (hNN : N * N ≤ X) (hX : X < (N + 1) * (N + 1)) :
    weightedArithmeticPartialSum (realCharacterArithmetic χ * realCharacterArithmetic ψ) s X =
      (∑ m ∈ Ioc 0 N, (m : ℝ) ^ (-s) * χ m * realDirichletPartialSum ψ s (X / m)) +
      (∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s) * ψ n * realDirichletPartialSum χ s (X / n)) -
      realDirichletPartialSum χ s N * realDirichletPartialSum ψ s N := by
  have h := weighted_convolution_hyperbola (realCharacterArithmetic χ)
    (realCharacterArithmetic ψ) s hNX hNX hNN hX
  simp only [weighted_realCharacter_eq_partialSum] at h
  rw [h]
  congr 2
  · apply sum_congr rfl
    intro m hm
    rw [realCharacterArithmetic, ← χ.apply_eq_toArithmeticFunction_apply
      (Nat.ne_zero_of_lt (mem_Ioc.mp hm).1)]
  · apply sum_congr rfl
    intro n hn
    rw [realCharacterArithmetic, ← ψ.apply_eq_toArithmeticFunction_apply
      (Nat.ne_zero_of_lt (mem_Ioc.mp hn).1)]

theorem realCharacterConvolution_hyperbola_error_le {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℝ q) (ψ : DirichletCharacter ℝ r) (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    {s : ℝ} (hs : 0 < s) {N X : ℕ} (hN : 0 < N)
    (hNN : N * N ≤ X) (hX : X < (N + 1) * (N + 1)) :
    ‖weightedArithmeticPartialSum (realCharacterArithmetic χ * realCharacterArithmetic ψ) s X -
        realDirichletValue χ s * realDirichletValue ψ s‖ ≤
      8 * q * r * (N : ℝ) ^ (1 - 2 * s) := by
  let A := ∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s) * χ n * realDirichletPartialSum ψ s (X / n)
  let B := ∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s) * ψ n * realDirichletPartialSum χ s (X / n)
  let W := (N : ℝ) ^ (1 - 2 * s)
  have hW : 0 ≤ W := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hX0 : 0 < X := (Nat.mul_pos hN hN).trans_le hNN
  have hNX : N ≤ X := (show N ≤ N * N by nlinarith).trans hNN
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hr : (1 : ℝ) ≤ r := by exact_mod_cast NeZero.pos r
  have hp : (X : ℝ) ^ (-s) ≤ ((N : ℝ) * N) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos hN0 hN0) (by exact_mod_cast hNN) (by linarith)
  have hscale : (N : ℝ) * (X : ℝ) ^ (-s) ≤ W := by
    calc
      _ ≤ (N : ℝ) * ((N : ℝ) * N) ^ (-s) := mul_le_mul_of_nonneg_left hp hN0.le
      _ = _ := rpow_hyperbola_square_error hN0 s
  have hA : ‖A - realDirichletPartialSum χ s N * realDirichletValue ψ s‖ ≤ 2 * r * W := by
    have h := hyperbola_twisted_character_strip_error_le χ ψ hψ hs N hX0
    rw [mul_assoc (2 * (r : ℝ))] at h
    exact h.trans (mul_le_mul_of_nonneg_left hscale (by positivity))
  have hB : ‖B - realDirichletPartialSum ψ s N * realDirichletValue χ s‖ ≤ 2 * q * W := by
    have h := hyperbola_twisted_character_strip_error_le ψ χ hχ hs N hX0
    rw [mul_assoc (2 * (q : ℝ))] at h
    exact h.trans (mul_le_mul_of_nonneg_left hscale (by positivity))
  have hcross : ‖(realDirichletValue χ s - realDirichletPartialSum χ s N) *
      (realDirichletValue ψ s - realDirichletPartialSum ψ s N)‖ ≤ 4 * q * r * W := by
    rw [norm_mul]
    calc
      _ ≤ (2 * q * (N : ℝ) ^ (-s)) * (2 * r * (N : ℝ) ^ (-s)) :=
        mul_le_mul (realDirichletValue_sub_partialSum_norm_le_nat χ hχ hs hN)
          (realDirichletValue_sub_partialSum_norm_le_nat ψ hψ hs hN) (norm_nonneg _) (by positivity)
      _ = 4 * q * r * ((N : ℝ) ^ (-s) * (N : ℝ) ^ (-s)) := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← Real.rpow_add hN0]
        exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have heq :
      weightedArithmeticPartialSum (realCharacterArithmetic χ * realCharacterArithmetic ψ) s X -
      realDirichletValue χ s * realDirichletValue ψ s =
      (A - realDirichletPartialSum χ s N * realDirichletValue ψ s) +
      (B - realDirichletPartialSum ψ s N * realDirichletValue χ s) -
      (realDirichletValue χ s - realDirichletPartialSum χ s N) *
        (realDirichletValue ψ s - realDirichletPartialSum ψ s N) := by
    rw [realCharacterConvolution_hyperbola χ ψ s hNX hNN hX]
    dsimp only [A, B]
    ring
  rw [heq]
  calc
    _ ≤ ‖A - realDirichletPartialSum χ s N * realDirichletValue ψ s‖ +
      ‖B - realDirichletPartialSum ψ s N * realDirichletValue χ s‖ +
      ‖(realDirichletValue χ s - realDirichletPartialSum χ s N) *
        (realDirichletValue ψ s - realDirichletPartialSum ψ s N)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 2 * r * W + 2 * q * W + 4 * q * r * W := add_le_add (add_le_add hA hB) hcross
    _ ≤ _ := by
      have hqr : (q : ℝ) ≤ q * r := by nlinarith [Nat.cast_nonneg (α := ℝ) q]
      have hrq : (r : ℝ) ≤ q * r := by nlinarith [Nat.cast_nonneg (α := ℝ) r]
      nlinarith [mul_nonneg (sub_nonneg.mpr hqr) hW, mul_nonneg (sub_nonneg.mpr hrq) hW]

end Erdos1148.DukeArithmetic
