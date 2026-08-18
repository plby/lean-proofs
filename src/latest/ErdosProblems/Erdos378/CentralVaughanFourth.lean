/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.CentralVaughan

/-!
# A uniform central-range estimate for Vaughan's fourth term

The hypotheses of the uniform estimate are deliberately quantitative.  They
only ask for the adaptive correlation estimate at scales which can actually
meet the product interval.  Blocks below that scale, or below either Vaughan
cutoff, vanish exactly.
-/

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace Erdos378
namespace CentralVaughanFourth

open BoundedGaps.Maynard
open PrimeReciprocal
open BilinearReciprocal
open VaughanReciprocalBlocks
open VaughanReciprocalEstimate
open AdaptiveShifts
open CentralCorrelation
open CentralVaughan

noncomputable section

def centralFourthUniformMajorant (y T : ℕ) (delta : ℝ) : ℝ :=
  (8 / 3 : ℝ) * (y : ℝ) ^ 2 *
    (Real.log (2 * (y : ℝ))) ^ 2 *
    (Real.log (T : ℝ) + 3) ^ 2 * (2 / (T : ℝ) + delta)

lemma centralFourthUniformMajorant_nonneg
    {y T : ℕ} {delta : ℝ} (hT : 0 < T) (hdelta : 0 ≤ delta) :
    0 ≤ centralFourthUniformMajorant y T delta := by
  unfold centralFourthUniformMajorant
  positivity

private lemma long_le_product_mul_two_div
    {L S T : ℕ} (hL : 0 < L) (hT : 0 < T) (hTS : T < 2 * S) :
    (L : ℝ) ≤ (L : ℝ) * (S : ℝ) * (2 / (T : ℝ)) := by
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hTSR : (T : ℝ) ≤ 2 * S := by exact_mod_cast hTS.le
  have hone : (1 : ℝ) ≤ (S : ℝ) * (2 / (T : ℝ)) := by
    rw [show (S : ℝ) * (2 / (T : ℝ)) =
      (2 * (S : ℝ)) / T by ring]
    exact (le_div_iff₀ hTR).2 (by simpa using hTSR)
  calc
    (L : ℝ) = (L : ℝ) * 1 := by ring
    _ ≤ (L : ℝ) * ((S : ℝ) * (2 / (T : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hone (by positivity)
    _ = (L : ℝ) * (S : ℝ) * (2 / (T : ℝ)) := by ring

lemma centralVaughanBlockMajorant_le_uniform
    {y T M K : ℕ} {delta : ℝ}
    (hT : 0 < T) (hM : 0 < M) (hK : 0 < K)
    (hprod : M * K ≤ y) (hTM : T < 2 * M) (hTK : T < 2 * K)
    (hdelta : 0 ≤ delta)
    (henv : adaptiveCorrelationEnvelope (max M K) ≤
      delta * (max M K : ℕ)) :
    centralVaughanBlockMajorant T M K ≤
      centralFourthUniformMajorant y T delta := by
  have hprodR : (M : ℝ) * K ≤ y := by exact_mod_cast hprod
  have hlogT : 0 ≤ Real.log (T : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hT)
  rcases le_total K M with hKM | hMK
  · have hmax : max M K = M := max_eq_left hKM
    have hmin : min M K = K := min_eq_right hKM
    have hMy : M ≤ y := by nlinarith
    have hlogM0 : 0 ≤ Real.log (2 * (M : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * M by omega))
    have hlog : Real.log (2 * (M : ℝ)) ≤ Real.log (2 * (y : ℝ)) :=
      Real.log_le_log (by positivity) (by exact_mod_cast Nat.mul_le_mul_left 2 hMy)
    have hlong := long_le_product_mul_two_div hM hT hTK
    have hoff : adaptiveCorrelationEnvelope M * (K : ℝ) ≤
        ((M : ℝ) * K) * delta := by
      calc
        adaptiveCorrelationEnvelope M * (K : ℝ) ≤
            (delta * (M : ℝ)) * K := by
          exact mul_le_mul_of_nonneg_right (by simpa [hmax] using henv) (by positivity)
        _ = ((M : ℝ) * K) * delta := by ring
    have hbracket : (M : ℝ) +
        adaptiveCorrelationEnvelope M * (K : ℝ) ≤
        ((M : ℝ) * K) * (2 / (T : ℝ) + delta) := by
      calc
        _ ≤ ((M : ℝ) * K) * (2 / (T : ℝ)) +
            ((M : ℝ) * K) * delta := add_le_add hlong hoff
        _ = _ := by ring
    unfold centralVaughanBlockMajorant centralFourthUniformMajorant
    simp only [hmax, hmin]
    have hfac : 0 ≤ 2 / (T : ℝ) + delta := by positivity
    have hbracket0 : 0 ≤ (M : ℝ) +
        adaptiveCorrelationEnvelope M * (K : ℝ) := by
      have hE := adaptiveCorrelationEnvelope_nonneg (show 1 ≤ M by omega)
      positivity
    calc
      _ = (8 / 3 : ℝ) * ((M : ℝ) * K) *
          (Real.log (2 * (M : ℝ))) ^ 2 *
          (Real.log (T : ℝ) + 3) ^ 2 *
          ((M : ℝ) + adaptiveCorrelationEnvelope M * K) := by ring
      _ ≤ (8 / 3 : ℝ) * ((M : ℝ) * K) *
          (Real.log (2 * (M : ℝ))) ^ 2 *
          (Real.log (T : ℝ) + 3) ^ 2 *
          (((M : ℝ) * K) * (2 / (T : ℝ) + delta)) := by
        gcongr
      _ ≤ (8 / 3 : ℝ) * (y : ℝ) *
          (Real.log (2 * (y : ℝ))) ^ 2 *
          (Real.log (T : ℝ) + 3) ^ 2 *
          ((y : ℝ) * (2 / (T : ℝ) + delta)) := by
        gcongr
      _ = _ := by ring
  · have hmax : max M K = K := max_eq_right hMK
    have hmin : min M K = M := min_eq_left hMK
    have hMy : M ≤ y := by nlinarith
    have hlogM0 : 0 ≤ Real.log (2 * (M : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * M by omega))
    have hlog : Real.log (2 * (M : ℝ)) ≤ Real.log (2 * (y : ℝ)) :=
      Real.log_le_log (by positivity) (by exact_mod_cast Nat.mul_le_mul_left 2 hMy)
    have hlong := long_le_product_mul_two_div hK hT hTM
    have hoff : adaptiveCorrelationEnvelope K * (M : ℝ) ≤
        ((M : ℝ) * K) * delta := by
      calc
        adaptiveCorrelationEnvelope K * (M : ℝ) ≤
            (delta * (K : ℝ)) * M := by
          exact mul_le_mul_of_nonneg_right (by simpa [hmax] using henv) (by positivity)
        _ = ((M : ℝ) * K) * delta := by ring
    have hbracket : (K : ℝ) +
        adaptiveCorrelationEnvelope K * (M : ℝ) ≤
        ((M : ℝ) * K) * (2 / (T : ℝ) + delta) := by
      calc
        _ ≤ ((K : ℝ) * M) * (2 / (T : ℝ)) +
            ((M : ℝ) * K) * delta := add_le_add hlong hoff
        _ = _ := by ring
    unfold centralVaughanBlockMajorant centralFourthUniformMajorant
    simp only [hmax, hmin]
    have hfac : 0 ≤ 2 / (T : ℝ) + delta := by positivity
    have hbracket0 : 0 ≤ (K : ℝ) +
        adaptiveCorrelationEnvelope K * (M : ℝ) := by
      have hE := adaptiveCorrelationEnvelope_nonneg (show 1 ≤ K by omega)
      positivity
    calc
      _ = (8 / 3 : ℝ) * ((M : ℝ) * K) *
          (Real.log (2 * (M : ℝ))) ^ 2 *
          (Real.log (T : ℝ) + 3) ^ 2 *
          ((K : ℝ) + adaptiveCorrelationEnvelope K * M) := by ring
      _ ≤ (8 / 3 : ℝ) * ((M : ℝ) * K) *
          (Real.log (2 * (M : ℝ))) ^ 2 *
          (Real.log (T : ℝ) + 3) ^ 2 *
          (((M : ℝ) * K) * (2 / (T : ℝ) + delta)) := by
        gcongr
      _ ≤ (8 / 3 : ℝ) * (y : ℝ) *
          (Real.log (2 * (y : ℝ))) ^ 2 *
          (Real.log (T : ℝ) + 3) ^ 2 *
          ((y : ℝ) * (2 / (T : ℝ) + delta)) := by
        gcongr
      _ = _ := by ring

/-- A dyadic block is controlled uniformly as soon as every scale large
enough to meet the product interval has the central correlation estimate and
the stated envelope ratio. -/
theorem norm_central_fourthDyadicBlock_sq_le_uniform
    {X : ℝ} {x y T alpha beta : ℕ} {delta : ℝ}
    (hT : 0 < T) (hdelta : 0 ≤ delta)
    (hsize : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y →
      centralCorrelationSizeCondition L)
    (henv : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y →
      adaptiveCorrelationEnvelope L ≤ delta * L)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x) :
    ‖reciprocalVaughanFourthDyadicBlock X T T x y alpha beta‖ ^ 2 ≤
      centralFourthUniformMajorant y T delta := by
  let M : ℕ := 2 ^ alpha
  let K : ℕ := 2 ^ beta
  have hM : 0 < M := by dsimp only [M]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  rw [reciprocalVaughanFourthDyadicBlock_eq_full]
  simp only [reciprocalVaughanFourthFullDyadicBlock, pow_succ,
    Nat.mul_comm]
  change ‖reciprocalBilinearBlock X x y M (2 * M) K (2 * K)
      (cutoffMangoldtCoefficient T) (cutoffFourthCoefficient T)‖ ^ 2 ≤ _
  by_cases hyprod : y < M * K
  · rw [reciprocalVaughanBlock_eq_zero_of_product_above
      X T T x y M K hyprod, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    exact centralFourthUniformMajorant_nonneg hT hdelta
  have hprod : M * K ≤ y := Nat.le_of_not_gt hyprod
  by_cases hxprod : 4 * M * K ≤ x
  · rw [reciprocalVaughanBlock_eq_zero_of_product_below
      X T T x y M K hxprod, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    exact centralFourthUniformMajorant_nonneg hT hdelta
  have hxprod' : x < 4 * M * K := Nat.lt_of_not_ge hxprod
  by_cases hTM : 2 * M ≤ T
  · have hTMR : ((2 * M : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast hTM
    rw [reciprocalVaughanBlock_eq_zero_of_mangoldt_cutoff
      X T T x y M K hTMR, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    exact centralFourthUniformMajorant_nonneg hT hdelta
  have hTM' : T < 2 * M := Nat.lt_of_not_ge hTM
  by_cases hTK : 2 * K ≤ T
  · have hTKR : ((2 * K : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast hTK
    rw [reciprocalVaughanBlock_eq_zero_of_fourth_cutoff
      X T T x y M K hTKR, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    exact centralFourthUniformMajorant_nonneg hT hdelta
  have hTK' : T < 2 * K := Nat.lt_of_not_ge hTK
  let L := max M K
  have hprodL : M * K ≤ L ^ 2 := by
    dsimp only [L]
    rcases le_total K M with hKM | hMK
    · rw [max_eq_left hKM]
      nlinarith
    · rw [max_eq_right hMK]
      nlinarith
  have hxL : x < 4 * L ^ 2 := hxprod'.trans_le (by
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 4 hprodL)
  have hMy : M ≤ y := by
    calc
      M = M * 1 := by simp
      _ ≤ M * K := Nat.mul_le_mul_left M (by omega)
      _ ≤ y := hprod
  have hKy : K ≤ y := by
    calc
      K = 1 * K := by simp
      _ ≤ M * K := Nat.mul_le_mul_right K (by omega)
      _ ≤ y := hprod
  have hLy : L ≤ y := max_le hMy hKy
  have hblock := norm_central_reciprocalVaughanBlock_sq_le
    (X := X) (U := (T : ℝ)) (V := (T : ℝ))
    (x := x) (y := y) (M := M) (K := K)
    (by exact_mod_cast hT) hM hK (hsize L hxL hLy) hXlo hXhi hyx
  exact hblock.trans (centralVaughanBlockMajorant_le_uniform
    hT hM hK hprod hTM' hTK' hdelta (henv L hxL hLy))

/-- The exact two-dimensional dyadic decomposition, summed with the uniform
central block estimate. -/
theorem norm_weightedVaughanIntervalFour_central_le
    {X : ℝ} {x y T : ℕ} {delta : ℝ}
    (hT : 0 < T) (hdelta : 0 ≤ delta)
    (hsize : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y →
      centralCorrelationSizeCondition L)
    (henv : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y →
      adaptiveCorrelationEnvelope L ≤ delta * L)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x) :
    ‖weightedVaughanIntervalFour (reciprocalWeight X) T T x y‖ ≤
      ((dyadicExponentRange y).card : ℝ) ^ 2 *
        Real.sqrt (centralFourthUniformMajorant y T delta) := by
  let A := centralFourthUniformMajorant y T delta
  have hA : 0 ≤ A := centralFourthUniformMajorant_nonneg hT hdelta
  have hblock (alpha beta : ℕ) :
      ‖reciprocalVaughanFourthDyadicBlock X T T x y alpha beta‖ ≤
        Real.sqrt A := by
    apply (Real.le_sqrt (norm_nonneg _) hA).2
    exact norm_central_fourthDyadicBlock_sq_le_uniform
      hT hdelta hsize henv hXlo hXhi hyx
  rw [weightedVaughanIntervalFour_reciprocal_eq_neg_sum_dyadicBlocks
    X (by exact_mod_cast hT) (by exact_mod_cast hT) x y, norm_neg]
  calc
    ‖∑ alpha ∈ dyadicExponentRange y,
        ∑ beta ∈ dyadicExponentRange y,
          reciprocalVaughanFourthDyadicBlock X T T x y alpha beta‖ ≤
      ∑ alpha ∈ dyadicExponentRange y,
        ‖∑ beta ∈ dyadicExponentRange y,
          reciprocalVaughanFourthDyadicBlock X T T x y alpha beta‖ :=
      norm_sum_le _ _
    _ ≤ ∑ alpha ∈ dyadicExponentRange y,
        ∑ beta ∈ dyadicExponentRange y,
          ‖reciprocalVaughanFourthDyadicBlock X T T x y alpha beta‖ := by
      apply Finset.sum_le_sum
      intro alpha halpha
      exact norm_sum_le _ _
    _ ≤ ∑ _alpha ∈ dyadicExponentRange y,
        ∑ _beta ∈ dyadicExponentRange y, Real.sqrt A := by
      apply Finset.sum_le_sum
      intro alpha halpha
      apply Finset.sum_le_sum
      intro beta hbeta
      exact hblock alpha beta
    _ = ((dyadicExponentRange y).card : ℝ) ^ 2 * Real.sqrt A := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      push_cast
      ring

end

end CentralVaughanFourth
end Erdos378
