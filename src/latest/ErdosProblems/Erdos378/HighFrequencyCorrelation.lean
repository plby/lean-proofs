/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.HigherDerivative
import ErdosProblems.Erdos378.BilinearReciprocal

/-!
# High-frequency reciprocal correlations

This file transports the arbitrary-order derivative estimate to the product
intervals occurring as off-diagonal correlations in Vaughan's identity.
-/

open scoped BigOperators ComplexConjugate

namespace Erdos378
namespace HighFrequencyCorrelation

open PrimeReciprocal
open BilinearReciprocal
open ReciprocalExponential
open HigherDerivative

noncomputable section

/-- The right side of the normalized `2^h`-moment estimate. -/
def reciprocalMomentMajorant
    (X : ℝ) (A N : ℕ) (Ls : List ℕ) : ℝ :=
  vdcMomentConstant Ls.length *
    (differencingError Ls + 1 / (8 * (N : ℝ)) +
      (3 * ((A + N : ℕ) : ℝ) ^ (Ls.length + 2) /
        (16 * (N : ℝ) * X * ((Ls.length + 1).factorial : ℝ))) *
        reciprocalShiftFactor Ls)

lemma reciprocalMomentMajorant_nonneg
    {X : ℝ} (hX : 0 < X) (A : ℕ) {N : ℕ} (hN : 0 < N)
    (Ls : List ℕ) :
    0 ≤ reciprocalMomentMajorant X A N Ls := by
  unfold reciprocalMomentMajorant
  have hC := (vdcMomentConstant_pos Ls.length).le
  have hErr := differencingError_nonneg Ls
  have hFactor := reciprocalShiftFactor_nonneg Ls
  positivity

/-- Root form of the moment majorant. -/
def reciprocalHighDerivativeBound
    (X : ℝ) (A N : ℕ) (Ls : List ℕ) : ℝ :=
  8 * (N : ℝ) *
    (reciprocalMomentMajorant X A N Ls) ^
      ((2 ^ Ls.length : ℕ) : ℝ)⁻¹

lemma reciprocalHighDerivativeBound_nonneg
    {X : ℝ} (hX : 0 < X) (A : ℕ) {N : ℕ} (hN : 0 < N)
    (Ls : List ℕ) :
    0 ≤ reciprocalHighDerivativeBound X A N Ls := by
  unfold reciprocalHighDerivativeBound
  exact mul_nonneg (by positivity) <|
    Real.rpow_nonneg (reciprocalMomentMajorant_nonneg hX A hN Ls) _

lemma reciprocalProductIntervalSum_eq_translated_Icc
    (X : ℝ) {a b : ℕ} (hab : a ≤ b) :
    reciprocalProductIntervalSum X 1 a b =
      ∑ n ∈ Finset.Icc 1 (b - a),
        e (-X / ((a + n : ℕ) : ℝ)) := by
  rw [reciprocalProductIntervalSum_eq_phase X (by omega : 0 < (1 : ℕ))]
  simp only [Nat.cast_one, div_one]
  rw [sum_Icc_one_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  unfold reciprocalPhase
  congr 2
  norm_cast
  omega

/-- Arbitrary-order reciprocal estimate on a half-open interval. -/
theorem norm_reciprocalProductIntervalSum_le_highDerivative
    (X : ℝ) (hX : 0 < X) {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (Ls : List ℕ) (hcut : ∀ L ∈ Ls, 1 ≤ L)
    (hfit : Ls.sum + 2 ≤ b - a)
    (hsmall : X * ((Ls.length + 1).factorial : ℝ) *
        (Ls.prod : ℝ) / (a : ℝ) ^ (Ls.length + 2) ≤ 1 / 2) :
    ‖reciprocalProductIntervalSum X 1 a b‖ ≤
      reciprocalHighDerivativeBound X a (b - a) Ls := by
  let N := b - a
  have hN : 0 < N := by dsimp only [N]; omega
  have hmoment := reciprocal_exponential_sum_high_derivative
    X hX ha hN Ls hcut (by simpa only [N] using hfit) hsmall
  have hsum : reciprocalProductIntervalSum X 1 a b =
      ∑ n ∈ Finset.Icc 1 N,
        e (-X / ((a + n : ℕ) : ℝ)) := by
    simpa only [N] using
      reciprocalProductIntervalSum_eq_translated_Icc X hab.le
  rw [← hsum] at hmoment
  let S : ℝ := ‖reciprocalProductIntervalSum X 1 a b‖ /
    (8 * (N : ℝ))
  let R : ℝ := reciprocalMomentMajorant X a N Ls
  let P : ℕ := 2 ^ Ls.length
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact reciprocalMomentMajorant_nonneg hX a hN Ls
  have hP : (0 : ℝ) < P := by dsimp only [P]; positivity
  have hpow : S ^ P ≤ R := by
    simpa only [S, R, P, reciprocalMomentMajorant, N] using hmoment
  have hpowR : Real.rpow S (P : ℝ) ≤ R := by
    calc
      Real.rpow S (P : ℝ) = S ^ P := Real.rpow_natCast S P
      _ ≤ R := hpow
  have hroot : S ≤ R ^ ((P : ℝ)⁻¹) :=
    (Real.le_rpow_inv_iff_of_pos hS hR hP).2 hpowR
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  unfold reciprocalHighDerivativeBound
  dsimp only [S, R, P] at hroot
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 8 * (N : ℝ))] at hroot
  simpa only [N, mul_comm] using hroot

/-- The cutoff correlation, in its increasing orientation, inherits the
high-derivative interval bound. -/
theorem norm_reciprocalCutoffWeight_correlation_le_highDerivative
    {X : ℝ} (hX : 0 < X) {x y m₀ m₁ r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r < s)
    (ha : 0 < max m₀ (max (x / r) (x / s)))
    (hab : max m₀ (max (x / r) (x / s)) <
      min m₁ (min (y / r) (y / s)))
    (Ls : List ℕ) (hcut : ∀ L ∈ Ls, 1 ≤ L)
    (hfit : Ls.sum + 2 ≤
      min m₁ (min (y / r) (y / s)) -
        max m₀ (max (x / r) (x / s)))
    (hsmall :
      (X * ((s - r : ℕ) : ℝ) / ((r * s : ℕ) : ℝ)) *
          ((Ls.length + 1).factorial : ℝ) * (Ls.prod : ℝ) /
            ((max m₀ (max (x / r) (x / s)) : ℕ) : ℝ) ^
              (Ls.length + 2) ≤ 1 / 2) :
    ‖∑ m ∈ Finset.Ioc m₀ m₁,
        reciprocalCutoffWeight X x y m s *
          conj (reciprocalCutoffWeight X x y m r)‖ ≤
      reciprocalHighDerivativeBound
        (X * ((s - r : ℕ) : ℝ) / ((r * s : ℕ) : ℝ))
        (max m₀ (max (x / r) (x / s)))
        (min m₁ (min (y / r) (y / s)) -
          max m₀ (max (x / r) (x / s))) Ls := by
  have hfreq : 0 < X * ((s - r : ℕ) : ℝ) / ((r * s : ℕ) : ℝ) := by
    have hgap : 0 < s - r := Nat.sub_pos_of_lt hrs
    positivity
  rw [norm_sum_reciprocalCutoffWeight_correlation_comm
    X x y m₀ m₁ s r]
  rw [sum_reciprocalCutoffWeight_correlation_eq_phase X hr hs hrs.le]
  exact norm_reciprocalProductIntervalSum_le_highDerivative
    _ hfreq ha hab Ls hcut hfit hsmall

end

end HighFrequencyCorrelation
end Erdos378
