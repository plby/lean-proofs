/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.InverseSquareHigherDerivative
import ErdosProblems.Erdos378.PrimeReciprocal

/-!
# Inverse-square product phases

This file transports the arbitrary-order estimate for `e (-X / t²)` to
half-open integer intervals and records the correlation identity needed in
Vaughan's bilinear term.
-/

open scoped BigOperators ComplexConjugate

namespace Erdos378
namespace InverseSquareCorrelation

open PrimeReciprocal
open ReciprocalExponential
open HigherDerivative
open InverseSquareHigherDerivative

noncomputable section

/-- The inverse-square phase used in the `J = 2` part of Granville--Ramaré's
prime fractional-part lemma. -/
def inverseSquareWeight (X : ℝ) (n : ℕ) : ℂ :=
  e (-X / (n : ℝ) ^ 2)

@[simp] theorem norm_inverseSquareWeight (X : ℝ) (n : ℕ) :
    ‖inverseSquareWeight X n‖ = 1 := by
  simp [inverseSquareWeight, norm_e]

/-- An inverse-square phase sum over a product interval. -/
def inverseSquareProductIntervalSum (X : ℝ) (t a b : ℕ) : ℂ :=
  ∑ r ∈ Finset.Ioc a b, inverseSquareWeight X (t * r)

lemma inverseSquareProductIntervalSum_eq_scaled
    (X : ℝ) {t a b : ℕ} (ht : 0 < t) :
    inverseSquareProductIntervalSum X t a b =
      inverseSquareProductIntervalSum (X / (t : ℝ) ^ 2) 1 a b := by
  unfold inverseSquareProductIntervalSum inverseSquareWeight
  apply Finset.sum_congr rfl
  intro r hr
  have hrpos : 0 < r := Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hr).1
  congr 1
  push_cast
  field_simp [show (t : ℝ) ≠ 0 by positivity,
    show (r : ℝ) ≠ 0 by positivity]

/-- Correlating two product phases leaves another inverse-square phase in
the common factor. -/
theorem inverseSquareWeight_mul_conj_product
    (X : ℝ) {m r s : ℕ} (hm : 0 < m) (hr : 0 < r) (hrs : r ≤ s) :
    inverseSquareWeight X (m * r) * conj (inverseSquareWeight X (m * s)) =
      inverseSquareWeight
        (X * (((s : ℕ) ^ 2 - r ^ 2 : ℕ) : ℝ) /
          (((r * s : ℕ) : ℝ) ^ 2)) m := by
  have hs : 0 < s := hr.trans_le hrs
  have hrsq : r ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hrs 2
  rw [inverseSquareWeight, inverseSquareWeight, inverseSquareWeight,
    ← e_sub]
  congr 1
  push_cast [hrsq]
  field_simp [show (m : ℝ) ≠ 0 by positivity,
    show (r : ℝ) ≠ 0 by positivity,
    show (s : ℝ) ≠ 0 by positivity]
  ring

/-- Correlation identity on an arbitrary consecutive interval. -/
theorem sum_inverseSquareWeight_product_correlation
    (X : ℝ) {a b r s : ℕ} (hr : 0 < r) (hrs : r ≤ s) :
    (∑ m ∈ Finset.Ioc a b,
        inverseSquareWeight X (m * r) *
          conj (inverseSquareWeight X (m * s))) =
      inverseSquareProductIntervalSum
        (X * (((s : ℕ) ^ 2 - r ^ 2 : ℕ) : ℝ) /
          (((r * s : ℕ) : ℝ) ^ 2)) 1 a b := by
  unfold inverseSquareProductIntervalSum
  simp only [one_mul]
  apply Finset.sum_congr rfl
  intro m hm
  exact inverseSquareWeight_mul_conj_product X
    (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hm).1) hr hrs

/-- The right side of the normalized `2^h`-moment estimate. -/
def inverseSquareMomentMajorant
    (X : ℝ) (A N : ℕ) (Ls : List ℕ) : ℝ :=
  vdcMomentConstant Ls.length *
    (differencingError Ls + 1 / (8 * (N : ℝ)) +
      (3 * ((A + N : ℕ) : ℝ) ^ (Ls.length + 3) /
        (16 * (N : ℝ) * X * ((Ls.length + 2).factorial : ℝ))) *
        reciprocalShiftFactor Ls)

lemma inverseSquareMomentMajorant_nonneg
    {X : ℝ} (hX : 0 < X) (A : ℕ) {N : ℕ} (hN : 0 < N)
    (Ls : List ℕ) :
    0 ≤ inverseSquareMomentMajorant X A N Ls := by
  unfold inverseSquareMomentMajorant
  have hC := (vdcMomentConstant_pos Ls.length).le
  have hErr := differencingError_nonneg Ls
  have hFactor := reciprocalShiftFactor_nonneg Ls
  positivity

/-- Root form of the inverse-square moment majorant. -/
def inverseSquareHighDerivativeBound
    (X : ℝ) (A N : ℕ) (Ls : List ℕ) : ℝ :=
  8 * (N : ℝ) *
    (inverseSquareMomentMajorant X A N Ls) ^
      ((2 ^ Ls.length : ℕ) : ℝ)⁻¹

lemma inverseSquareHighDerivativeBound_nonneg
    {X : ℝ} (hX : 0 < X) (A : ℕ) {N : ℕ} (hN : 0 < N)
    (Ls : List ℕ) :
    0 ≤ inverseSquareHighDerivativeBound X A N Ls := by
  unfold inverseSquareHighDerivativeBound
  exact mul_nonneg (by positivity) <|
    Real.rpow_nonneg (inverseSquareMomentMajorant_nonneg hX A hN Ls) _

lemma inverseSquareProductIntervalSum_eq_translated_Icc
    (X : ℝ) {a b : ℕ} (hab : a ≤ b) :
    inverseSquareProductIntervalSum X 1 a b =
      ∑ n ∈ Finset.Icc 1 (b - a),
        e (-X / ((a + n : ℕ) : ℝ) ^ 2) := by
  unfold inverseSquareProductIntervalSum inverseSquareWeight
  simp only [one_mul]
  rw [sum_Ioc_eq_sum_range, sum_Icc_one_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  have heq : a + (i + 1) = a + 1 + i := by omega
  rw [heq]

/-- Arbitrary-order inverse-square estimate on a half-open interval. -/
theorem norm_inverseSquareProductIntervalSum_le_highDerivative
    (X : ℝ) (hX : 0 < X) {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (Ls : List ℕ) (hcut : ∀ L ∈ Ls, 1 ≤ L)
    (hfit : Ls.sum + 2 ≤ b - a)
    (hsmall : X * ((Ls.length + 2).factorial : ℝ) *
        (Ls.prod : ℝ) / (a : ℝ) ^ (Ls.length + 3) ≤ 1 / 2) :
    ‖inverseSquareProductIntervalSum X 1 a b‖ ≤
      inverseSquareHighDerivativeBound X a (b - a) Ls := by
  let N := b - a
  have hN : 0 < N := by dsimp only [N]; omega
  have hmoment := inverseSquare_exponential_sum_high_derivative
    X hX ha hN Ls hcut (by simpa only [N] using hfit) hsmall
  have hsum : inverseSquareProductIntervalSum X 1 a b =
      ∑ n ∈ Finset.Icc 1 N,
        e (-X / ((a + n : ℕ) : ℝ) ^ 2) := by
    simpa only [N] using
      inverseSquareProductIntervalSum_eq_translated_Icc X hab.le
  rw [← hsum] at hmoment
  let S : ℝ := ‖inverseSquareProductIntervalSum X 1 a b‖ /
    (8 * (N : ℝ))
  let R : ℝ := inverseSquareMomentMajorant X a N Ls
  let P : ℕ := 2 ^ Ls.length
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact inverseSquareMomentMajorant_nonneg hX a hN Ls
  have hP : (0 : ℝ) < P := by dsimp only [P]; positivity
  have hpow : S ^ P ≤ R := by
    simpa only [S, R, P, inverseSquareMomentMajorant, N] using hmoment
  have hpowR : Real.rpow S (P : ℝ) ≤ R := by
    calc
      Real.rpow S (P : ℝ) = S ^ P := Real.rpow_natCast S P
      _ ≤ R := hpow
  have hroot : S ≤ R ^ ((P : ℝ)⁻¹) :=
    (Real.le_rpow_inv_iff_of_pos hS hR hP).2 hpowR
  unfold inverseSquareHighDerivativeBound
  dsimp only [S, R, P] at hroot
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 8 * (N : ℝ))] at hroot
  simpa only [N, mul_comm] using hroot

/-- The trivial interval-length estimate. -/
lemma norm_inverseSquareProductIntervalSum_le_length
    (X : ℝ) (a b : ℕ) :
    ‖inverseSquareProductIntervalSum X 1 a b‖ ≤ (b - a : ℕ) := by
  unfold inverseSquareProductIntervalSum
  calc
    ‖∑ r ∈ Finset.Ioc a b, inverseSquareWeight X (1 * r)‖ ≤
        ∑ r ∈ Finset.Ioc a b, ‖inverseSquareWeight X (1 * r)‖ :=
      norm_sum_le _ _
    _ = ∑ _r ∈ Finset.Ioc a b, (1 : ℝ) := by simp
    _ = (b - a : ℕ) := by simp

end

end InverseSquareCorrelation
end Erdos378
