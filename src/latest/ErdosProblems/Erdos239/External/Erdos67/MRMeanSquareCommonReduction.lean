import ErdosProblems.Erdos239.External.Erdos67.MRPowerBlockDensity

/-!
# Reduction of the complex MR input to the common-denominator energy

This file composes the typical/atypical decomposition with the exact
merely-multiplicative prime-square correction.  After this composition,
the only analytic quantity left is the square energy of the
common-denominator Ramaré sum.
-/

open scoped BigOperators ComplexConjugate

namespace Erdos67

noncomputable section

/-- The common-denominator Ramaré energy over the target starting points. -/
def commonRamareMeanSquare
    (blocks : Finset (ℕ × ℕ)) (I : ℕ × ℕ)
    (f : ℕ → ℂ) (X H : ℕ) (alpha : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc X (2 * X),
    Complex.normSq
      (mrCommonDenominatorRamareShortSum (primesInBlock I)
        (typicalShortSupport blocks (2 * X + H) n H) f n alpha)

theorem sum_normSq_typical_le_common_add_primeSquare
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} (hI : I ∈ blocks)
    {X H : ℕ} (hlo : 0 < I.1) (f : ℕ → ℂ) (alpha : ℝ)
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ m : ℕ, 0 < m → ‖f m‖ ≤ 1) :
    ∑ n ∈ Finset.Ioc X (2 * X),
        Complex.normSq
          (typicalModulatedShortSum blocks (2 * X + H) f n H alpha) ≤
      2 * commonRamareMeanSquare blocks I f X H alpha +
        2 * (8 * (H : ℝ) ^ 2 * (2 * X + H : ℕ) / (I.1 : ℝ)) := by
  let E : ℕ → ℂ := fun n ↦
    typicalModulatedShortSum blocks (2 * X + H) f n H alpha -
      mrCommonDenominatorRamareShortSum (primesInBlock I)
        (typicalShortSupport blocks (2 * X + H) n H) f n alpha
  let C : ℕ → ℂ := fun n ↦
    mrCommonDenominatorRamareShortSum (primesInBlock I)
      (typicalShortSupport blocks (2 * X + H) n H) f n alpha
  have hrange : ∀ n ∈ Finset.Ioc X (2 * X),
      ∀ j ∈ Finset.Icc 1 H, n + j ≤ 2 * X + H := by
    intro n hn j hj
    have hn' := (Finset.mem_Ioc.mp hn).2
    have hj' := (Finset.mem_Icc.mp hj).2
    omega
  have herr :=
    sum_normSq_typical_sub_common_le_primeSquareTail_of_oneBounded
      hI f alpha hmul hbound hrange hlo
  calc
    (∑ n ∈ Finset.Ioc X (2 * X),
        Complex.normSq
          (typicalModulatedShortSum blocks (2 * X + H) f n H alpha)) =
        ∑ n ∈ Finset.Ioc X (2 * X),
          Complex.normSq (E n + C n) := by
      apply Finset.sum_congr rfl
      intro n hn
      congr 1
      dsimp [E, C]
      ring
    _ ≤ ∑ n ∈ Finset.Ioc X (2 * X),
          (2 * Complex.normSq (E n) + 2 * Complex.normSq (C n)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact normSq_add_le_two_mul (E n) (C n)
    _ = 2 * (∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq (C n)) +
          2 * (∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq (E n)) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    _ ≤ 2 * commonRamareMeanSquare blocks I f X H alpha +
          2 * (8 * (H : ℝ) ^ 2 * (2 * X + H : ℕ) / (I.1 : ℝ)) := by
      dsimp [commonRamareMeanSquare, C, E]
      gcongr

theorem sum_normSq_typical_le_common_add_eta
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} (hI : I ∈ blocks)
    {X H : ℕ} (hHX : H ≤ X) (hlo : 0 < I.1)
    {eta : ℝ} (hsmall : 24 / (I.1 : ℝ) ≤ eta)
    (f : ℕ → ℂ) (alpha : ℝ)
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ m : ℕ, 0 < m → ‖f m‖ ≤ 1) :
    ∑ n ∈ Finset.Ioc X (2 * X),
        Complex.normSq
          (typicalModulatedShortSum blocks (2 * X + H) f n H alpha) ≤
      2 * commonRamareMeanSquare blocks I f X H alpha +
        2 * eta * (H : ℝ) ^ 2 * (X : ℝ) := by
  have hbase := sum_normSq_typical_le_common_add_primeSquare
    (X := X) (H := H) hI hlo f alpha hmul hbound
  have hLnonneg : (0 : ℝ) ≤ (I.1 : ℝ) := by positivity
  have hZ : 2 * X + H ≤ 3 * X := by omega
  have htail :
      8 * (H : ℝ) ^ 2 * (2 * X + H : ℕ) / (I.1 : ℝ) ≤
        eta * (H : ℝ) ^ 2 * (X : ℝ) := by
    calc
      8 * (H : ℝ) ^ 2 * (2 * X + H : ℕ) / (I.1 : ℝ) ≤
          8 * (H : ℝ) ^ 2 * (3 * (X : ℝ)) / (I.1 : ℝ) := by
        apply div_le_div_of_nonneg_right _ hLnonneg
        apply mul_le_mul_of_nonneg_left
        · exact_mod_cast hZ
        · positivity
      _ = (24 / (I.1 : ℝ)) * ((H : ℝ) ^ 2 * (X : ℝ)) := by ring
      _ ≤ eta * ((H : ℝ) ^ 2 * (X : ℝ)) :=
        mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = eta * (H : ℝ) ^ 2 * (X : ℝ) := by ring
  have htwice := mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℝ) ≤ 2)
  exact hbase.trans (by
    simpa only [mul_assoc] using
      add_le_add_right htwice
        (2 * commonRamareMeanSquare blocks I f X H alpha))

/-- Exact final reduction before the analytic common-denominator estimate.
The atypical density costs `2 rho`, and the merely-multiplicative
prime-square branch costs `4 eta`. -/
theorem uncenteredShortIntervalMeanSquare_le_commonRamare_of_density
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} (hI : I ∈ blocks)
    {X H : ℕ} (hHX : H ≤ X) (hlo : 0 < I.1)
    {eta rho : ℝ} (hsmall : 24 / (I.1 : ℝ) ≤ eta)
    (f : ℕ → ℂ)
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ m : ℕ, 0 < m → ‖f m‖ ≤ 1)
    (hbad : ((atypicalFactorizationSet blocks (2 * X + H)).card : ℝ) ≤
      rho * X) :
    uncenteredShortIntervalMeanSquare f X H ≤
      4 * commonRamareMeanSquare blocks I f X H 0 +
        (4 * eta + 2 * rho) * (H : ℝ) ^ 2 * (X : ℝ) := by
  have htyp := sum_normSq_typical_le_common_add_eta
    hI hHX hlo hsmall f 0 hmul hbound
  have hbase :=
    uncenteredShortIntervalMeanSquare_le_typical_add_atypical
      blocks f X H hbound
  have hHsq : 0 ≤ (H : ℝ) ^ 2 := sq_nonneg _
  calc
    uncenteredShortIntervalMeanSquare f X H ≤
        2 * (∑ n ∈ Finset.Ioc X (2 * X),
          Complex.normSq
            (typicalModulatedShortSum blocks (2 * X + H) f n H 0)) +
        2 * (H : ℝ) ^ 2 *
          (atypicalFactorizationSet blocks (2 * X + H)).card := hbase
    _ ≤ 2 * (2 * commonRamareMeanSquare blocks I f X H 0 +
          2 * eta * (H : ℝ) ^ 2 * (X : ℝ)) +
        2 * (H : ℝ) ^ 2 * (rho * (X : ℝ)) := by
      gcongr
    _ = 4 * commonRamareMeanSquare blocks I f X H 0 +
        (4 * eta + 2 * rho) * (H : ℝ) ^ 2 * (X : ℝ) := by ring

/-- Once the common-denominator energy has budget `theta`, all finite and
sieve losses combine linearly into the exact target normalization. -/
theorem uncenteredShortIntervalMeanSquare_le_of_commonRamare
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} (hI : I ∈ blocks)
    {X H : ℕ} (hHX : H ≤ X) (hlo : 0 < I.1)
    {eta rho theta : ℝ} (hsmall : 24 / (I.1 : ℝ) ≤ eta)
    (f : ℕ → ℂ)
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ m : ℕ, 0 < m → ‖f m‖ ≤ 1)
    (hbad : ((atypicalFactorizationSet blocks (2 * X + H)).card : ℝ) ≤
      rho * X)
    (hcommon : commonRamareMeanSquare blocks I f X H 0 ≤
      theta * (H : ℝ) ^ 2 * (X : ℝ)) :
    uncenteredShortIntervalMeanSquare f X H ≤
      (4 * theta + 4 * eta + 2 * rho) *
        (H : ℝ) ^ 2 * (X : ℝ) := by
  have hbase := uncenteredShortIntervalMeanSquare_le_commonRamare_of_density
    hI hHX hlo hsmall f hmul hbound hbad
  calc
    uncenteredShortIntervalMeanSquare f X H ≤
        4 * commonRamareMeanSquare blocks I f X H 0 +
          (4 * eta + 2 * rho) * (H : ℝ) ^ 2 * (X : ℝ) := hbase
    _ ≤ 4 * (theta * (H : ℝ) ^ 2 * (X : ℝ)) +
          (4 * eta + 2 * rho) * (H : ℝ) ^ 2 * (X : ℝ) := by
      gcongr
    _ = (4 * theta + 4 * eta + 2 * rho) *
          (H : ℝ) ^ 2 * (X : ℝ) := by ring

end

end Erdos67
