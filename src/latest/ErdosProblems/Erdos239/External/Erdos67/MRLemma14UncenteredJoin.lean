import ErdosProblems.Erdos239.External.Erdos67.MRLemma14TwoLengthSplit

/-!
# Recovering an uncentered short sum from the two-length estimate

Source Lemma 14 controls the difference of two normalized averages.  This
file records the exact finite algebra which recovers the shorter uncentered
sum once the longer normalized average has been estimated.  The two costs
remain separate, as required by the quantitative MR parameter hierarchy.
-/

open scoped BigOperators
open Finset

namespace Erdos67

noncomputable section

/-- Square mean of the normalized dyadically restricted average at one
length. -/
def dyadicRestrictedNormalizedMeanSquare
    (S : Finset ℕ) (f : ℕ → ℂ) (X H : ℕ) : ℝ :=
  ∑ x ∈ Finset.Ioc X (2 * X),
    Complex.normSq (dyadicRestrictedShortAverage S f X x H)

/-- A uniform estimate for the long normalized average gives its square
mean with the exact cardinality `X`. -/
theorem dyadicRestrictedNormalizedMeanSquare_le_of_norm_le
    (S : Finset ℕ) (f : ℕ → ℂ) {X H : ℕ} {R : ℝ}
    (hR : 0 ≤ R)
    (havg : ∀ x ∈ Finset.Ioc X (2 * X),
      ‖dyadicRestrictedShortAverage S f X x H‖ ≤ R) :
    dyadicRestrictedNormalizedMeanSquare S f X H ≤ X * R ^ 2 := by
  unfold dyadicRestrictedNormalizedMeanSquare
  calc
    (∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq (dyadicRestrictedShortAverage S f X x H)) ≤
      ∑ _x ∈ Finset.Ioc X (2 * X), R ^ 2 := by
        apply Finset.sum_le_sum
        intro x hx
        rw [Complex.normSq_eq_norm_sq]
        exact (sq_le_sq₀ (norm_nonneg _) hR).2 (havg x hx)
    _ = X * R ^ 2 := by
      have hcard : (Finset.Ioc X (2 * X)).card = X := by simp; omega
      simp [hcard]

/-- The unnormalized shorter sum is `H₁` times the two-length difference
plus `H₁` times the longer normalized average. -/
theorem uncenteredShortIntervalMeanSquare_dyadicRestricted_le_twoLength_add_long
    (S : Finset ℕ) (f : ℕ → ℂ)
    {X H₁ H₂ : ℕ} (hH₁ : 0 < H₁) (hH₂ : 0 < H₂) :
    uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient S f X) X H₁ ≤
      2 * (H₁ : ℝ) ^ 2 *
        (dyadicTwoLengthShortMeanSquare S f X H₁ H₂ +
          dyadicRestrictedNormalizedMeanSquare S f X H₂) := by
  classical
  unfold uncenteredShortIntervalMeanSquare
    dyadicTwoLengthShortMeanSquare dyadicRestrictedNormalizedMeanSquare
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hx
  have hshort (H : ℕ) (hH : 0 < H) :
      (∑ j ∈ Finset.Icc 1 H,
          dyadicRestrictedCoefficient S f X (x + j)) =
        (H : ℂ) * dyadicRestrictedShortAverage S f X x H := by
    unfold dyadicRestrictedShortAverage
    rw [sum_Icc_add_eq_sum_Ioc]
    rw [mul_div_cancel₀]
    exact_mod_cast hH.ne'
  rw [hshort H₁ hH₁]
  let A : ℂ := dyadicRestrictedShortAverage S f X x H₁ -
    dyadicRestrictedShortAverage S f X x H₂
  let B : ℂ := dyadicRestrictedShortAverage S f X x H₂
  have hdecomp : dyadicRestrictedShortAverage S f X x H₁ = A + B := by
    dsimp [A, B]
    ring
  conv_lhs => rw [hdecomp]
  rw [Complex.normSq_mul, Complex.normSq_natCast]
  have hsum := normSq_sub_le_two_mul_add A (-B)
  simp only [sub_neg_eq_add, Complex.normSq_neg] at hsum
  calc
    (H₁ : ℝ) * H₁ * Complex.normSq (A + B) =
        (H₁ : ℝ) ^ 2 * Complex.normSq (A + B) := by ring
    _ ≤ (H₁ : ℝ) ^ 2 *
        (2 * (Complex.normSq A + Complex.normSq B)) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = 2 * (H₁ : ℝ) ^ 2 * Complex.normSq
            (dyadicRestrictedShortAverage S f X x H₁ -
              dyadicRestrictedShortAverage S f X x H₂) +
          2 * (H₁ : ℝ) ^ 2 *
            Complex.normSq (dyadicRestrictedShortAverage S f X x H₂) := by
      dsimp [A, B]
      ring

/-- Quantitative composition with the source-Lemma-14 limit join. -/
theorem uncenteredShortIntervalMeanSquare_dyadicRestricted_le_of_uniform_high
    (S : Finset ℕ) (f : ℕ → ℂ)
    {X H₁ H₂ : ℕ} (hX : 0 < X) (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    {T E : ℝ} (hT : 0 < T)
    (hhigh : ∀ U : ℝ, T ≤ U →
      dyadicTwoLengthPerronHighMeanSquare S f X X H₁ H₂ T U ≤ E) :
    uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient S f X) X H₁ ≤
      2 * (H₁ : ℝ) ^ 2 *
        (4 * dyadicTwoLengthCorrectedPerronMeanSquare S f X H₁ H₂ T +
          8 * E + dyadicRestrictedNormalizedMeanSquare S f X H₂) := by
  have hbase :=
    uncenteredShortIntervalMeanSquare_dyadicRestricted_le_twoLength_add_long
      S f (X := X) hH₁ hH₂
  have htwo := dyadicTwoLengthShortMeanSquare_le_of_uniform_high
    S f hX hH₁ hH₂ hT hhigh
  calc
    uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient S f X) X H₁ ≤
      2 * (H₁ : ℝ) ^ 2 *
        (dyadicTwoLengthShortMeanSquare S f X H₁ H₂ +
          dyadicRestrictedNormalizedMeanSquare S f X H₂) := hbase
    _ ≤ 2 * (H₁ : ℝ) ^ 2 *
        (4 * dyadicTwoLengthCorrectedPerronMeanSquare S f X H₁ H₂ T +
          8 * E + dyadicRestrictedNormalizedMeanSquare S f X H₂) := by
      gcongr

/-- Fully normalized parameter form.  The three dimensionless costs are:
the source low-frequency Taylor error, the uniform high-frequency energy,
and the longer-average energy. -/
theorem uncenteredShortIntervalMeanSquare_dyadicRestricted_le_source_parameters
    (S : Finset ℕ) {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X H₁ H₂ K : ℕ}
    (hX : 0 < X) (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    (hK : 0 < K) (hH₁H₂ : H₁ ≤ H₂) (hscale : K * H₂ ≤ X)
    {T Ehigh Elong : ℝ} (hT : 0 < T)
    (hhigh : ∀ U : ℝ, T ≤ U →
      dyadicTwoLengthPerronHighMeanSquare S f X X H₁ H₂ T U ≤
        X * Ehigh)
    (hlong : dyadicRestrictedNormalizedMeanSquare S f X H₂ ≤
      X * Elong) :
    uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient S f X) X H₁ ≤
      (256 * T ^ 4 / (K : ℝ) ^ 2 + 64 / (H₁ : ℝ) ^ 2 +
          16 * Ehigh + 2 * Elong) * (H₁ : ℝ) ^ 2 * X := by
  have hbase :=
    uncenteredShortIntervalMeanSquare_dyadicRestricted_le_of_uniform_high
      S f hX hH₁ hH₂ hT hhigh
  have hlow := dyadicTwoLengthCorrectedPerronMeanSquare_low_le_scale
    S hf hX hH₁ hH₂ hK hH₁H₂ hscale hT.le
  have hXnonneg : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hHsq : (0 : ℝ) ≤ (H₁ : ℝ) ^ 2 := sq_nonneg _
  calc
    uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient S f X) X H₁ ≤
      2 * (H₁ : ℝ) ^ 2 *
        (4 * dyadicTwoLengthCorrectedPerronMeanSquare S f X H₁ H₂ T +
          8 * (X * Ehigh) +
            dyadicRestrictedNormalizedMeanSquare S f X H₂) := hbase
    _ ≤ 2 * (H₁ : ℝ) ^ 2 *
        (4 * (X * (32 * T ^ 4 / (K : ℝ) ^ 2 +
              8 / (H₁ : ℝ) ^ 2)) +
          8 * (X * Ehigh) + X * Elong) := by
      gcongr
    _ = (256 * T ^ 4 / (K : ℝ) ^ 2 + 64 / (H₁ : ℝ) ^ 2 +
          16 * Ehigh + 2 * Elong) * (H₁ : ℝ) ^ 2 * X := by
      ring

end

end Erdos67
