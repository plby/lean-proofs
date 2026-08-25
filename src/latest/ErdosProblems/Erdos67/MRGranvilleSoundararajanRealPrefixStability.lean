import ErdosProblems.Erdos67.MRGranvilleSoundararajanReal
import ErdosProblems.Erdos67.MRRealMeanSignDichotomy

/-!
# Real prefix stability from the Granville--Soundararajan variation estimate

This file packages the slow-variation half of the real Halasz dichotomy in
the exact normalization used by the centered long-average reduction.  The
comparison mean is the prefix mean at the left endpoint.  Thus no desired
short-interval estimate occurs among the hypotheses.
-/

open scoped BigOperators ComplexConjugate

namespace Erdos67

noncomputable section

/-- An explicit absolute constant for the real GS prefix comparison. -/
def realGSPrefixVariationConstant : ℝ :=
  6 * (HalberstamScratch.explicitMassConstant 2 1 + 1) * Real.exp 8

theorem realGSPrefixVariationConstant_nonneg :
    0 ≤ realGSPrefixVariationConstant := by
  unfold realGSPrefixVariationConstant
  exact mul_nonneg
    (mul_nonneg (by norm_num)
      (add_nonneg
        (HalberstamScratch.explicitMassConstant_nonneg (by norm_num) (by norm_num))
        zero_le_one))
    (Real.exp_pos 8).le

/-- Every positive prefix mean of a real-valued coefficient lies on the
real axis. -/
theorem positivePrefixMean_im_eq_zero_of_real
    {f : ℕ → ℂ} (hreal : ∀ n, 0 < n → conj (f n) = f n) (N : ℕ) :
    (positivePrefixMean f N).im = 0 := by
  have hprefix : positivePrefixSum f N = ∑ n ∈ Finset.Ioc 0 N, f n := by
    have h := sum_Ioc_eq_positivePrefixSum_sub f (Nat.zero_le N)
    simpa [positivePrefixSum] using h.symm
  apply Complex.conj_eq_iff_im.mp
  unfold positivePrefixMean
  rw [hprefix]
  rw [map_div₀, map_sum]
  congr 1
  ·
    apply Finset.sum_congr rfl
    intro n hn
    exact hreal n (Finset.mem_Ioc.mp hn).1
  · simp

/-- Uniform real-sign recombination used after the GS near-twist comparison:
a rough signed comparison and slow variation of the absolute mean imply
slow variation of the mean itself. -/
theorem uniform_positivePrefixMean_stable_of_real_of_rough_of_norm_stable
    {f : ℕ → ℂ} (hreal : ∀ n, 0 < n → conj (f n) = f n)
    {X : ℕ} {epsilon delta : ℝ}
    (hrough : ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
      ‖positivePrefixMean f Z - positivePrefixMean f X‖ ≤
        ‖positivePrefixMean f X‖ / 2 + epsilon)
    (hnorm : ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
      |‖positivePrefixMean f Z‖ - ‖positivePrefixMean f X‖| ≤ delta) :
    ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
      ‖positivePrefixMean f Z - positivePrefixMean f X‖ ≤
        max delta (2 * epsilon) := by
  intro Z hXZ hZ
  exact norm_sub_le_max_normDiff_two_mul_of_real
    (positivePrefixMean_im_eq_zero_of_real hreal Z)
    (positivePrefixMean_im_eq_zero_of_real hreal X)
    (hrough Z hXZ hZ) (hnorm Z hXZ hZ)

/-- Uniform GS variation on `[X,3X]`, expressed only through the
zero-frequency distance at the common upper cutoff `3X`. -/
theorem norm_positivePrefixMean_sub_left_le_realGS
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hreal : ∀ n, 0 < n → conj (f n) = f n)
    (hbound : ∀ n, ‖f n‖ ≤ 1)
    {X Z : ℕ} (hX : 2 ≤ X) (hXZ : X ≤ Z) (hZ : Z ≤ 3 * X) :
    ‖positivePrefixMean f Z - positivePrefixMean f X‖ ≤
      realGSPrefixVariationConstant *
        Real.exp (pretentiousDistSq f (archimedeanTwist 0) (3 * X)) /
          Real.log (X : ℝ) := by
  have hXpos : 0 < X := by omega
  have hZtwo : 2 ≤ Z := hX.trans hXZ
  have hXR : (0 : ℝ) < X := by positivity
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hlogZ : 0 < Real.log (Z : ℝ) :=
    Real.log_pos (by exact_mod_cast hZtwo)
  have hdist :
      pretentiousDistSq f (archimedeanTwist 0) Z ≤
        pretentiousDistSq f (archimedeanTwist 0) (3 * X) := by
    apply pretentiousDistSq_mono hZ
    · intro p hp
      exact hbound p
    · intro p hp
      rw [archimedeanTwist_zero_of_pos hp.pos]
      simp
  have heuler :
      gsEulerExponent f Z ≤
        pretentiousDistSq f (archimedeanTwist 0) (3 * X) + 8 :=
    (gsEulerExponent_le_pretentiousDistSq_zero_add_eight
      hreal (fun n _hn ↦ hbound n) Z).trans (add_le_add hdist le_rfl)
  have hexp :
      Real.exp (gsEulerExponent f Z) ≤
        Real.exp 8 *
          Real.exp (pretentiousDistSq f (archimedeanTwist 0) (3 * X)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hratio : (2 : ℝ) * Z / X ≤ 6 := by
    apply (div_le_iff₀ hXR).2
    have hZR : (Z : ℝ) ≤ 3 * X := by exact_mod_cast hZ
    nlinarith
  have hlogmono : Real.log (X : ℝ) ≤ Real.log (Z : ℝ) := by
    exact Real.log_le_log hXR (by exact_mod_cast hXZ)
  have hinvlog : (Real.log (Z : ℝ))⁻¹ ≤ (Real.log (X : ℝ))⁻¹ :=
    by simpa only [one_div] using one_div_le_one_div_of_le hlogX hlogmono
  have hconstant :
      0 ≤ HalberstamScratch.explicitMassConstant 2 1 + 1 :=
    add_nonneg
      (HalberstamScratch.explicitMassConstant_nonneg (by norm_num) (by norm_num))
      zero_le_one
  have hbase := norm_positivePrefixMean_sub_le_gsEulerExponent
    hmul hbound hXpos hXZ hZtwo
  calc
    ‖positivePrefixMean f Z - positivePrefixMean f X‖ ≤
        (2 / (X : ℝ)) *
          ((HalberstamScratch.explicitMassConstant 2 1 + 1) *
            (Z : ℝ) / Real.log (Z : ℝ) *
              Real.exp (gsEulerExponent f Z)) := hbase
    _ = ((2 : ℝ) * Z / X) *
          (HalberstamScratch.explicitMassConstant 2 1 + 1) *
          (Real.log (Z : ℝ))⁻¹ * Real.exp (gsEulerExponent f Z) := by
      field_simp
    _ ≤ 6 * (HalberstamScratch.explicitMassConstant 2 1 + 1) *
          (Real.log (Z : ℝ))⁻¹ * Real.exp (gsEulerExponent f Z) := by
      gcongr
    _ ≤ 6 * (HalberstamScratch.explicitMassConstant 2 1 + 1) *
          (Real.log (X : ℝ))⁻¹ * Real.exp (gsEulerExponent f Z) := by
      gcongr
    _ ≤ 6 * (HalberstamScratch.explicitMassConstant 2 1 + 1) *
          (Real.log (X : ℝ))⁻¹ *
            (Real.exp 8 *
              Real.exp (pretentiousDistSq f (archimedeanTwist 0) (3 * X))) := by
      exact mul_le_mul_of_nonneg_left hexp
        (mul_nonneg (mul_nonneg (by norm_num) hconstant) (inv_nonneg.mpr hlogX.le))
    _ = realGSPrefixVariationConstant *
          Real.exp (pretentiousDistSq f (archimedeanTwist 0) (3 * X)) /
            Real.log (X : ℝ) := by
      unfold realGSPrefixVariationConstant
      field_simp

/-- The source-sized slow-variation branch.  A zero-frequency distance of at
most `3/4 log log X` gives the desired `log(X)^(-1/4)` prefix stability. -/
theorem norm_positivePrefixMean_sub_left_le_log_rpow_neg_quarter
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hreal : ∀ n, 0 < n → conj (f n) = f n)
    (hbound : ∀ n, ‖f n‖ ≤ 1)
    {X Z : ℕ} (hX : 3 ≤ X) (hXZ : X ≤ Z) (hZ : Z ≤ 3 * X)
    (hsmall : pretentiousDistSq f (archimedeanTwist 0) (3 * X) ≤
      (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ))) :
    ‖positivePrefixMean f Z - positivePrefixMean f X‖ ≤
      realGSPrefixVariationConstant *
        (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ) := by
  have hXtwo : 2 ≤ X := by omega
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hvariation := norm_positivePrefixMean_sub_left_le_realGS
    hmul hreal hbound hXtwo hXZ hZ
  have hexp :
      Real.exp (pretentiousDistSq f (archimedeanTwist 0) (3 * X)) ≤
        (Real.log (X : ℝ)) ^ (3 / 4 : ℝ) := by
    calc
      _ ≤ Real.exp ((3 / 4 : ℝ) * Real.log (Real.log (X : ℝ))) :=
        Real.exp_le_exp.mpr hsmall
      _ = _ := by
        rw [Real.rpow_def_of_pos hlogX]
        congr 1
        ring
  calc
    ‖positivePrefixMean f Z - positivePrefixMean f X‖ ≤
        realGSPrefixVariationConstant *
          Real.exp (pretentiousDistSq f (archimedeanTwist 0) (3 * X)) /
            Real.log (X : ℝ) := hvariation
    _ ≤ realGSPrefixVariationConstant *
          (Real.log (X : ℝ)) ^ (3 / 4 : ℝ) /
            Real.log (X : ℝ) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp realGSPrefixVariationConstant_nonneg)
        hlogX.le
    _ = realGSPrefixVariationConstant *
          (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one]
      calc
        realGSPrefixVariationConstant *
              (Real.log (X : ℝ)) ^ (3 / 4 : ℝ) *
            (Real.log (X : ℝ)) ^ (-(1 : ℝ)) =
            realGSPrefixVariationConstant *
              ((Real.log (X : ℝ)) ^ (3 / 4 : ℝ) *
                (Real.log (X : ℝ)) ^ (-(1 : ℝ))) := by ring
        _ = realGSPrefixVariationConstant *
              (Real.log (X : ℝ)) ^ ((3 / 4 : ℝ) + -(1 : ℝ)) := by
          rw [Real.rpow_add hlogX]
        _ = _ := by norm_num

/-- Existential form of the slow-variation branch, matching the `mu`
quantifier of the centered-long reduction. -/
theorem exists_uniform_positivePrefixMean_stable_of_zeroDistance_small
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hreal : ∀ n, 0 < n → conj (f n) = f n)
    (hbound : ∀ n, ‖f n‖ ≤ 1)
    {X : ℕ} (hX : 3 ≤ X)
    (hsmall : pretentiousDistSq f (archimedeanTwist 0) (3 * X) ≤
      (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ))) :
    ∃ mu : ℂ, ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
      ‖positivePrefixMean f Z - mu‖ ≤
        realGSPrefixVariationConstant *
          (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ) := by
  refine ⟨positivePrefixMean f X, ?_⟩
  intro Z hXZ hZ
  exact norm_positivePrefixMean_sub_left_le_log_rpow_neg_quarter
    hmul hreal hbound hX hXZ hZ hsmall

/-- Direct centered-long consequence of the GS small-distance branch. -/
theorem centeredNormalizedShortAverageMeanSquare_le_of_zeroDistance_small
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hreal : ∀ n, 0 < n → conj (f n) = f n)
    (hbound : ∀ n, ‖f n‖ ≤ 1)
    {X H : ℕ} (hX : 3 ≤ X) (hH : 0 < H) (hHX : H ≤ X)
    (hsmall : pretentiousDistSq f (archimedeanTwist 0) (3 * X) ≤
      (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ))) :
    centeredNormalizedShortAverageMeanSquare f X H ≤
      (X : ℝ) *
        (8 * (X : ℝ) / (H : ℝ) *
          (realGSPrefixVariationConstant *
            (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ))) ^ 2 := by
  have hlogX : 0 ≤ Real.log (X : ℝ) :=
    (Real.log_pos (by exact_mod_cast (show 1 < X by omega))).le
  have hepsilon : 0 ≤ realGSPrefixVariationConstant *
      (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ) :=
    mul_nonneg realGSPrefixVariationConstant_nonneg (Real.rpow_nonneg hlogX _)
  apply centeredNormalizedShortAverageMeanSquare_le_of_prefixStable
    (mu := positivePrefixMean f X)
    (epsilon := realGSPrefixVariationConstant *
      (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ))
    f (by omega) hH hHX hepsilon
  intro Z hXZ hZ
  exact norm_positivePrefixMean_sub_left_le_log_rpow_neg_quarter
    hmul hreal hbound hX hXZ hZ hsmall

/-- Two-length short-interval recombination with the GS small-distance
centered-long term already discharged. -/
theorem shortIntervalMeanSquare_le_twoDyadicTwoLength_add_of_zeroDistance_small
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hreal : ∀ n, 0 < n → conj (f n) = f n)
    (hbound : ∀ n, ‖f n‖ ≤ 1)
    {X H₁ H₂ : ℕ}
    (hX : 3 ≤ X) (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    (hH₁X : H₁ ≤ X) (hH₂X : H₂ ≤ X)
    (hsmall : pretentiousDistSq f (archimedeanTwist 0) (3 * X) ≤
      (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ))) :
    shortIntervalMeanSquare f X H₁ ≤
      4 * (H₁ : ℝ) ^ 2 *
        (dyadicTwoLengthShortMeanSquareAt
            (Finset.Ioc X (2 * X)) f X X H₁ H₂ +
          dyadicTwoLengthShortMeanSquareAt
            (Finset.Ioc (2 * X) (4 * X)) f (2 * X) X H₁ H₂) +
      2 * (H₁ : ℝ) ^ 2 *
        ((X : ℝ) *
          (8 * (X : ℝ) / (H₂ : ℝ) *
            (realGSPrefixVariationConstant *
              (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ))) ^ 2) := by
  have hlogX : 0 ≤ Real.log (X : ℝ) :=
    (Real.log_pos (by exact_mod_cast (show 1 < X by omega))).le
  have hepsilon : 0 ≤ realGSPrefixVariationConstant *
      (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ) :=
    mul_nonneg realGSPrefixVariationConstant_nonneg (Real.rpow_nonneg hlogX _)
  apply shortIntervalMeanSquare_le_twoDyadicTwoLength_add_prefixStable
    (mu := positivePrefixMean f X)
    (epsilon := realGSPrefixVariationConstant *
      (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ))
    f (by omega) hH₁ hH₂ hH₁X hH₂X hepsilon
  intro Z hXZ hZ
  exact norm_positivePrefixMean_sub_left_le_log_rpow_neg_quarter
    hmul hreal hbound hX hXZ hZ hsmall

/-- Exact dichotomy supplied by the GS half: either all prefixes on
`[X,3X]` are stable around the common left prefix mean with the source
`log^(-1/4)` scale, or the zero-frequency distance exceeds the threshold
required by the complementary Halasz mean theorem. -/
theorem real_prefixStable_or_zeroDistance_large
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hreal : ∀ n, 0 < n → conj (f n) = f n)
    (hbound : ∀ n, ‖f n‖ ≤ 1)
    {X : ℕ} (hX : 3 ≤ X) :
    (∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
      ‖positivePrefixMean f Z - positivePrefixMean f X‖ ≤
        realGSPrefixVariationConstant *
          (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ)) ∨
      (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) <
        pretentiousDistSq f (archimedeanTwist 0) (3 * X) := by
  by_cases hsmall : pretentiousDistSq f (archimedeanTwist 0) (3 * X) ≤
      (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ))
  · left
    intro Z hXZ hZ
    exact norm_positivePrefixMean_sub_left_le_log_rpow_neg_quarter
      hmul hreal hbound hX hXZ hZ hsmall
  · right
    exact lt_of_not_ge hsmall

/-- The same dichotomy with the existential common mean exposed exactly as
required by the E69 real-major specialization. -/
theorem exists_uniform_positivePrefixMean_stable_or_zeroDistance_large
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hreal : ∀ n, 0 < n → conj (f n) = f n)
    (hbound : ∀ n, ‖f n‖ ≤ 1)
    {X : ℕ} (hX : 3 ≤ X) :
    (∃ mu : ℂ, ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
      ‖positivePrefixMean f Z - mu‖ ≤
        realGSPrefixVariationConstant *
          (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ)) ∨
      (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) <
        pretentiousDistSq f (archimedeanTwist 0) (3 * X) := by
  rcases real_prefixStable_or_zeroDistance_large hmul hreal hbound hX with
    hstable | hlarge
  · exact Or.inl ⟨positivePrefixMean f X, hstable⟩
  · exact Or.inr hlarge

end

end Erdos67
