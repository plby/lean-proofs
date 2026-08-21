import ErdosProblems.Erdos239.External.Erdos67.MRRealPrefixMinimizerDichotomy

/-!
# Complete-multiplicative real prefix stability adapter

The current source A.10 global-secondary identity is proved for completely
multiplicative coefficients.  This adapter retains that honest hypothesis
while reusing the real minimizer dichotomy, whose split itself only needs
ordinary multiplicativity.
-/

open Filter
open scoped ComplexConjugate

namespace Erdos67

noncomputable section

theorem eventually_uniform_real_complete_prefix_stable_one_thousandth_of_branches
    {C_halasz C_far : ℝ}
    (hhalasz : ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ),
      IsMultiplicativeOnPositiveNat f →
      IsCompletelyMultiplicativeOnPositive f →
      (∀ n, 0 < n → conj (f n) = f n) →
      (∀ n, ‖f n‖ ≤ 1) →
      MRArchimedeanNonpretentious f (realPrefixMovingThreshold X) (3 * X) →
      (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) <
        pretentiousDistSq f (archimedeanTwist 0) (3 * X) →
      ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
        ‖positivePrefixMean f Z‖ ≤
          C_halasz * (Real.log (X : ℝ)) ^ (-(1 / 1000 : ℝ)))
    (hfar : ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ),
      IsMultiplicativeOnPositiveNat f →
      IsCompletelyMultiplicativeOnPositive f →
      (∀ n, 0 < n → conj (f n) = f n) →
      (∀ n, ‖f n‖ ≤ 1) →
      (∃ t₀ : ℝ,
        (Real.log (X : ℝ)) ^ (4 : ℕ) < |t₀| ∧
        |t₀| ≤ 3 * X ∧
        pretentiousDistSq f (archimedeanTwist t₀) (3 * X) <
          realPrefixMovingThreshold X) →
      (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) <
        pretentiousDistSq f (archimedeanTwist 0) (3 * X) →
      ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
        ‖positivePrefixMean f Z‖ ≤
          C_far * (Real.log (X : ℝ)) ^ (-(1 / 1000 : ℝ))) :
    ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ),
      IsMultiplicativeOnPositiveNat f →
      IsCompletelyMultiplicativeOnPositive f →
      (∀ n, 0 < n → conj (f n) = f n) →
      (∀ n, ‖f n‖ ≤ 1) →
      ∃ mu : ℂ, ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
        ‖positivePrefixMean f Z - mu‖ ≤
          max C_halasz (max C_far realGSSignedPrefixStabilityConstant) *
            (Real.log (X : ℝ)) ^ (-(1 / 1000 : ℝ)) := by
  filter_upwards
      [eventually_real_prefix_halaszLargeZero_or_farLargeZero_or_stable,
        hhalasz, hfar, eventually_ge_atTop 3]
      with X hsplit hhalaszX hfarX hX
  intro f hmul hcomp hreal hbound
  have hlog : 1 ≤ Real.log (X : ℝ) := by
    have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
    have hexp : Real.exp 1 < (X : ℝ) :=
      Real.exp_one_lt_three.trans_le (by exact_mod_cast hX)
    exact Real.exp_le_exp.mp
      (hexp.le.trans_eq (Real.exp_log hXpos).symm)
  have hrpow : 0 ≤ (Real.log (X : ℝ)) ^ (-(1 / 1000 : ℝ)) :=
    Real.rpow_nonneg (zero_lt_one.trans_le hlog).le _
  have hrpowQuarter :
      (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ) ≤
        (Real.log (X : ℝ)) ^ (-(1 / 1000 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hlog
    norm_num
  rcases hsplit f hmul hreal hbound with
    ⟨hnonpret, hzero⟩ | ⟨hfarBranch, hzero⟩ | hstable
  · refine ⟨0, ?_⟩
    intro Z hXZ hZX
    simpa using
      (hhalaszX f hmul hcomp hreal hbound hnonpret hzero Z hXZ hZX).trans
        (mul_le_mul_of_nonneg_right
          (le_max_left C_halasz
            (max C_far realGSSignedPrefixStabilityConstant)) hrpow)
  · refine ⟨0, ?_⟩
    intro Z hXZ hZX
    simpa using
      (hfarX f hmul hcomp hreal hbound hfarBranch hzero Z hXZ hZX).trans
        (mul_le_mul_of_nonneg_right
          ((le_max_left C_far realGSSignedPrefixStabilityConstant).trans
            (le_max_right C_halasz
              (max C_far realGSSignedPrefixStabilityConstant))) hrpow)
  · obtain ⟨mu, hmu⟩ := hstable
    refine ⟨mu, ?_⟩
    intro Z hXZ hZX
    calc
      ‖positivePrefixMean f Z - mu‖ ≤
          realGSSignedPrefixStabilityConstant *
            (Real.log (X : ℝ)) ^ (-1 / 4 : ℝ) := hmu Z hXZ hZX
      _ ≤ realGSSignedPrefixStabilityConstant *
          (Real.log (X : ℝ)) ^ (-(1 / 1000 : ℝ)) :=
        mul_le_mul_of_nonneg_left hrpowQuarter
          realGSSignedPrefixStabilityConstant_nonneg
      _ ≤ max C_halasz
            (max C_far realGSSignedPrefixStabilityConstant) *
          (Real.log (X : ℝ)) ^ (-(1 / 1000 : ℝ)) :=
        mul_le_mul_of_nonneg_right
          ((le_max_right C_far realGSSignedPrefixStabilityConstant).trans
            (le_max_right C_halasz
              (max C_far realGSSignedPrefixStabilityConstant))) hrpow

end

end Erdos67

#print axioms
  Erdos67.eventually_uniform_real_complete_prefix_stable_one_thousandth_of_branches
