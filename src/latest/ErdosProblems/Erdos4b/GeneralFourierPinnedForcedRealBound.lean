/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedForcedSourceBound
import ErdosProblems.Erdos4b.GeneralFourierPinnedPrimeErrorTransfer
import ErdosProblems.Erdos4b.SingularWeightedPrimeAverage

/-!
# From the complex forced kernel to the literal nonnegative collision weight

The normalization uses the actual finite prime count. Taking real parts
of the checked complex error and bounding the main term by its norm
gives an upper bound for each literal residue-restricted square sum.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem real_le_main_norm_add_error {s E C : ℝ} {z : ℂ}
    (he : ‖(s : ℂ) - z‖ ≤ E) (hz : ‖z‖ ≤ C) : s ≤ C + E := by
  have h₁ := (Complex.re_le_norm ((s : ℂ) - z)).trans he
  have h₂ := (Complex.re_le_norm z).trans hz
  simp only [Complex.sub_re, Complex.ofReal_re] at h₁
  linarith

theorem real_normalized_weight_le_of_error
    {scale series count s E C : ℝ} {T : ℂ}
    (hscale : 0 ≤ scale) (hseries : 0 < series) (hcount : 0 < count)
    (herror : ‖(s : ℂ) - (count : ℂ) * T‖ ≤ E)
    (hmain : ‖((scale / series : ℝ) : ℂ) * T‖ ≤ C) :
    scale / (series * count) * s ≤ C + scale / (series * count) * E := by
  have he := norm_real_normalized_complex_error_le hscale hseries hcount herror
  rw [← Complex.ofReal_mul] at he
  exact real_le_main_norm_add_error he hmain

theorem normalized_pinnedSourceRealIntegerWeight_forced_le
    {K w m p₀ Y p a A B : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    (P : Finset ℕ) (hP : ∀ r ∈ P, r.Prime) (hrough : ∀ r ∈ P, w < r)
    {LD C : ℝ} (hLD : 0 < LD) (hY : 1 < Y) (hKw : K ≤ w) (hm : 0 < m) (hp₀ : p₀.Prime)
    (hcop : (m * p₀ - 1).Coprime (primorial Y)) (hpP : p ∈ P) (ha : a.Coprime p)
    (hA : 0 < A) (hAB : A ≤ B)
    (hFsupport : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1) (hD : LD / 10 < Real.log p₀)
    (hSS : 0 < pinnedSingularSeries h w m p₀ Y)
    (hcount : 0 < (auxiliaryPrimeInterval A B).card)
    (hmain : ‖(((LD ^ (K - 1) * Real.log Y ^ (K - 1)) /
      pinnedSingularSeries h w m p₀ Y : ℝ) : ℂ) *
        pinnedSourceForcedGraphKernel S F G h P w m p₀ Y p a LD (Real.log Y)‖ ≤ C / p) :
    (LD ^ (K - 1) * Real.log Y ^ (K - 1)) /
        (pinnedSingularSeries h w m p₀ Y * (auxiliaryPrimeInterval A B).card) *
      (∑ q ∈ (auxiliaryPrimeInterval A B).filter (fun q ↦ q ≡ a [MOD p]),
        pinnedSourceRealIntegerWeight S F G h P w m p₀ q LD (Real.log Y)) ≤
      C / p + (LD ^ (K - 1) * Real.log Y ^ (K - 1)) /
        (pinnedSingularSeries h w m p₀ Y * (auxiliaryPrimeInterval A B).card) *
          pinnedSourceOneForcedProgressionErrorBound S F G h P p A B LD (Real.log Y) := by
  have herr := norm_sum_pinnedSourceIntegerWeight_forced_sub_graphKernel_le S F G h P hP
    hrough hLD hY hKw hm hp₀ hcop hpP ha hA hAB hFsupport hGsupport hD
  simp_rw [← ofReal_pinnedSourceRealIntegerWeight] at herr
  rw [← Complex.ofReal_sum] at herr
  exact real_normalized_weight_le_of_error
    (mul_nonneg (pow_nonneg hLD.le _)
      (pow_nonneg (Real.log_pos (by exact_mod_cast hY)).le _))
    hSS (by exact_mod_cast hcount) herr hmain

theorem weightedAffineCollisionSum_eq_forced_residue
    {K w m p A B : ℕ} (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p) (hpm : ¬p ∣ m)
    {ba : ↥(preSievedShifts K w) × ↥(preSievedShifts K w)} (hba : ba.1 ≠ ba.2)
    (W : ℕ → ℝ) :
    weightedAffineCollisionSum A B m p ba W =
      ∑ q ∈ (auxiliaryPrimeInterval A B).filter
        (fun q ↦ q ≡ crossAffinePrimeResidue m p ba
          (preSieved_crossAffineCoefficient_isUnit hp hKw hwp hpm hba) [MOD p]), W q := by
  unfold weightedAffineCollisionSum affineCollisionAuxiliaryPrimes
  congr 1
  ext q
  simp only [Finset.mem_filter,
    prime_dvd_preSieved_crossAffineDifference_iff_modEq hp hKw hwp hpm hba]

end

end Erdos4b
