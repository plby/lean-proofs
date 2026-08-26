import ErdosProblems.Erdos67b.MRCofactorTwistDistance
import ErdosProblems.Erdos67b.MRCofactorPowerCutoff
import ErdosProblems.Erdos67b.MRTypicalLowHigh
import ErdosProblems.Erdos67b.MRGSPrefixToDyadic
import ErdosProblems.Erdos67b.MRRealPretentiousSymmetry

/-! # The actual twisted cofactor prefix and monotone cutoff -/

open scoped BigOperators ComplexConjugate

namespace Erdos67b

noncomputable section

theorem mrIndexedTypicalCofactor_untwist_apply {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ) (f : ℕ → ℂ) (t : ℝ)
    {n : ℕ} (hn : 0 < n) :
    mrIndexedTypicalCofactorCoefficient A J B (archimedeanUntwist f t) n =
      mrIndexedTypicalCofactorCoefficient A J B f n * conj (archimedeanTwist t n) := by
  unfold mrIndexedTypicalCofactorCoefficient mrIndexedTypicalCoefficient archimedeanUntwist
  rw [if_neg hn.ne']
  split_ifs <;> ring

theorem mrPositivePrefix_typicalCofactor_untwist_eq {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ) (f : ℕ → ℂ) (t : ℝ) (N : ℕ) :
    positivePrefixSum (mrIndexedTypicalCofactorCoefficient A J B (archimedeanUntwist f t)) N =
      gsTwistedPositivePrefixSum (mrIndexedTypicalCofactorCoefficient A J B f) t N := by
  have hsum := sum_Ioc_eq_positivePrefixSum_sub
    (mrIndexedTypicalCofactorCoefficient A J B (archimedeanUntwist f t)) (Nat.zero_le N)
  have hzero : positivePrefixSum (mrIndexedTypicalCofactorCoefficient A J B
      (archimedeanUntwist f t)) 0 = 0 := by simp [positivePrefixSum]
  rw [hzero, sub_zero] at hsum
  rw [← hsum, gsTwistedPositivePrefixSum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [mrIndexedTypicalCofactor_untwist_apply A J B f t (Finset.mem_Ioc.1 hn).1,
    LogPhaseSum.natLogTwist_eq_archimedeanTwist_neg, archimedeanTwist_neg]

theorem mrCofactorPowerCutoff_mono {delta : ℝ} (hdelta : 0 ≤ delta)
    {Y Z : ℕ} (hY : 0 < Y) (hYZ : Y ≤ Z) :
    mrCofactorPowerCutoff delta Y ≤ mrCofactorPowerCutoff delta Z := by
  apply Nat.ceil_mono
  apply Real.exp_le_exp.2
  exact mul_le_mul_of_nonneg_left
    (Real.log_le_log (by exact_mod_cast hY) (by exact_mod_cast hYZ)) hdelta

theorem mrNorm_cofactor_dyadicPolynomial_le_of_untwisted_prefixes {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ) (f : ℕ → ℂ)
    {Y : ℕ} (hY : 0 < Y) (t : ℝ) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hprefix : ∀ Z ∈ Finset.Icc Y (2 * Y),
      ‖positivePrefixSum (mrIndexedTypicalCofactorCoefficient A J B (archimedeanUntwist f t)) Z‖ /
        (Z : ℝ) ≤ epsilon) :
    ‖dyadicVerticalDirichletPolynomial (Finset.Ioc Y (2 * Y))
      (mrIndexedTypicalCofactorCoefficient A J B f) Y t‖ ≤ 3 * epsilon := by
  apply norm_dyadicVerticalDirichletPolynomial_le_of_normalized_gsPrefixes
    (mrIndexedTypicalCofactorCoefficient A J B f) hY t hepsilon
  intro Z hZ
  rw [norm_div, Complex.norm_natCast, ← mrPositivePrefix_typicalCofactor_untwist_eq]
  exact hprefix Z hZ

end

end Erdos67b
