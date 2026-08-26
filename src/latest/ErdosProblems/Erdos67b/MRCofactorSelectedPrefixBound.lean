import ErdosProblems.Erdos67b.MRCofactorSelectedPrefix
import ErdosProblems.Erdos67b.MRSelectedPrimeMass

/-! # Finite cofactor prefix bound from complementary cancellation and a selected tail -/

open scoped BigOperators

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrNorm_positivePrefix_le_of_unit_bound
    {a : ℕ → ℂ} (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1) (X : ℕ) :
    ‖positivePrefixSum a X‖ ≤ (X : ℝ) := by
  rw [mrPositivePrefixSum_eq_Icc]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 X, ‖a n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 X, (1 : ℝ) :=
      Finset.sum_le_sum (fun n hn ↦ ha n (Finset.mem_Icc.mp hn).1)
    _ = _ := by simp

theorem mrNorm_typicalCofactor_prefix_le_selected_mass {ι : Type*}
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    (hdisj : ∀ j ∈ J, Disjoint A (B j))
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) {X K : ℕ}
    (hsmall : ∀ d ∈ Finset.Icc 1 X, d ≤ K → PrimeSupported (fun p ↦ p ∈ A) d →
      ‖positivePrefixSum (mrIndexedTypicalCoefficient J B
        (gsDeletePrimeBand f (fun p ↦ p ∈ A))) (X / d)‖ ≤ epsilon * (X / d : ℕ)) :
    ‖positivePrefixSum (mrIndexedTypicalCofactorCoefficient A J B f) X‖ ≤
      (X : ℝ) * (epsilon * (∑ d ∈ Finset.Icc 1 X, mrSelectedPrimeWeight A 1 d) +
        ∑ d ∈ Finset.Icc 1 X, mrSelectedPrimeTailWeight A (K : ℝ) d) := by
  classical
  let c := mrIndexedTypicalCoefficient J B (gsDeletePrimeBand f (fun p ↦ p ∈ A))
  have hc : ∀ n, 0 < n → ‖c n‖ ≤ 1 := fun n hn ↦
    mrIndexedTypicalCoefficient_norm_le J B
      (fun m hm ↦ norm_gsDeletePrimeBand_le_one hbound (fun p ↦ p ∈ A) hm) hn
  have hpoint : ∀ d ∈ Finset.Icc 1 X,
      ‖mrSelectedCofactorFactor A f d * positivePrefixSum c (X / d)‖ ≤
        (X : ℝ) * (epsilon * mrSelectedPrimeWeight A 1 d +
          mrSelectedPrimeTailWeight A (K : ℝ) d) := by
    intro d hd
    have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
    have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
    have hquot : ((X / d : ℕ) : ℝ) ≤ (X : ℝ) / d := by
      apply (le_div_iff₀ hdR).2
      exact_mod_cast Nat.div_mul_le_self X d
    by_cases hsupp : PrimeSupported (fun p ↦ p ∈ A) d
    · have hw : mrSelectedPrimeWeight A 1 d = (d : ℝ)⁻¹ := by
        simp only [mrSelectedPrimeWeight, if_pos hsupp, Real.rpow_neg_one]
      rw [norm_mul]
      have hnorm := mul_le_of_le_one_left (norm_nonneg (positivePrefixSum c (X / d)))
        (norm_mrSelectedCofactorFactor_le_one A hbound d)
      by_cases hdK : d ≤ K
      · have hnot : ¬ (K : ℝ) < d := by exact_mod_cast not_lt.mpr hdK
        rw [mrSelectedPrimeTailWeight, if_neg hnot, hw, add_zero]
        calc
          _ ≤ ‖positivePrefixSum c (X / d)‖ := hnorm
          _ ≤ epsilon * (X / d : ℕ) := hsmall d hd hdK hsupp
          _ ≤ epsilon * ((X : ℝ) / d) := mul_le_mul_of_nonneg_left hquot hepsilon
          _ = _ := by ring
      · have hlt : (K : ℝ) < d := by exact_mod_cast Nat.lt_of_not_ge hdK
        rw [mrSelectedPrimeTailWeight, if_pos hlt, hw]
        calc
          _ ≤ ‖positivePrefixSum c (X / d)‖ := hnorm
          _ ≤ (X / d : ℕ) := mrNorm_positivePrefix_le_of_unit_bound hc _
          _ ≤ (X : ℝ) / d := hquot
          _ ≤ _ := by
            have hx : (0 : ℝ) ≤ X := Nat.cast_nonneg X
            have he : 0 ≤ (X : ℝ) * (epsilon * (d : ℝ)⁻¹) := by positivity
            rw [div_eq_mul_inv]
            nlinarith
    · rw [mrSelectedCofactorFactor_eq_zero_of_not_supported A f hsupp, zero_mul, norm_zero]
      have hw := mrSelectedPrimeWeight_nonneg A 1 d
      have ht : 0 ≤ mrSelectedPrimeTailWeight A (K : ℝ) d := by
        unfold mrSelectedPrimeTailWeight
        split_ifs <;> positivity
      positivity
  rw [mrTypicalCofactor_selected_prefix A hA J B hB hdisj hmul]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 X,
        ‖mrSelectedCofactorFactor A f d * positivePrefixSum c (X / d)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 X,
        (X : ℝ) * (epsilon * mrSelectedPrimeWeight A 1 d +
          mrSelectedPrimeTailWeight A (K : ℝ) d) := Finset.sum_le_sum hpoint
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem mrNorm_typicalCofactor_prefix_div_le_euler_rankin {ι : Type*}
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    (hdisj : ∀ j ∈ J, Disjoint A (B j))
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {epsilon sigma : ℝ} (hepsilon : 0 ≤ epsilon) (hsigma : 0 < sigma)
    (hsigmaOne : sigma ≤ 1) {X K : ℕ} (hX : 0 < X) (hK : 0 < K)
    (hsmall : ∀ d ∈ Finset.Icc 1 X, d ≤ K → PrimeSupported (fun p ↦ p ∈ A) d →
      ‖positivePrefixSum (mrIndexedTypicalCoefficient J B
        (gsDeletePrimeBand f (fun p ↦ p ∈ A))) (X / d)‖ ≤ epsilon * (X / d : ℕ)) :
    ‖positivePrefixSum (mrIndexedTypicalCofactorCoefficient A J B f) X‖ / (X : ℝ) ≤
      epsilon * (∏ p ∈ A, (1 - (p : ℝ)⁻¹)⁻¹) +
        (K : ℝ) ^ (sigma - 1) * ∏ p ∈ A, (1 - (p : ℝ) ^ (-sigma))⁻¹ := by
  have hprefix := mrNorm_typicalCofactor_prefix_le_selected_mass
    A hA J B hB hdisj hmul hbound hepsilon hsmall
  have hhead := mrSum_selectedPrimeWeight_le_euler A hA
    (by norm_num : (0 : ℝ) < 1) (Finset.Icc 1 X)
  simp only [Real.rpow_neg_one] at hhead
  have htail := mrSum_selectedPrimeTailWeight_le_rankin A hA
    (by exact_mod_cast hK : (0 : ℝ) < K) hsigma hsigmaOne (Finset.Icc 1 X)
  apply (div_le_iff₀ (by exact_mod_cast hX : (0 : ℝ) < X)).2
  calc
    _ ≤ _ := hprefix
    _ ≤ _ := by
      rw [mul_comm _ (X : ℝ)]
      exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hhead hepsilon) htail) (Nat.cast_nonneg X)

end

end Erdos67b
