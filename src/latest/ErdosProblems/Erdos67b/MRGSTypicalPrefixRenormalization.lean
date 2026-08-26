import ErdosProblems.Erdos67b.MRPrimeMaskInclusion
import ErdosProblems.Erdos67b.MRGSTwoBlockA8Scalar
import ErdosProblems.Erdos67b.MRGSArchimedeanFactorDecay

/-!
# GS prefix renormalization for any finite typical block family

The exact finite mask identity is applied before the GS estimate.
Each mask remains multiplicative; the typical coefficient need not be.
The sum of the individual quantitative errors is kept explicit.
-/

open scoped BigOperators

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrGS_twistedPrefix_indexedTypical_eq_mask_sum
    {ι : Type*} (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime) (f : ℕ → ℂ) (t : ℝ) (N : ℕ) :
    gsTwistedPositivePrefixSum (mrIndexedTypicalCoefficient J B f) t N =
      ∑ S ∈ J.powerset, (-1 : ℂ) ^ S.card *
        gsTwistedPositivePrefixSum (gsDeletePrimeBand f (fun p ↦ p ∈ S.biUnion B)) t N := by
  classical
  unfold gsTwistedPositivePrefixSum
  calc
    _ = ∑ n ∈ Finset.Ioc 0 N,
        (∑ S ∈ J.powerset, (-1 : ℂ) ^ S.card *
          gsDeletePrimeBand f (fun p ↦ p ∈ S.biUnion B) n) * LogPhaseSum.natLogTwist n t := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [mrIndexedTypicalCoefficient_eq_mask_sum J B hB f (Finset.mem_Ioc.mp hn).1]
      rfl
    _ = _ := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S hS
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring

theorem mrGS_norm_deleted_centered_prefix_error_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, ‖f n‖ ≤ 1) (Q : ℕ → Prop) [DecidablePred Q]
    (t₁ u : ℝ) {N : ℕ} (hN : 2 ≤ N) (hu : u ≠ 0) :
    ‖gsTwistedPositivePrefixSum (gsDeletePrimeBand f Q) (t₁ + u) N / (N : ℂ) -
        gsPrefixArchimedeanFactor u N *
          (gsTwistedPositivePrefixSum (gsDeletePrimeBand f Q) t₁ N / (N : ℂ))‖ ≤
      gsPrefixRenormalizationLinearError (gsDeletePrimeBand (archimedeanUntwist f t₁) Q) u N := by
  have hdeleted : ∀ n, ‖gsDeletePrimeBand f Q n‖ ≤ 1 := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [gsDeletePrimeBand, primeBandCoefficient, PrimeSupported]
    · exact norm_gsDeletePrimeBand_le_one (fun m _ ↦ hbound m) Q (Nat.pos_of_ne_zero hn)
  have h := norm_normalized_gsTwistedPrefix_sub_archimedeanFactor_mul_prefixMean_le_exp_linear
    (archimedeanUntwist_isMultiplicative
      (gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul Q) t₁)
    (norm_archimedeanUntwist_le_one hdeleted t₁) u hN hu
  rw [gsTwistedPositivePrefixSum_archimedeanUntwist_add,
    ← gsTwistedPositivePrefixSum_div_eq_positivePrefixMean_archimedeanUntwist
      (gsDeletePrimeBand f Q) t₁ (by omega : 0 < N)] at h
  simpa only [gsPrefixRenormalizationLinearError, gsDeletePrimeBand_archimedeanUntwist] using h

theorem mrGS_norm_indexedTypical_centered_prefix_error_le_sum
    {ι : Type*} (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f) (hbound : ∀ n, ‖f n‖ ≤ 1)
    (t₁ u : ℝ) {N : ℕ} (hN : 2 ≤ N) (hu : u ≠ 0) :
    ‖gsTwistedPositivePrefixSum (mrIndexedTypicalCoefficient J B f) (t₁ + u) N / (N : ℂ) -
        gsPrefixArchimedeanFactor u N *
          (gsTwistedPositivePrefixSum (mrIndexedTypicalCoefficient J B f) t₁ N / (N : ℂ))‖ ≤
      ∑ S ∈ J.powerset, gsPrefixRenormalizationLinearError
        (gsDeletePrimeBand (archimedeanUntwist f t₁) (fun p ↦ p ∈ S.biUnion B)) u N := by
  classical
  rw [mrGS_twistedPrefix_indexedTypical_eq_mask_sum J B hB f (t₁ + u) N,
    mrGS_twistedPrefix_indexedTypical_eq_mask_sum J B hB f t₁ N]
  simp only [Finset.sum_div, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  have halgebra :
      (∑ S ∈ J.powerset,
        ((-1 : ℂ) ^ S.card * gsTwistedPositivePrefixSum
            (gsDeletePrimeBand f (fun p ↦ p ∈ S.biUnion B)) (t₁ + u) N / (N : ℂ) -
          gsPrefixArchimedeanFactor u N *
            ((-1 : ℂ) ^ S.card * gsTwistedPositivePrefixSum
              (gsDeletePrimeBand f (fun p ↦ p ∈ S.biUnion B)) t₁ N / (N : ℂ)))) =
      ∑ S ∈ J.powerset, (-1 : ℂ) ^ S.card *
        (gsTwistedPositivePrefixSum (gsDeletePrimeBand f (fun p ↦ p ∈ S.biUnion B))
            (t₁ + u) N / (N : ℂ) - gsPrefixArchimedeanFactor u N *
          (gsTwistedPositivePrefixSum (gsDeletePrimeBand f (fun p ↦ p ∈ S.biUnion B))
            t₁ N / (N : ℂ))) := by
    apply Finset.sum_congr rfl
    intro S hS
    ring
  rw [halgebra]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro S hS
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact mrGS_norm_deleted_centered_prefix_error_le hmul hbound
    (fun p ↦ p ∈ S.biUnion B) t₁ u hN hu

end

end Erdos67b
