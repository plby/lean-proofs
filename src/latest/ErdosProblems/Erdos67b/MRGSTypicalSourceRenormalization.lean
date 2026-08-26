import ErdosProblems.Erdos67b.MRGSTypicalSourceMass
import ErdosProblems.Erdos67b.MRGSTypicalPrefixRenormalization
import ErdosProblems.Erdos67b.MRGSTypicalMaskCount
import ErdosProblems.Erdos67b.MRCofactorScheduledBlocks

/-!
# Full scheduled-family GS renormalization on the central window

The source logarithmic prime bounds pay all mask masses with their fixed
Mertens allowances. The number of masks is absorbed uniformly before the
source parameters, coefficient, center frequency, and displacement.
-/

open scoped BigOperators
open Filter

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrGS_counted_centralError_le {C u : ℝ} (hC : 0 ≤ C) {K N : ℕ}
    (hlog : 1 ≤ Real.log (N : ℝ))
    (hwindow : |u| ≤ (Real.log (N : ℝ)) ^ (1 / 16 : ℝ))
    (hcount : (2 : ℝ) ^ K ≤ (Real.log (N : ℝ)) ^ (1 / 80 : ℝ)) :
    (2 : ℝ) ^ K * C * (1 + |u|) * (Real.log (N : ℝ)) ^ (-1 / 8 : ℝ) ≤
      2 * C * (Real.log (N : ℝ)) ^ (-1 / 20 : ℝ) := by
  have hL : 0 < Real.log (N : ℝ) := by linarith
  have hpowers : (Real.log (N : ℝ)) ^ (1 / 80 : ℝ) *
      (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ) = (Real.log (N : ℝ)) ^ (-1 / 20 : ℝ) := by
    rw [← Real.rpow_add hL]
    norm_num
  calc
    _ = (2 : ℝ) ^ K * C * ((1 + |u|) * (Real.log (N : ℝ)) ^ (-1 / 8 : ℝ)) := by ring
    _ ≤ (2 : ℝ) ^ K * C * (2 * (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ)) :=
      mul_le_mul_of_nonneg_left (one_add_abs_mul_log_rpow_neg_eighth_le hlog hwindow)
        (mul_nonneg (by positivity) hC)
    _ ≤ (Real.log (N : ℝ)) ^ (1 / 80 : ℝ) * C *
        (2 * (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcount hC) (by positivity)
    _ = 2 * C * ((Real.log (N : ℝ)) ^ (1 / 80 : ℝ) *
        (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ)) := by ring
    _ = _ := by rw [hpowers]

theorem mrGS_norm_indexedTypical_central_error_le_source_of_distanceAllowance
    {ι : Type*} (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f) (hbound : ∀ n, ‖f n‖ ≤ 1)
    (t₁ u : ℝ) {L : ℝ} (hL : 0 ≤ L) {N : ℕ} (hN : 2 ≤ N) (hlog : 1 ≤ Real.log (N : ℝ))
    (hwindow : |u| ≤ (Real.log (N : ℝ)) ^ (1 / 16 : ℝ))
    (hcount : (2 : ℝ) ^ J.card ≤ (Real.log (N : ℝ)) ^ (1 / 80 : ℝ))
    (hsmall : ∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.sqrt (Real.log (N : ℝ)))
    (hdist : pretentiousDistSq f (archimedeanTwist t₁) N ≤
      Real.log (Real.log (N : ℝ)) / 8 + L) :
    ‖gsTwistedPositivePrefixSum (mrIndexedTypicalCoefficient J B f) (t₁ + u) N / (N : ℂ) -
        gsPrefixArchimedeanFactor u N *
          (gsTwistedPositivePrefixSum (mrIndexedTypicalCoefficient J B f) t₁ N / (N : ℂ))‖ ≤
      2 * (mrGSTypicalSourceErrorConstant * Real.exp (7 * L)) * (Real.log (N : ℝ)) ^ (-1 / 20 : ℝ) := by
  classical
  have hC : 0 ≤ mrGSTypicalSourceErrorConstant * Real.exp (7 * L) :=
    mul_nonneg mrGSTypicalSourceErrorConstant_nonneg (Real.exp_pos _).le
  by_cases hu : u = 0
  · subst u
    have hfactor : gsPrefixArchimedeanFactor 0 N = 1 := by
      simp [gsPrefixArchimedeanFactor, LogPhaseSum.natLogTwist, LogPhaseSum.logPhase]
    simp only [add_zero, hfactor, one_mul, sub_self, norm_zero]
    positivity
  apply (mrGS_norm_indexedTypical_centered_prefix_error_le_sum J B hB hmul hbound
    t₁ u hN hu).trans
  calc
    _ ≤ ∑ _S ∈ J.powerset,
        (mrGSTypicalSourceErrorConstant * Real.exp (7 * L)) * (1 + |u|) *
          (Real.log (N : ℝ)) ^ (-1 / 8 : ℝ) := by
      apply Finset.sum_le_sum
      intro S hS
      apply mrGS_sourceMasked_linearError_le_log_rpow_of_distanceAllowance hbound
        (fun p ↦ p ∈ S.biUnion B) t₁ u hL hN hlog ?_ hdist
      intro p hp hpS
      obtain ⟨j, hj, hpB⟩ := Finset.mem_biUnion.mp hpS
      exact hsmall j (Finset.mem_powerset.mp hS hj) p hpB
    _ = (2 : ℝ) ^ J.card * (mrGSTypicalSourceErrorConstant * Real.exp (7 * L)) * (1 + |u|) *
        (Real.log (N : ℝ)) ^ (-1 / 8 : ℝ) := by simp [Finset.card_powerset, mul_assoc]
    _ ≤ _ := mrGS_counted_centralError_le hC hlog hwindow hcount

theorem mrGS_norm_indexedTypical_central_error_le_source
    {ι : Type*} (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f) (hbound : ∀ n, ‖f n‖ ≤ 1)
    (t₁ u : ℝ) {N : ℕ} (hN : 2 ≤ N) (hlog : 1 ≤ Real.log (N : ℝ))
    (hwindow : |u| ≤ (Real.log (N : ℝ)) ^ (1 / 16 : ℝ))
    (hcount : (2 : ℝ) ^ J.card ≤ (Real.log (N : ℝ)) ^ (1 / 80 : ℝ))
    (hsmall : ∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.sqrt (Real.log (N : ℝ)))
    (hdist : pretentiousDistSq f (archimedeanTwist t₁) N ≤
      Real.log (Real.log (N : ℝ)) / 8) :
    ‖gsTwistedPositivePrefixSum (mrIndexedTypicalCoefficient J B f) (t₁ + u) N / (N : ℂ) -
        gsPrefixArchimedeanFactor u N *
          (gsTwistedPositivePrefixSum (mrIndexedTypicalCoefficient J B f) t₁ N / (N : ℂ))‖ ≤
      2 * mrGSTypicalSourceErrorConstant * (Real.log (N : ℝ)) ^ (-1 / 20 : ℝ) := by
  simpa only [mul_zero, Real.exp_zero, mul_one, add_zero] using
    mrGS_norm_indexedTypical_central_error_le_source_of_distanceAllowance
      J B hB hmul hbound t₁ u (L := 0) le_rfl hN hlog hwindow hcount hsmall
      (by simpa only [add_zero] using hdist)

theorem mrGS_exists_scheduled_central_renormalization :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ {eta p₁ q₁ : ℝ}, eta ≤ 1 / 12 → 2 ≤ p₁ → 1 ≤ q₁ →
        p₁ ≤ q₁ → 1 ≤ Real.log q₁ → 4096 * Real.log q₁ ≤ eta * p₁ →
      ∀ J : ℕ, mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (N : ℝ)) →
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f → (∀ n, ‖f n‖ ≤ 1) →
      ∀ t₁ : ℝ, pretentiousDistSq f (archimedeanTwist t₁) N ≤
        Real.log (Real.log (N : ℝ)) / 8 →
      ∀ u : ℝ, |u| ≤ (Real.log (N : ℝ)) ^ (1 / 16 : ℝ) →
        let a := mrIndexedTypicalCoefficient (Finset.Icc 1 J)
          (fun j ↦ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)) f
        ‖gsTwistedPositivePrefixSum a (t₁ + u) N / (N : ℂ) -
            gsPrefixArchimedeanFactor u N * (gsTwistedPositivePrefixSum a t₁ N / (N : ℂ))‖ ≤
          2 * mrGSTypicalSourceErrorConstant * (Real.log (N : ℝ)) ^ (-1 / 20 : ℝ) := by
  obtain ⟨N₁, _, hcount⟩ := mrExists_eventually_source_maskCount_le_log_rpow
    (by norm_num : (0 : ℝ) < 1 / 80)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1
    (EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max 2 (max N₁ N₂), le_max_left _ _, ?_⟩
  intro N hN eta p₁ q₁ heta hp hq hpq hlogq hbudget J hupper f hmul hbound t₁ hdist u hu
  have hN₁ : N₁ ≤ N := (le_max_left N₁ N₂).trans ((le_max_right _ _).trans hN)
  have hN₂' : N₂ ≤ N := (le_max_right N₁ N₂).trans ((le_max_right _ _).trans hN)
  apply mrGS_norm_indexedTypical_central_error_le_source (Finset.Icc 1 J)
    (fun j ↦ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j))
    (fun j hj p hpB ↦ (mem_primesInBlock.mp hpB).1) hmul hbound t₁ u
    ((le_max_left _ _).trans hN) (hN₂ N hN₂') hu
  · simpa only [Nat.card_Icc, Nat.add_sub_cancel_right] using hcount N hN₁ hq J hupper
  · intro j hj p hpB
    exact mrScheduledPrime_log_le_sqrt heta hp hq hpq hlogq hbudget hupper hj hpB
  · exact hdist

theorem mrGS_exists_scheduled_central_prefix_profile :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ {eta p₁ q₁ : ℝ}, eta ≤ 1 / 12 → 2 ≤ p₁ → 1 ≤ q₁ →
        p₁ ≤ q₁ → 1 ≤ Real.log q₁ → 4096 * Real.log q₁ ≤ eta * p₁ →
      ∀ J : ℕ, mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (N : ℝ)) →
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f → (∀ n, ‖f n‖ ≤ 1) →
      ∀ t₁ : ℝ, pretentiousDistSq f (archimedeanTwist t₁) N ≤
        Real.log (Real.log (N : ℝ)) / 8 →
      ∀ u : ℝ, |u| ≤ (Real.log (N : ℝ)) ^ (1 / 16 : ℝ) →
        let a := mrIndexedTypicalCoefficient (Finset.Icc 1 J)
          (fun j ↦ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)) f
        ‖gsTwistedPositivePrefixSum a (t₁ + u) N / (N : ℂ)‖ ≤
          2 * ‖gsTwistedPositivePrefixSum a t₁ N / (N : ℂ)‖ * (1 + |u|)⁻¹ +
            2 * mrGSTypicalSourceErrorConstant * (Real.log (N : ℝ)) ^ (-1 / 20 : ℝ) := by
  obtain ⟨N₀, hN₀, hrenorm⟩ := mrGS_exists_scheduled_central_renormalization
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN eta p₁ q₁ heta hp hq hpq hlogq hbudget J hupper f hmul hbound t₁ hdist u hu
  have hr := hrenorm N hN heta hp hq hpq hlogq hbudget J hupper hmul hbound t₁ hdist u hu
  have hNpos : 0 < N := lt_of_lt_of_le (by omega : 0 < N₀) hN
  have hC := mrGSTypicalSourceErrorConstant_nonneg
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hNpos)
  have herror : 0 ≤ 2 * mrGSTypicalSourceErrorConstant *
      (Real.log (N : ℝ)) ^ (-1 / 20 : ℝ) := by positivity
  exact norm_le_two_mul_inv_one_add_abs_mul_add_of_renormalized
    herror (norm_nonneg _) (norm_gsPrefixArchimedeanFactor_le_two_div_one_add_abs u hNpos) le_rfl hr

end

end Erdos67b
