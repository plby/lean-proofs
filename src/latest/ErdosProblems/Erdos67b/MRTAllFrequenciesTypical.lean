import ErdosProblems.Erdos67b.MRTMinorArcTypical
import ErdosProblems.Erdos67b.MRTMajorArcTypical

/-! # One fixed typical family controls all additive frequencies -/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos67b

noncomputable section

theorem mrtScheduled_firstInterval (p q : ℝ) :
    mrScheduledPrimeInterval p q 1 = mrLogPrimeInterval p q := by
  simp [mrScheduledPrimeInterval, mrLogScheduleLower, mrLogScheduleWeight, mrLogScheduleUpper]

theorem mrtScheduled_first_mem (p q : ℝ) {K : ℕ} (hK : 0 < K) :
    mrLogPrimeInterval p q ∈ mrScheduledBlocks p q K := by
  rw [← mrtScheduled_firstInterval]
  exact Finset.mem_image.2 ⟨1, Finset.mem_Icc.2 ⟨le_refl _, hK⟩, rfl⟩

theorem mrtExists_logPower_allFrequency_typical_firstMoment {ε rho R : ℝ}
    (hε : 0 < ε) (hrho : 0 < rho) (hR : 1 ≤ R) :
    ∃ H₀ : ℕ, 10 ≤ H₀ ∧ ∀ H : ℕ, H₀ ≤ H →
      2 ≤ mrtLogPowerWindow (Real.log (H : ℝ)) ∧
      mrtLogPowerLower (Real.log (H : ℝ)) / mrtLogPowerUpper (Real.log (H : ℝ)) ≤ rho ∧
      ∃ K A₀ Y₀ : ℕ, 0 < K ∧ 0 < A₀ ∧ H ≤ Y₀ ∧
        ∀ {A X Y : ℕ}, A₀ ≤ A → Y₀ ≤ Y → Y ≤ X →
          Real.log (X : ℝ) ≤ R * Real.log
            ((Y / mrtLogPowerNatWindow (Real.log (H : ℝ)) : ℕ) : ℝ) →
        ∀ {f : ℕ → ℂ}, IsCompletelyMultiplicativeOnPositive f →
          (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRTNonpretentious f A X →
        ∀ α : ℝ, ∀ {Z : ℕ}, 2 * Y ≤ Z →
          (∑ n ∈ Finset.Ioc Y (2 * Y),
            ‖typicalModulatedShortSum
              (mrScheduledBlocks (mrtLogPowerLower (Real.log (H : ℝ)))
                (mrtLogPowerUpper (Real.log (H : ℝ))) K) Z f n H α‖) ≤
              ε * H * Y := by
  obtain ⟨H₁, hH₁, hmajor⟩ := mrtExists_logPower_majorArc_typical_firstMoment hε hrho hR
  obtain ⟨H₂, _, hminor⟩ := mrtExists_logPower_minorArc_typical_firstMoment hε
  obtain ⟨H₃, hsource⟩ := eventually_atTop.1
    (EulerSubpower.tendsto_log_nat_atTop.eventually (mrtEventually_logPower_source hrho))
  refine ⟨max H₁ (max H₂ H₃), hH₁.trans (le_max_left _ _), ?_⟩
  intro H hH
  have hH1 : H₁ ≤ H := (le_max_left _ _).trans hH
  have hH2 : H₂ ≤ H := (le_max_left H₂ H₃).trans ((le_max_right _ _).trans hH)
  have hH3 : H₃ ≤ H := (le_max_right H₂ H₃).trans ((le_max_right _ _).trans hH)
  have hHpos : 0 < H := by omega
  obtain ⟨hW, hratio, K, A₀, Y₀, hK, hA₀, hY₀, hmajorH⟩ := hmajor H hH1
  have hminorH := (hminor H hH2).2
  obtain ⟨_, _, hp, hq, hpq, hlogq, hbudget, _, _, _, _⟩ := hsource H hH3
  let p := mrtLogPowerLower (Real.log (H : ℝ))
  let u := mrtLogPowerUpper (Real.log (H : ℝ))
  let w := mrtLogPowerNatWindow (Real.log (H : ℝ))
  let I := mrLogPrimeInterval p u
  have hw : 2 ≤ w := (mrtLogPowerNatWindow_bounds hW).1
  have hI : I ∈ mrScheduledBlocks p u K := mrtScheduled_first_mem p u hK
  have hu : 1 ≤ u := (Real.one_le_exp_iff.2 (by norm_num : (0 : ℝ) ≤ 1)).trans hq
  have hpu : p ≤ u := by dsimp only [p, u]; linarith only [hp, hpq]
  have hdisj : ∀ J ∈ mrScheduledBlocks p u K, J ≠ I →
      Disjoint (primesInBlock I) (primesInBlock J) := by
    simpa only [mrtScheduled_firstInterval] using
      (mrScheduledBlocks_other_disjoint (by norm_num : (1 / 12 : ℝ) ≤ 1 / 12)
        hp hu hpu hlogq hbudget K (by norm_num : 1 ≤ (1 : ℕ)))
  refine ⟨hW, hratio, K, A₀, Y₀, hK, hA₀, hY₀, ?_⟩
  intro A X Y hA hY hYX hlog f hmul hbound hnonpret α Z hZ
  obtain ⟨a, q, hqpos, hqbound, hcop, happrox⟩ :=
    exists_reducedRationalApproximation_shortInterval α hHpos (by omega : 0 < w)
  by_cases hqw : q ≤ w
  · apply hmajorH hA hY hYX hlog hmul hbound hnonpret hqpos hqw a α _ hZ
    exact happrox.trans (div_le_div_of_nonneg_right
      (mrtLogPowerNatWindow_bounds hW).2.2 (by positivity))
  · exact hminorH (mrScheduledBlocks p u K) I Z Y f (mrtLogPower_prime_lower_le hW)
      (mrtLogPower_prime_upper_le hHpos hW) hI hdisj (hY₀.trans hY)
      hmul.isMultiplicativeOnPositiveNat hbound q a α (by omega) hqbound hcop happrox

end

end Erdos67b
