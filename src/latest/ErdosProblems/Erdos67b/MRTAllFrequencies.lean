import ErdosProblems.Erdos67b.MRTAllFrequenciesTypical
import ErdosProblems.Erdos67b.MRScheduledDensitySmall

/-! # Removing atypical integers from the all-frequency dyadic first moment -/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos67b

noncomputable section

theorem mrtSum_Ioc_modulated_le_typical_add_density
    (blocks : Finset (ℕ × ℕ)) (H Y : ℕ) (hHY : H ≤ Y) (f : ℕ → ℂ) (α : ℝ)
    (hf : ∀ r, 0 < r → ‖f r‖ ≤ 1) :
    (∑ n ∈ Finset.Ioc Y (2 * Y), ‖modulatedShortSum f n H α‖) ≤
      (∑ n ∈ Finset.Ioc Y (2 * Y), ‖typicalModulatedShortSum blocks (3 * Y) f n H α‖) +
        H * (atypicalFactorizationSet blocks (3 * Y)).card := by
  have herror : (∑ n ∈ Finset.Ioc Y (2 * Y),
      ‖modulatedShortSum f n H α - typicalModulatedShortSum blocks (3 * Y) f n H α‖) ≤
      H * (atypicalFactorizationSet blocks (3 * Y)).card := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg Finset.Ioc_subset_Icc_self
      (fun _ _ _ ↦ norm_nonneg _)).trans
    apply sum_norm_modulatedShortSum_sub_typical_le _ hf
    intro n hn j hj
    obtain ⟨_, hnhi⟩ := Finset.mem_Icc.1 hn
    obtain ⟨_, hjhi⟩ := Finset.mem_Icc.1 hj
    omega
  calc
    _ ≤ ∑ n ∈ Finset.Ioc Y (2 * Y),
        (‖typicalModulatedShortSum blocks (3 * Y) f n H α‖ +
          ‖modulatedShortSum f n H α - typicalModulatedShortSum blocks (3 * Y) f n H α‖) := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        _ ≤ ‖typicalModulatedShortSum blocks (3 * Y) f n H α‖ +
            ‖typicalModulatedShortSum blocks (3 * Y) f n H α - modulatedShortSum f n H α‖ :=
          norm_le_norm_add_norm_sub _ _
        _ = _ := by rw [norm_sub_rev]
    _ = (∑ n ∈ Finset.Ioc Y (2 * Y), ‖typicalModulatedShortSum blocks (3 * Y) f n H α‖) +
        ∑ n ∈ Finset.Ioc Y (2 * Y),
          ‖modulatedShortSum f n H α - typicalModulatedShortSum blocks (3 * Y) f n H α‖ :=
      Finset.sum_add_distrib
    _ ≤ _ := add_le_add (le_refl _) herror

theorem mrtExists_logPower_allFrequency_firstMoment {ε R : ℝ} (hε : 0 < ε) (hR : 1 ≤ R) :
    ∃ H₀ : ℕ, 10 ≤ H₀ ∧ ∀ H : ℕ, H₀ ≤ H →
      ∃ A₀ Y₀ : ℕ, 0 < A₀ ∧ H ≤ Y₀ ∧
        ∀ {A X Y : ℕ}, A₀ ≤ A → Y₀ ≤ Y → Y ≤ X →
          Real.log (X : ℝ) ≤ R * Real.log
            ((Y / mrtLogPowerNatWindow (Real.log (H : ℝ)) : ℕ) : ℝ) →
        ∀ {f : ℕ → ℂ}, IsCompletelyMultiplicativeOnPositive f →
          (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRTNonpretentious f A X →
        ∀ α : ℝ,
          (∑ n ∈ Finset.Ioc Y (2 * Y), ‖modulatedShortSum f n H α‖) ≤ ε * H * Y := by
  obtain ⟨rho, hrho, Y₁, _, hdensity⟩ := mrExists_scheduled_atypical_density_small (half_pos hε)
  obtain ⟨H₁, hH₁, htypical⟩ :=
    mrtExists_logPower_allFrequency_typical_firstMoment (half_pos hε) hrho hR
  obtain ⟨H₂, hsource⟩ := eventually_atTop.1
    (EulerSubpower.tendsto_log_nat_atTop.eventually (mrtEventually_logPower_source hrho))
  refine ⟨max H₁ H₂, hH₁.trans (le_max_left _ _), ?_⟩
  intro H hH
  have hH1 : H₁ ≤ H := (le_max_left _ _).trans hH
  have hH2 : H₂ ≤ H := (le_max_right _ _).trans hH
  obtain ⟨hW, hratio, K, A₀, Y₂, hK, hA₀, hY₂, htyp⟩ := htypical H hH1
  obtain ⟨_, _, hp, hq, hpq, hlogq, hbudget, _, _, _, _⟩ := hsource H hH2
  let p := mrtLogPowerLower (Real.log (H : ℝ))
  let u := mrtLogPowerUpper (Real.log (H : ℝ))
  have hu : 1 ≤ u := (Real.one_le_exp_iff.2 (by norm_num : (0 : ℝ) ≤ 1)).trans hq
  obtain ⟨Y₃, hY₃⟩ := eventually_atTop.1
    ((Real.tendsto_sqrt_atTop.comp EulerSubpower.tendsto_log_nat_atTop).eventually
      (eventually_ge_atTop (mrLogScheduleUpper u K)))
  refine ⟨A₀, max Y₁ (max Y₂ Y₃), hA₀,
    hY₂.trans ((le_max_left Y₂ Y₃).trans (le_max_right _ _)), ?_⟩
  intro A X Y hA hY hYX hlog f hmul hbound hnonpret α
  have hY1 : Y₁ ≤ Y := (le_max_left _ _).trans hY
  have hY2 : Y₂ ≤ Y := (le_max_left Y₂ Y₃).trans ((le_max_right _ _).trans hY)
  have hY3 : Y₃ ≤ Y := (le_max_right Y₂ Y₃).trans ((le_max_right _ _).trans hY)
  have hHY : H ≤ Y := hY₂.trans hY2
  have hden := hdensity Y hY1 (by norm_num : (1 / 12 : ℝ) ≤ 1 / 12)
    hp hu hpq hlogq hbudget hratio hK (hY₃ Y hY3) (3 * Y) (le_refl _)
  have htypY := htyp hA hY2 hYX hlog hmul hbound hnonpret α
    (show 2 * Y ≤ 3 * Y by omega)
  calc
    _ ≤ (∑ n ∈ Finset.Ioc Y (2 * Y),
        ‖typicalModulatedShortSum (mrScheduledBlocks p u K) (3 * Y) f n H α‖) +
        H * (atypicalFactorizationSet (mrScheduledBlocks p u K) (3 * Y)).card :=
      mrtSum_Ioc_modulated_le_typical_add_density _ H Y hHY f α hbound
    _ ≤ (ε / 2) * H * Y + H * ((ε / 2) * Y) :=
      add_le_add htypY (mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg H))
    _ = _ := by ring

end

end Erdos67b
