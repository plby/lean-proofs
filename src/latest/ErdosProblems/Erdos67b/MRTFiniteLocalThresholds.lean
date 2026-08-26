import ErdosProblems.Erdos67b.MRTAllFrequencies

/-! # A common local first-moment threshold over the prescribed finite H interval -/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos67b

noncomputable section

theorem mrtExists_uniform_finite_firstMoment {δ R : ℝ} (hδ : 0 < δ) (hR : 1 ≤ R) :
    ∃ Hmin : ℕ, 10 ≤ Hmin ∧ ∀ Hmax : ℕ, Hmin ≤ Hmax →
      ∃ N : ℕ, Hmax ≤ N ∧
        ∀ H : ℕ, Hmin ≤ H → H ≤ Hmax →
          ∀ {A X Y : ℕ}, N ≤ A → N ≤ Y → Y ≤ X →
            Real.log X ≤ R * Real.log
              ((Y / mrtLogPowerNatWindow (Real.log (H : ℝ)) : ℕ) : ℝ) →
          ∀ {f : ℕ → ℂ}, IsCompletelyMultiplicativeOnPositive f →
            (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRTNonpretentious f A X →
          ∀ α : ℝ,
            (∑ n ∈ Finset.Ioc Y (2 * Y), ‖modulatedShortSum f n H α‖) ≤ δ * H * Y := by
  obtain ⟨Hmin, hHmin, hlocal⟩ := mrtExists_logPower_allFrequency_firstMoment hδ hR
  refine ⟨Hmin, hHmin, ?_⟩
  intro Hmax hHmax
  let S := Finset.Icc Hmin Hmax
  have heach : ∀ H ∈ S, ∀ᶠ N : ℕ in atTop,
      ∀ {A X Y : ℕ}, N ≤ A → N ≤ Y → Y ≤ X →
        Real.log X ≤ R * Real.log
          ((Y / mrtLogPowerNatWindow (Real.log (H : ℝ)) : ℕ) : ℝ) →
      ∀ {f : ℕ → ℂ}, IsCompletelyMultiplicativeOnPositive f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRTNonpretentious f A X →
      ∀ α : ℝ, (∑ n ∈ Finset.Ioc Y (2 * Y), ‖modulatedShortSum f n H α‖) ≤ δ * H * Y := by
    intro H hHS
    obtain ⟨A₀, Y₀, _, _, hfirst⟩ := hlocal H (Finset.mem_Icc.1 hHS).1
    filter_upwards [eventually_ge_atTop (max A₀ Y₀)] with N hN
    intro A X Y hA hY hYX hlog f hmul hf hnonpret α
    exact hfirst ((le_max_left _ _).trans (hN.trans hA))
      ((le_max_right _ _).trans (hN.trans hY)) hYX hlog hmul hf hnonpret α
  have hall := (Finset.eventually_all S).2 heach
  obtain ⟨N, hNmax, hN⟩ := ((eventually_ge_atTop Hmax).and hall).exists
  refine ⟨N, hNmax, ?_⟩
  intro H hHlo hHhi
  exact hN H (Finset.mem_Icc.2 ⟨hHlo, hHhi⟩)

end

end Erdos67b
