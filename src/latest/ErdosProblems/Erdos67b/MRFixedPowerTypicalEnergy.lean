import ErdosProblems.Erdos67b.MRFixedPowerExceptionalEnergy
import ErdosProblems.Erdos67b.MRClassSummation

/-! # Recombining every frequency class for the actual typical polynomial -/

open MeasureTheory
open scoped Interval

namespace Erdos67b

noncomputable section

theorem mrIntervalIntegral_indicator_normSq_mono
    {E : Set ℝ} (hE : MeasurableSet E) {F : ℝ → ℂ} (hF : Continuous F)
    {T U : ℝ} (hT : 0 ≤ T) (hTU : T ≤ U) :
    (∫ t in -T..T, E.indicator (fun t ↦ ‖F t‖ ^ 2) t) ≤
      ∫ t in -U..U, E.indicator (fun t ↦ ‖F t‖ ^ 2) t := by
  have hint : IntervalIntegrable (E.indicator (fun t ↦ ‖F t‖ ^ 2)) volume (-U) U := by
    rw [intervalIntegrable_iff]
    exact (intervalIntegrable_iff.mp ((hF.norm.pow 2).intervalIntegrable (-U) U)).indicator hE
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (-U) U)]
      E.indicator (fun t ↦ ‖F t‖ ^ 2) :=
    ae_restrict_of_forall_mem measurableSet_Ioc (fun t _ ↦
      Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) t)
  exact intervalIntegral.integral_mono_interval (by linarith) (by linarith) hTU hnonneg hint

theorem mrExists_typical_energy_le_firstSmall_add_small
    {eta p₁ q₁ epsilon : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hq : 1 ≤ q₁) (hpq : 2 * p₁ ≤ q₁)
    (hlogq : 1 ≤ Real.log q₁) (hsourceBudget : 4096 * Real.log q₁ ≤ eta * p₁)
    (hmertens : Real.log 2 + 2 * PrimeEstimates.mertensBound ≤ Real.log q₁ - Real.log p₁)
    (hepsilon : 0 < epsilon) :
    ∃ M₀ X₀ : ℕ, 0 < M₀ ∧ 2 ≤ X₀ ∧
      ∀ {M X : ℕ}, M₀ ≤ M → X₀ ≤ X →
      ∃ J : ℕ, 1 ≤ J ∧ mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (X : ℝ)) ∧
        Real.sqrt (Real.log (X : ℝ)) < mrLogScheduleUpper q₁ (J + 1) ∧
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRArchimedeanNonpretentious f M X →
      ∀ {T : ℝ}, 0 ≤ T → T ≤ (X : ℝ) / 2 →
        (∫ t in -T..T, ‖mrTypicalDyadicPolynomial (mrScheduledBlocks p₁ q₁ J) f X t‖ ^ 2) ≤
          mrFirstSmallEnergyBudget eta p₁ q₁ X J T + epsilon := by
  obtain ⟨M₀, X₁, hM₀, hX₁, hfull⟩ := mrExists_noSmall_typical_energy_small
    heta0 heta1 hp hq hpq hlogq hsourceBudget hmertens hepsilon
  refine ⟨M₀, max X₁ ⌈Real.exp q₁⌉₊, hM₀, hX₁.trans (le_max_left _ _), ?_⟩
  intro M X hM hX
  obtain ⟨J, hJ, hupper, hnext, hnoSmall⟩ := hfull hM ((le_max_left _ _).trans hX)
  refine ⟨J, hJ, hupper, hnext, ?_⟩
  intro f hmul hbound hnonpret T hT hTX
  have hXpos : 0 < X := by have := (le_max_left _ _).trans hX; omega
  have hscale : Real.exp q₁ ≤ X := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right X₁ ⌈Real.exp q₁⌉₊).trans hX)
  have hqexp : Real.exp 1 ≤ q₁ := by
    calc
      _ ≤ Real.exp (Real.log q₁) := Real.exp_le_exp.mpr hlogq
      _ = _ := Real.exp_log (by linarith)
  have hsmall := hnoSmall hmul hbound hnonpret
  have hmono := mrIntervalIntegral_indicator_normSq_mono
    (F := mrTypicalDyadicPolynomial (mrScheduledBlocks p₁ q₁ J) f X)
    (measurableSet_mrArithmeticNoSmall eta p₁ q₁ f J)
    (continuous_logarithmicDirichletPolynomial _ _) hT hTX
  have hfirst := mrTypical_energy_le_firstSmallBudget_add_noSmall J hJ heta0 heta1 hp
    hqexp (by linarith : p₁ ≤ q₁) hsourceBudget hmul hbound hXpos hscale hT
  exact hfirst.trans (add_le_add le_rfl (hmono.trans hsmall))

end

end Erdos67b
