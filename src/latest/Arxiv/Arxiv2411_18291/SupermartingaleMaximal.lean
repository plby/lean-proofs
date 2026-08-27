import Mathlib.Probability.Martingale.OptionalStopping

/-!
# A finite-horizon maximal inequality for nonnegative supermartingales

Stopping on the first threshold crossing avoids a union bound over times.
Nonnegativity and bounded optional stopping then give Ville's inequality.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace Arxiv2411_18291

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}

theorem supermartingale_maximal_mul_probability_le (hM : Supermartingale M ℱ P)
    (hM0 : ∀ i, 0 ≤ᵐ[P] M i) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    c * P.real {ω | ∃ j ≤ n, c ≤ M j ω} ≤ ∫ ω, M 0 ω ∂P := by
  let τ : Ω → ℕ∞ := fun ω => (hittingBtwn M (Set.Ici c) 0 n ω : ℕ)
  have hτ : IsStoppingTime ℱ τ :=
    hM.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hbdd : ∀ ω, τ ω ≤ n := by
    intro ω
    dsimp only [τ]
    exact_mod_cast (hittingBtwn_le (u := M) (s := Set.Ici c) (n := 0) (m := n) ω)
  have hint : Integrable (stoppedValue M τ) P :=
    integrable_stoppedValue ℕ hτ hM.integrable hbdd
  have hstop := hM.neg.expected_stoppedValue_mono (isStoppingTime_const ℱ 0) hτ
    (show (fun _ => (0 : ℕ∞)) ≤ τ from fun _ => bot_le) hbdd
  change (∫ ω, -M 0 ω ∂P) ≤ ∫ ω, -stoppedValue M τ ω ∂P at hstop
  simp only [integral_neg] at hstop
  have hle : (∫ ω, stoppedValue M τ ω ∂P) ≤ ∫ ω, M 0 ω ∂P := by
    linarith only [hstop]
  have hnonneg : 0 ≤ᵐ[P] stoppedValue M τ := by
    filter_upwards [ae_all_iff.mpr hM0] with ω hω
    exact hω ((τ ω).untopA)
  have hsub : {ω | ∃ j ≤ n, c ≤ M j ω} ⊆ {ω | c ≤ stoppedValue M τ ω} := by
    rintro ω ⟨j, hj, hcross⟩
    exact stoppedValue_hittingBtwn_mem ⟨j, ⟨Nat.zero_le j, hj⟩, hcross⟩
  calc
    _ ≤ c * P.real {ω | c ≤ stoppedValue M τ ω} :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsub) hc
    _ ≤ ∫ ω, stoppedValue M τ ω ∂P :=
      mul_meas_ge_le_integral_of_nonneg hnonneg hint c
    _ ≤ _ := hle

theorem supermartingale_maximal_probability_le (hM : Supermartingale M ℱ P)
    (hM0 : ∀ i, 0 ≤ᵐ[P] M i) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    P.real {ω | ∃ j ≤ n, c ≤ M j ω} ≤ (∫ ω, M 0 ω ∂P) / c := by
  apply (le_div_iff₀ hc).mpr
  simpa only [mul_comm] using supermartingale_maximal_mul_probability_le hM hM0 hc.le n

end Arxiv2411_18291
