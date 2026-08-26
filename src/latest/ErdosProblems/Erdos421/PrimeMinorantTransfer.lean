import ErdosProblems.Erdos421.IntermediateWindowTransfer
import ErdosProblems.Erdos421.LogarithmicPrimeMinorant

/-! # The explicit prime minorant and its unconditional short-window transfer -/

namespace Erdos421

open MeasureTheory Filter Topology

noncomputable def intermediatePrimeMinorant (X : ℕ) (δ y : ℝ) : ℝ :=
  logarithmicRoughWindow (3 * X) (intermediatePrimeCutoff X) δ y -
    logarithmicPrimeCofactorWindow
      (sievePrimes (intermediatePrimeCutoff X) (outerPrimeCutoff X))
      (3 * X) (intermediatePrimeCutoff X) δ y

theorem intermediatePrimeMinorant_continuous (X : ℕ) (δ : ℝ) :
    Continuous (intermediatePrimeMinorant X δ) :=
  (logarithmicRoughWindow_continuous _ _ δ).sub
    (logarithmicPrimeCofactorWindow_continuous _ _ _ δ)

theorem intermediatePrimeMinorant_le_primeWindow {X : ℕ} (hX : 1 ≤ X)
    {δ y : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ Real.log (3 / 2))
    (hy : y ∈ Set.Icc (Real.log X) (Real.log (2 * X : ℝ))) :
    intermediatePrimeMinorant X δ y ≤ logarithmicPrimeWindow (3 * X) δ y := by
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hXp : (0 : ℝ) < X := by linarith
  apply logarithmic_prime_minorant (3 * X) (intermediatePrimeCutoff_le_outer hXr) hδ
    ((Real.log_nonneg hXr).trans hy.1)
  exact (logarithmic_window_endpoint_le hXp hδhi hy.2).trans
    (outerPrimeCutoff_bounds hXr).2.2

theorem intermediatePrimeMinorant_l1 {σ e : ℝ} (hσ : 0 < σ) (he : 0 < e) (he' : e < 9 / 10) :
    ∃ L : ℝ, 2 ≤ L ∧ ∀ᶠ X : ℕ in atTop,
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ (Real.log X) ^ (-L) ∧
      ∀ δ₁ δ₂ : ℝ,
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ δ₁ → δ₁ ≤ (Real.log X) ^ (-L) →
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ δ₂ → δ₂ ≤ (Real.log X) ^ (-L) →
      (∫ y in Real.log (X : ℝ)..Real.log (2 * X : ℝ),
        |intermediatePrimeMinorant X δ₁ y - intermediatePrimeMinorant X δ₂ y|) ≤
        σ / Real.log X := by
  obtain ⟨L, hL, hmean⟩ := intermediate_windows_l1 (by positivity : 0 < σ / 2) he he'
  refine ⟨L, hL, ?_⟩
  filter_upwards [hmean, eventually_ge_atTop 1] with X hmeanX hX
  refine ⟨hmeanX.1, ?_⟩
  intro δ₁ δ₂ hδ₁lo hδ₁hi hδ₂lo hδ₂hi
  obtain ⟨hr, hc⟩ := hmeanX.2 δ₁ δ₂ hδ₁lo hδ₁hi hδ₂lo hδ₂hi
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  let f := fun y ↦ logarithmicRoughWindow (3 * X) (intermediatePrimeCutoff X) δ₁ y -
    logarithmicRoughWindow (3 * X) (intermediatePrimeCutoff X) δ₂ y
  let g := fun y ↦ logarithmicPrimeCofactorWindow
      (sievePrimes (intermediatePrimeCutoff X) (outerPrimeCutoff X))
      (3 * X) (intermediatePrimeCutoff X) δ₁ y -
    logarithmicPrimeCofactorWindow
      (sievePrimes (intermediatePrimeCutoff X) (outerPrimeCutoff X))
      (3 * X) (intermediatePrimeCutoff X) δ₂ y
  have hf : Continuous f := (logarithmicRoughWindow_continuous _ _ δ₁).sub
    (logarithmicRoughWindow_continuous _ _ δ₂)
  have hg : Continuous g := (logarithmicPrimeCofactorWindow_continuous _ _ _ δ₁).sub
    (logarithmicPrimeCofactorWindow_continuous _ _ _ δ₂)
  have hm := interval_abs_integral_transfer
    ((intermediatePrimeMinorant_continuous X δ₁).sub
      (intermediatePrimeMinorant_continuous X δ₂)) hf hg
    (integrable_zero ℝ ℝ volume) (integrable_zero ℝ ℝ volume)
    (fun _ ↦ le_rfl) (fun _ ↦ le_rfl)
    (show ∀ y, (intermediatePrimeMinorant X δ₁ - intermediatePrimeMinorant X δ₂) y =
      f y - g y + 0 - 0 from fun y ↦ by
        simp only [Pi.sub_apply, intermediatePrimeMinorant, f, g]
        ring)
    (Real.log_le_log hXp (show (X : ℝ) ≤ 2 * X by linarith))
  simp only [Pi.sub_apply, Pi.zero_apply, integral_zero, add_zero, f, g] at hm
  exact (hm.trans (add_le_add hr hc)).trans_eq (by ring)

end Erdos421
