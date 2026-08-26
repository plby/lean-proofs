import ErdosProblems.Erdos421.PrimeCofactorLogWindowEnergy
import ErdosProblems.Erdos421.SchwartzProductWindows

/-! # The unconditional variance estimate for the actual smoothed product sums -/

namespace Erdos421

open Complex MeasureTheory FourierTransform Filter Topology
open scoped SchwartzMap

noncomputable def scaledProductWindow (S T : Finset ℕ) (a b : ℕ → ℂ)
    (σ : ℝ) (φ : 𝓢(ℝ, ℂ)) (δ y : ℝ) : ℂ :=
  ∑ m ∈ S, (a m * ((m : ℝ) ^ (-σ) : ℝ)) *
    ∑ n ∈ T, (b n * ((n : ℝ) ^ (-σ) : ℝ)) *
      ((δ⁻¹ : ℝ) • φ ((y - Real.log m - Real.log n) / δ))

theorem schwartzProductWindow_normalized_apply (S T : Finset ℕ) (a b : ℕ → ℂ)
    (σ : ℝ) (φ : 𝓢(ℝ, ℂ)) {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    schwartzProductWindow S T a b σ (normalizedSchwartzScale δ hδ φ) y =
      scaledProductWindow S T a b σ φ δ y := by
  simp only [schwartzProductWindow, schwartzDirichletWindow_apply,
    normalizedSchwartzScale_apply, scaledProductWindow]

theorem prime_cofactor_smooth_variance (φ : 𝓢(ℝ, ℂ)) {δ e A ε : ℝ}
    (hδ : 0 < δ) (he : 0 < e) (he' : e < 9 / 10) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ X : ℕ in atTop,
      4 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ (Real.log X) ^ (-B) ∧
      ∀ M H J : ℕ, 1 ≤ M → 1 ≤ H → M ≤ X → H ≤ X → J ≤ H → M * H = X →
      (X : ℝ) ^ δ ≤ H → (H : ℝ) ≤ (X : ℝ) ^ (1 / 5 : ℝ) →
      ∀ (S : Finset ℕ) (a : ℕ → ℂ), (∀ n ∈ S, M ≤ n ∧ n ≤ 2 * M) →
      (∀ n ∈ S, ‖a n‖ ≤ 1) → S.card ≤ M →
      ∀ σ ρ : ℝ, 1 ≤ σ → 4 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ ρ →
      ρ ≤ (Real.log X) ^ (-B) →
      (∫ y : ℝ, ‖scaledProductWindow S (primeBlockSupport H J) a (fun _ ↦ 1) σ φ
          (4 * Real.pi / (X : ℝ) ^ (9 / 10 - e)) y -
        scaledProductWindow S (primeBlockSupport H J) a (fun _ ↦ 1) σ φ ρ y‖ ^ 2) ≤
        ε / (Real.log X) ^ A := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hε' : 0 < (2 * Real.pi) * ε := mul_pos hpi hε
  obtain ⟨B, hB, hsave⟩ := prime_cofactor_log_window_energy φ hδ he he' hA hε'
  refine ⟨B, hB, ?_⟩
  filter_upwards [hsave, eventually_ge_atTop (2 : ℕ)] with X hXsave hX
  refine ⟨hXsave.1, ?_⟩
  intro M H J hM hH hMX hHX hJ hprod hHlo hHhi S a hS ha hcard σ ρ hσ hρlo hρhi
  have hXp : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
  have hshort : 0 < 4 * Real.pi / (X : ℝ) ^ (9 / 10 - e) := by positivity
  have hlong : 0 < ρ := hshort.trans_le hρlo
  have hpos : ∀ n ∈ S, 0 < n := fun n hn ↦ by have := (hS n hn).1; omega
  have hp : ∀ p ∈ primeBlockSupport H J, 0 < p :=
    fun _ hp ↦ (Finset.mem_filter.mp hp).2.pos
  have hid := normalized_product_window_mellin_energy S (primeBlockSupport H J)
    a (fun _ ↦ 1) hpos hp σ φ hshort hlong
  simp only [schwartzProductWindow_normalized_apply, ← primeDirichletBlock_eq_polynomial] at hid
  rw [hid]
  have hb := hXsave.2 M H J hM hH hMX hHX hJ hprod hHlo hHhi S a hS ha hcard
    σ ρ hσ hρlo hρhi
  have hm := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 1 / (2 * Real.pi))
  apply hm.trans_eq
  have hpin : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

end Erdos421
