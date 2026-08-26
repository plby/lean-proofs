import ErdosProblems.Erdos421.PrimeCofactorNegativeWindowMean
import ErdosProblems.Erdos421.WindowVarianceBound

/-! # Full frequency energy for a prime block times a cofactor polynomial -/

namespace Erdos421

open Complex MeasureTheory FourierTransform Filter Topology
open scoped SchwartzMap

theorem prime_cofactor_full_window_energy (φ : 𝓢(ℝ, ℂ)) (k : ℕ) {δ e A ε : ℝ}
    (hδ : 0 < δ) (he : 0 < e) (he' : e < 9 / 10) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ C > 0, ∃ K > 0, ∀ᶠ X : ℕ in atTop,
      ∀ M H J : ℕ, 1 ≤ M → 1 ≤ H → M ≤ X → H ≤ X → J ≤ H → M * H = X →
      (X : ℝ) ^ δ ≤ H → (H : ℝ) ≤ (X : ℝ) ^ (1 / 5 : ℝ) →
      ∀ (S : Finset ℕ) (a : ℕ → ℂ), (∀ n ∈ S, M ≤ n ∧ n ≤ 2 * M) →
      (∀ n ∈ S, ‖a n‖ ≤ 1) → S.card ≤ M →
      ∀ σ u v ρ : ℝ, 1 ≤ σ →
      (Real.log X) ^ (2 * (A + twoFactorSampleExponent (primeFactorMaxMoment δ)) + 13) ≤ u →
      u ≤ v → v + 1 ≤ X → 4 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ ρ →
      (∫ t : ℝ, ‖dirichletPolynomial S a (σ + t * I) *
        primeDirichletBlock H J (σ + t * I)‖ ^ 2 *
          ‖windowMultiplier φ (4 * Real.pi / (X : ℝ) ^ (9 / 10 - e)) ρ t‖ ^ 2) ≤
        2 * (ε / (Real.log X) ^ A) + 2 * (C * ρ / (2 * Real.pi)) ^ 2 * u ^ 3 +
          2 * ((2 * K * (((X : ℝ) ^ (9 / 10 - e)) / 2) ^ (k + 1)) ^ 2 /
            (v ^ k) ^ 2 / v) := by
  obtain ⟨C, hC, hnorm, hdecay, hlip⟩ := exists_schwartz_fourier_bounds φ
  obtain ⟨K, hK, hrapid⟩ := exists_schwartz_fourier_decay φ (k + 1)
  refine ⟨C, hC, K, hK, ?_⟩
  filter_upwards [prime_cofactor_window_mean_square φ hδ he he' hA hε,
    prime_cofactor_negative_window_mean_square φ hδ he he' hA hε,
    eventually_ge_atTop (2 : ℕ)] with X hpositive hnegative hX
  intro M H J hM hH hMX hHX hJ hprod hHlo hHhi S a hS ha hcard σ u v ρ hσ hlo huv hhi hρ
  have hXp : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
  have hRp : 0 < (X : ℝ) ^ (9 / 10 - e) := Real.rpow_pos_of_pos hXp _
  have hlogp : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hup : 0 < u := (Real.rpow_pos_of_pos hlogp _).trans_le hlo
  have hvp : 0 < v := hup.trans_le huv
  have hpos : ∀ n ∈ S, 0 < n := fun n hn ↦ by have := (hS n hn).1; omega
  let D : ℝ → ℂ := fun t ↦ dirichletPolynomial S a (σ + t * I) *
    primeDirichletBlock H J (σ + t * I)
  have hD : Continuous D := (dirichletPolynomial_vertical_continuous S a hpos σ).mul
    (primeDirichletBlock_vertical_continuous H J σ)
  have hDbound : ∀ t : ℝ, ‖D t‖ ≤ 1 := by
    intro t
    have hc := dirichletPolynomial_norm_le_one S a hM (fun n hn ↦ (hS n hn).1) ha hcard hσ t
    have hp : ‖primeDirichletBlock H J (σ + t * I)‖ ≤ 1 := by
      rw [primeDirichletBlock_eq_polynomial]
      exact dirichletPolynomial_norm_le_one _ _ hH
        (fun n hn ↦ (primeBlockSupport_bounds hJ n hn).1) (by simp)
        ((primeBlockSupport_card_le H J).trans hJ) hσ t
    dsimp only [D]
    rw [norm_mul]
    nlinarith [norm_nonneg (dirichletPolynomial S a (σ + t * I)),
      norm_nonneg (primeDirichletBlock H J (σ + t * I))]
  exact window_energy_le_of_middle_bounds φ hC hnorm hdecay hlip hK.le k hrapid hRp hρ
    hup.le hvp hD hDbound
    (hpositive M H J hM hH hMX hHX hJ hprod hHlo hHhi S a hS ha hcard σ u v ρ hσ hlo huv hhi hρ)
    (hnegative M H J hM hH hMX hHX hJ hprod hHlo hHhi S a hS ha hcard σ u v ρ hσ hlo huv hhi hρ)

end Erdos421
