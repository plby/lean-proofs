import ErdosProblems.Erdos421.PrimeCofactorSampleEnergy
import ErdosProblems.Erdos421.IntegralFromSamples

/-! # Unconditional mean squares for a prime block times a cofactor polynomial -/

namespace Erdos421

open Complex MeasureTheory Filter Topology

theorem prime_cofactor_mean_square_log_saving {k : ℕ} (hk : 5 ≤ k) {e A ε : ℝ}
    (he : 0 < e) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ M H J : ℕ, 1 ≤ M → 1 ≤ H → M ≤ X → H ≤ X → J ≤ H → M * H = X →
      (X : ℝ) ^ (1 / ((k : ℝ) + 1)) ≤ H → (H : ℝ) ≤ (X : ℝ) ^ (1 / (k : ℝ)) →
      ∀ (S : Finset ℕ) (a : ℕ → ℂ), (∀ n ∈ S, M ≤ n ∧ n ≤ 2 * M) →
      (∀ n ∈ S, ‖a n‖ ≤ 1) → S.card ≤ M →
      ∀ σ u v : ℝ, 1 ≤ σ → (Real.log X) ^ (2 * (A + twoFactorSampleExponent k) + 13) ≤ u →
      u ≤ v → v + 1 ≤ X → v + 1 - u ≤ (X : ℝ) ^ (9 / 10 - e) →
      (∫ t in u..v, ‖dirichletPolynomial S a (σ + t * I) *
        primeDirichletBlock H J (σ + t * I)‖ ^ 2) ≤ ε / (Real.log X) ^ A := by
  have hhalf : 0 < ε / 2 := by positivity
  filter_upwards [prime_cofactor_sample_energy_log_saving hk he hA hhalf] with X hsave
  intro M H J hM hH hMX hHX hJ hprod hHlo hHhi S a hS ha hcard σ u v hσ hlo huv hhi htime
  let f : ℝ → ℝ := fun t ↦ ‖dirichletPolynomial S a (σ + t * I) *
    primeDirichletBlock H J (σ + t * I)‖ ^ 2
  have hpos : ∀ n ∈ S, 0 < n := fun n hn ↦ by have := (hS n hn).1; omega
  have hcont : Continuous f :=
    ((dirichletPolynomial_vertical_continuous S a hpos σ).mul
      (primeDirichletBlock_vertical_continuous H J σ)).norm.pow 2
  have hf0 : ∀ t, 0 ≤ f t := fun t ↦ sq_nonneg _
  have hsample : ∀ (F : Finset ℕ) (t : ℕ → ℝ), (∀ i ∈ F, u ≤ t i ∧ t i ≤ v + 1) →
      (∀ i ∈ F, ∀ j ∈ F, i ≠ j → 1 ≤ |t i - t j|) →
      (∑ i ∈ F, f (t i)) ≤ (ε / 2) / (Real.log X) ^ A := by
    intro F t ht hsep
    exact hsave M H J hM hH hMX hHX hJ hprod hHlo hHhi S a hS ha hcard σ u (v + 1)
      hσ hlo (by linarith) hhi htime F t ht hsep
  have hb := integral_le_twice_separated_samples hcont hf0 huv hsample
  exact hb.trans_eq (by ring)

end Erdos421
