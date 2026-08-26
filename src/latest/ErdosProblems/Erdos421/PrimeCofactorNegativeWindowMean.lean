import ErdosProblems.Erdos421.PrimeCofactorWindowMean
import ErdosProblems.Erdos421.WindowReflection

/-! # The smooth-window mean square on the negative frequency interval -/

namespace Erdos421

open Complex MeasureTheory FourierTransform Filter Topology
open scoped SchwartzMap ComplexConjugate

theorem prime_cofactor_negative_window_mean_square (φ : 𝓢(ℝ, ℂ)) {δ e A ε : ℝ}
    (hδ : 0 < δ) (he : 0 < e) (he' : e < 9 / 10) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ M H J : ℕ, 1 ≤ M → 1 ≤ H → M ≤ X → H ≤ X → J ≤ H → M * H = X →
      (X : ℝ) ^ δ ≤ H → (H : ℝ) ≤ (X : ℝ) ^ (1 / 5 : ℝ) →
      ∀ (S : Finset ℕ) (a : ℕ → ℂ), (∀ n ∈ S, M ≤ n ∧ n ≤ 2 * M) →
      (∀ n ∈ S, ‖a n‖ ≤ 1) → S.card ≤ M →
      ∀ σ u v ρ : ℝ, 1 ≤ σ →
      (Real.log X) ^ (2 * (A + twoFactorSampleExponent (primeFactorMaxMoment δ)) + 13) ≤ u →
      u ≤ v → v + 1 ≤ X → 4 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ ρ →
      (∫ t in -v..-u, ‖dirichletPolynomial S a (σ + t * I) *
        primeDirichletBlock H J (σ + t * I)‖ ^ 2 *
          ‖windowMultiplier φ (4 * Real.pi / (X : ℝ) ^ (9 / 10 - e)) ρ t‖ ^ 2) ≤
        ε / (Real.log X) ^ A := by
  filter_upwards [prime_cofactor_window_mean_square (reflectedSchwartz φ) hδ he he' hA hε]
    with X hsave
  intro M H J hM hH hMX hHX hJ hprod hHlo hHhi S a hS ha hcard σ u v ρ hσ hlo huv hhi hρ
  have hpos : ∀ n ∈ S, 0 < n := fun n hn ↦ by have := (hS n hn).1; omega
  have hconj : ∀ n ∈ S, ‖conj (a n)‖ ≤ 1 := by simpa only [Complex.norm_conj] using ha
  have hb := hsave M H J hM hH hMX hHX hJ hprod hHlo hHhi S (fun n ↦ conj (a n))
    hS hconj hcard σ u v ρ hσ hlo huv hhi hρ
  have he : (∫ t in -v..-u, ‖dirichletPolynomial S a (σ + t * I) *
      primeDirichletBlock H J (σ + t * I)‖ ^ 2 *
        ‖windowMultiplier φ (4 * Real.pi / (X : ℝ) ^ (9 / 10 - e)) ρ t‖ ^ 2) =
      ∫ t in u..v, ‖dirichletPolynomial S (fun n ↦ conj (a n)) (σ + t * I) *
        primeDirichletBlock H J (σ + t * I)‖ ^ 2 *
          ‖windowMultiplier (reflectedSchwartz φ)
            (4 * Real.pi / (X : ℝ) ^ (9 / 10 - e)) ρ t‖ ^ 2 := by
    rw [← intervalIntegral.integral_comp_neg (a := u) (b := v)]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [dirichletPolynomial_reflected S a hpos σ t, primeDirichletBlock_reflected,
      ← map_mul, Complex.norm_conj, windowMultiplier_reflected]
  rwa [he]

end Erdos421
