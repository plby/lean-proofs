import ErdosProblems.Erdos421.PrimeCofactorUniformMean
import ErdosProblems.Erdos421.WindowWeightCover
import ErdosProblems.Erdos421.SchwartzWindowMultiplier

/-! # Prime/cofactor mean square with a smooth-window Fourier multiplier -/

namespace Erdos421

open Complex MeasureTheory FourierTransform Filter Topology
open scoped SchwartzMap

theorem prime_cofactor_window_mean_square (φ : 𝓢(ℝ, ℂ)) {δ e A ε : ℝ}
    (hδ : 0 < δ) (he : 0 < e) (he' : e < 9 / 10) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ M H J : ℕ, 1 ≤ M → 1 ≤ H → M ≤ X → H ≤ X → J ≤ H → M * H = X →
      (X : ℝ) ^ δ ≤ H → (H : ℝ) ≤ (X : ℝ) ^ (1 / 5 : ℝ) →
      ∀ (S : Finset ℕ) (a : ℕ → ℂ), (∀ n ∈ S, M ≤ n ∧ n ≤ 2 * M) →
      (∀ n ∈ S, ‖a n‖ ≤ 1) → S.card ≤ M →
      ∀ σ u v ρ : ℝ, 1 ≤ σ →
      (Real.log X) ^ (2 * (A + twoFactorSampleExponent (primeFactorMaxMoment δ)) + 13) ≤ u →
      u ≤ v → v + 1 ≤ X → 4 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ ρ →
      (∫ t in u..v, ‖dirichletPolynomial S a (σ + t * I) *
        primeDirichletBlock H J (σ + t * I)‖ ^ 2 *
          ‖windowMultiplier φ (4 * Real.pi / (X : ℝ) ^ (9 / 10 - e)) ρ t‖ ^ 2) ≤
        ε / (Real.log X) ^ A := by
  obtain ⟨C, hC, hnorm, hdecay, hlip⟩ := exists_schwartz_fourier_bounds φ
  let ε₀ : ℝ := ε / (288 * C ^ 2)
  have hε₀ : 0 < ε₀ := by dsimp only [ε₀]; positivity
  have hpower : ∀ᶠ X : ℕ in atTop, 2 ≤ (X : ℝ) ^ (9 / 10 - e) :=
    ((tendsto_rpow_atTop (by linarith : 0 < 9 / 10 - e)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  filter_upwards [prime_cofactor_uniform_mean_square hδ he hA hε₀, hpower,
    eventually_ge_atTop (2 : ℕ)] with X hsave hR2 hX
  intro M H J hM hH hMX hHX hJ hprod hHlo hHhi S a hS ha hcard σ u v ρ hσ hlo huv hhi hρ
  let R : ℝ := (X : ℝ) ^ (9 / 10 - e)
  let Y : ℝ := R / 2
  let f : ℝ → ℝ := fun t ↦ ‖dirichletPolynomial S a (σ + t * I) *
    primeDirichletBlock H J (σ + t * I)‖ ^ 2
  let g : ℝ → ℝ := fun t ↦ ‖windowMultiplier φ (4 * Real.pi / R) ρ t‖ ^ 2
  have hRp : 0 < R := by dsimp only [R]; linarith
  have hYp : 0 < Y := by dsimp only [Y]; positivity
  have hlogp : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hup : 0 < u := (Real.rpow_pos_of_pos hlogp _).trans_le hlo
  have hQ : 0 ≤ ε₀ / (Real.log X) ^ A := by positivity
  have hpos : ∀ n ∈ S, 0 < n := fun n hn ↦ by have := (hS n hn).1; omega
  have hf : Continuous f :=
    ((dirichletPolynomial_vertical_continuous S a hpos σ).mul
      (primeDirichletBlock_vertical_continuous H J σ)).norm.pow 2
  have hg : Continuous g := (windowMultiplier_continuous φ (4 * Real.pi / R) ρ).norm.pow 2
  have hlocal : ∀ u' v' : ℝ, u ≤ u' → u' ≤ v' → v' ≤ v → v' - u' ≤ Y →
      (∫ t in u'..v', f t) ≤ ε₀ / (Real.log X) ^ A := by
    intro u' v' huu huv' hvv hlen
    apply hsave M H J hM hH hMX hHX hJ hprod hHlo hHhi S a hS ha hcard σ u' v'
      hσ (hlo.trans huu) huv' (by linarith)
    dsimp only [Y, R] at hlen
    linarith
  have hweight : ∀ t ∈ Set.Icc u v, g t ≤ (4 * C ^ 2) * (min 1 (Y / t)) ^ 2 := by
    intro t ht
    exact windowMultiplier_inverse_scale_bound φ hC hnorm hdecay hlip hRp hρ
      (hup.trans_le ht.1)
  have hb := integral_window_weight_le_of_short_integrals hf hg hup huv hYp hQ
    (by positivity : 0 ≤ 4 * C ^ 2) (fun t _ ↦ sq_nonneg _) hweight hlocal
  apply hb.trans_eq
  dsimp only [ε₀]
  have hCp : C ≠ 0 := hC.ne'
  field_simp
  ring

end Erdos421
