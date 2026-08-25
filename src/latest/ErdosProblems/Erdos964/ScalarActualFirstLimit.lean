import ErdosProblems.Erdos964.ScalarCandidateSums
import ErdosProblems.Erdos964.ScalarFirstMomentLimit
import ErdosProblems.Erdos964.ScalarPowerLogLimits
import ErdosProblems.Erdos964.LinearErrorNormalization

/-!
# The limit of the actual first scalar sieve sum
-/

namespace Erdos964

open BoundedGaps.Maynard Filter
open scoped Topology

theorem tendsto_normalizedScalarCandidateFirstSum (A B : Fin 3 → ℕ)
    (hA : ∀ i, 0 < A i) (hne : ∀ i j, i ≠ j → A i * B j ≠ A j * B i)
    (hadm : ∀ p, p.Prime → ∃ n : ℕ, ∀ i, ¬ p ∣ A i * n + B i)
    (v : ℕ) (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun t : ℕ => normalizedScalarCandidateFirstSum A B hA hne hadm v
      (t ^ 2) (modulusCutoff β t) /
        (((t ^ 2 : ℕ) : ℝ) * (Real.log (modulusCutoff β t)) ^ 3)) atTop
      (𝓝 ((scalarSieveEulerConstant (affineNormalizationModulus A B) *
        coprimeHarmonicDensity (affineNormalizationModulus A B) ^ 3) * (19 / 15))) := by
  let M := affineNormalizationModulus A B
  let N : ℕ → ℝ := fun t => (t ^ 2 : ℕ)
  let L : ℕ → ℝ := fun t => Real.log (modulusCutoff β t)
  let f : ℕ → ℝ := fun t => normalizedScalarCandidateFirstSum A B hA hne hadm v
    (t ^ 2) (modulusCutoff β t)
  let g : ℕ → ℝ := fun t => N t * scalarCandidateFirstMain M (modulusCutoff β t)
  have hM : 0 < M := affineNormalizationModulus_pos A B hA hne
  have h2M : 2 ∣ M := small_prime_dvd_affine_normalization A B hA hne hadm 2
    Nat.prime_two (by decide)
  have h3M : 3 ∣ M := small_prime_dvd_affine_normalization A B hA hne hadm 3
    Nat.prime_three (by decide)
  have hN : ∀ᶠ t : ℕ in atTop, 0 < N t := by
    filter_upwards [eventually_ge_atTop 2] with t ht
    dsimp only [N]
    positivity
  have hL : Tendsto L atTop atTop := tendsto_log_scalar_power_radius β hβ
  have hmain : Tendsto (fun t => g t / (N t * (L t) ^ 3)) atTop
      (𝓝 ((scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 3) * (19 / 15))) := by
    have h := (tendsto_scalarCandidateFirstMain M hM h2M h3M).comp
      (tendsto_scalar_power_radius β hβ)
    apply h.congr'
    filter_upwards [hN] with t hNt
    change scalarCandidateFirstMain M (modulusCutoff β t) / (L t) ^ 3 =
      g t / (N t * (L t) ^ 3)
    dsimp only [g]
    rw [mul_div_mul_left _ _ hNt.ne']
  obtain ⟨N₀, hN₀, hbound⟩ := exists_normalizedScalarCandidateS1_logSaving 0 (β / 2)
    (by positivity) (by linarith)
  have herror : ∀ᶠ t : ℕ in atTop, |f t - g t| ≤ 1 * N t := by
    filter_upwards [eventually_ge_atTop (max N₀ 2)] with t ht
    have ht2 : 2 ≤ t := (le_max_right _ _).trans ht
    have htN : N₀ ≤ t ^ 2 := by have := (le_max_left N₀ 2).trans ht; nlinarith
    have hRone : 1 ≤ modulusCutoff β t :=
      (scalar_radius_bounds t 1 (by omega) (by decide) β hβ.le hβ1.le).1
    have h := hbound (t ^ 2) htN A B hA hne hadm v (modulusCutoff β t) hRone
      (scalar_radius_le_parameter_power t (by omega) β)
    simpa only [f, g, N, M, normalizedScalarCandidateFirstSum,
      normalizedScalarCandidateWeight, pow_zero, div_one, one_mul] using h
  have hdiff := tendsto_normalized_linear_error f g N L 1 hN hL herror
  have h := hdiff.add hmain
  simp only [zero_add] at h
  apply h.congr'
  exact Eventually.of_forall (fun t => by change (_ - _) + _ = _; ring)

end Erdos964
