import ErdosProblems.Erdos964.ScalarCandidateSums
import ErdosProblems.Erdos964.ScalarCandidateSecondSaving
import ErdosProblems.Erdos964.ScalarSecondMainLimit
import ErdosProblems.Erdos964.ScalarNormalizationDensity
import ErdosProblems.Erdos964.LinearErrorNormalization

/-!
# The limit of the actual second scalar sieve sum
-/

namespace Erdos964

open BoundedGaps.Maynard Filter
open scoped Topology

noncomputable def scalarAffineSemiprimeSet (m c K : ℕ) (η : ℝ) (t : ℕ) : Finset ℕ :=
  semiprimeScaleInterval (scalarSmallPrimeSupport η K t) (K * t)
    (m * t ^ 2 + c - 1) (m * (2 * t ^ 2) + c - 1)

theorem tendsto_normalizedScalarCandidateSecondSum (A B : Fin 3 → ℕ)
    (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i)
    (hne : ∀ i j, i ≠ j → A i * B j ≠ A j * B i)
    (hadm : ∀ p, p.Prime → ∃ n : ℕ, ∀ i, ¬ p ∣ A i * n + B i)
    (j : Fin 3) (v K : ℕ)
    (hv : ∀ i, (A i * v + B i).Coprime (affineNormalizationModulus A B))
    (hK : 1 ≤ K)
    (hKsize : 2 * (A j * affineNormalizationModulus A B) + (A j * v + B j) ≤ K ^ 2)
    (η β θβ θp : ℝ) (hη : 0 < η) (hηβ : η < β)
    (hβθβ : 2 * β ≤ θβ) (hθβ1 : θβ < 1) (hβθp : β < θp) (hθphalf : θp < 1 / 2) :
    Tendsto (fun t : ℕ => normalizedScalarCandidateSecondSum A B hA hne hadm j v
      (t ^ 2) (modulusCutoff β t)
      (scalarAffineSemiprimeSet (A j * affineNormalizationModulus A B) (A j * v + B j) K η t) /
        (((t ^ 2 : ℕ) : ℝ) * (Real.log (modulusCutoff β t)) ^ 3)) atTop
      (𝓝 ((scalarSieveEulerConstant (affineNormalizationModulus A B) *
        coprimeHarmonicDensity (affineNormalizationModulus A B) ^ 3) *
          (β / 2) * scalarPrimeIntegral η β)) := by
  have hβ : 0 < β := hη.trans hηβ
  have hβ1 : β < 1 := by linarith
  let M := affineNormalizationModulus A B
  let m := A j * M
  let c := A j * v + B j
  let N : ℕ → ℝ := fun t => (t ^ 2 : ℕ)
  let L : ℕ → ℝ := fun t => Real.log (modulusCutoff β t)
  let f : ℕ → ℝ := fun t => normalizedScalarCandidateSecondSum A B hA hne hadm j v
    (t ^ 2) (modulusCutoff β t) (scalarAffineSemiprimeSet m c K η t)
  let g : ℕ → ℝ := fun t => (1 / (m.totient : ℝ)) * scalarSecondMainAtScale M m c K η β t
  have hM : 0 < M := affineNormalizationModulus_pos A B hA hne
  have hm : 1 ≤ m := Nat.mul_pos (hA j) hM
  have hc : 1 ≤ c := Nat.add_pos_right _ (hB j)
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
      (𝓝 ((scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 3) *
        (β / 2) * scalarPrimeIntegral η β)) := by
    have h := (tendsto_scalarSecondMainAtScale M m c K hM h2M h3M hm hc hK hKsize
      η β hη hηβ hβ1).const_mul (1 / (m.totient : ℝ))
    have hcancel : (m : ℝ) / m.totient * coprimeHarmonicDensity M = 1 :=
      normalized_affine_totient_density_cancel A B hA hne j
    have hconst : (1 / (m.totient : ℝ)) *
        ((scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 4) *
          (m : ℝ) * (β / 2) * scalarPrimeIntegral η β) =
        (scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 3) *
          (β / 2) * scalarPrimeIntegral η β := by
      calc
        _ = ((m : ℝ) / m.totient * coprimeHarmonicDensity M) *
            ((scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 3) *
              (β / 2) * scalarPrimeIntegral η β) := by ring
        _ = _ := by rw [hcancel, one_mul]
    rw [hconst] at h
    apply h.congr'
    exact Eventually.of_forall (fun t => by dsimp only [g, N, L]; ring)
  obtain ⟨C, hC, T₀, hT₀, hbound⟩ := exists_normalizedScalarCandidateS2_logSaving
    A B hA hB hne hadm j v K hv hK hKsize 0 β η θβ θp hβ hη hβθβ hθβ1 hβθp hθphalf
  have herror : ∀ᶠ t : ℕ in atTop, |f t - g t| ≤ (C * (K : ℝ) ^ 2) * N t := by
    filter_upwards [eventually_ge_atTop T₀] with t ht
    have h := hbound t ht
    simp only [pow_zero, div_one] at h
    change |f t - g t| ≤ C * ((K * t : ℕ) : ℝ) ^ 2 at h
    calc
      _ ≤ C * ((K * t : ℕ) : ℝ) ^ 2 := h
      _ = _ := by dsimp only [N]; push_cast; ring
  have hdiff := tendsto_normalized_linear_error f g N L (C * (K : ℝ) ^ 2) hN hL herror
  have h := hdiff.add hmain
  simp only [zero_add] at h
  apply h.congr'
  exact Eventually.of_forall (fun t => by change (_ - _) + _ = _; ring)

end Erdos964
