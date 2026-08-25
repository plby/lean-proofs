import ErdosProblems.Erdos964.ScalarActualFirstLimit
import ErdosProblems.Erdos964.ScalarActualSecondLimit
import ErdosProblems.Erdos964.WeightedPairExtraction

/-!
# Positive sieve excess and two simultaneous semiprime events
-/

namespace Erdos964

open BoundedGaps.Maynard Filter
open scoped Topology

theorem eventually_scalar_sieve_excess (A B : Fin 3 → ℕ)
    (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i)
    (hne : ∀ i j, i ≠ j → A i * B j ≠ A j * B i)
    (hadm : ∀ p, p.Prime → ∃ n : ℕ, ∀ i, ¬ p ∣ A i * n + B i)
    (v K : ℕ) (hv : ∀ i, (A i * v + B i).Coprime (affineNormalizationModulus A B))
    (hK : 1 ≤ K)
    (hKsize : ∀ j, 2 * (A j * affineNormalizationModulus A B) + (A j * v + B j) ≤ K ^ 2)
    (η β θβ θp : ℝ) (hη : 0 < η) (hηβ : η < β)
    (hβθβ : 2 * β ≤ θβ) (hθβ1 : θβ < 1) (hβθp : β < θp) (hθphalf : θp < 1 / 2)
    (hmargin : (19 / 15 : ℝ) < 3 * (β / 2) * scalarPrimeIntegral η β) :
    ∀ᶠ t : ℕ in atTop,
      normalizedScalarCandidateFirstSum A B hA hne hadm v (t ^ 2) (modulusCutoff β t) <
        ∑ j : Fin 3, normalizedScalarCandidateSecondSum A B hA hne hadm j v
          (t ^ 2) (modulusCutoff β t)
          (scalarAffineSemiprimeSet (A j * affineNormalizationModulus A B)
            (A j * v + B j) K η t) := by
  have hβ : 0 < β := hη.trans hηβ
  have hβ1 : β < 1 := by linarith
  let M := affineNormalizationModulus A B
  let c := scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 3
  let U : ℕ → ℝ := fun t => ((t ^ 2 : ℕ) : ℝ) * (Real.log (modulusCutoff β t)) ^ 3
  let F : ℕ → ℝ := fun t => normalizedScalarCandidateFirstSum A B hA hne hadm v
    (t ^ 2) (modulusCutoff β t)
  let G : Fin 3 → ℕ → ℝ := fun j t => normalizedScalarCandidateSecondSum A B hA hne hadm j v
    (t ^ 2) (modulusCutoff β t) (scalarAffineSemiprimeSet (A j * M) (A j * v + B j) K η t)
  have hM : 0 < M := affineNormalizationModulus_pos A B hA hne
  have h2M : 2 ∣ M := small_prime_dvd_affine_normalization A B hA hne hadm 2
    Nat.prime_two (by decide)
  have h3M : 3 ∣ M := small_prime_dvd_affine_normalization A B hA hne hadm 3
    Nat.prime_three (by decide)
  have hδ : 0 < coprimeHarmonicDensity M := by
    unfold coprimeHarmonicDensity
    exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hM) (by exact_mod_cast hM)
  have hS : 0 < scalarSieveEulerConstant M :=
    lt_of_lt_of_le zero_lt_one (scalarSieveEulerConstant_ge_one M h2M h3M)
  have hc : 0 < c := mul_pos hS (pow_pos hδ 3)
  have hF : Tendsto (fun t => F t / U t) atTop (𝓝 (c * (19 / 15))) :=
    tendsto_normalizedScalarCandidateFirstSum A B hA hne hadm v β hβ hβ1
  have hG (j : Fin 3) : Tendsto (fun t => G j t / U t) atTop
      (𝓝 (c * (β / 2) * scalarPrimeIntegral η β)) :=
    tendsto_normalizedScalarCandidateSecondSum A B hA hB hne hadm j v K hv hK (hKsize j)
      η β θβ θp hη hηβ hβθβ hθβ1 hβθp hθphalf
  have hsum : Tendsto (fun t => ∑ j : Fin 3, G j t / U t) atTop
      (𝓝 (3 * (c * (β / 2) * scalarPrimeIntegral η β))) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hG j)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat] using h
  have hgap : c * (19 / 15) < 3 * (c * (β / 2) * scalarPrimeIntegral η β) := by
    calc
      _ < c * (3 * (β / 2) * scalarPrimeIntegral η β) := mul_lt_mul_of_pos_left hmargin hc
      _ = _ := by ring
  have hexcess := hF.eventually_lt hsum hgap
  filter_upwards [hexcess, eventually_ge_atTop 2,
    (tendsto_log_scalar_power_radius β hβ).eventually (eventually_gt_atTop 0)] with t ht ht2 hL
  have hU : 0 < U t := by dsimp only [U]; positivity
  rw [← Finset.sum_div] at ht
  exact (div_lt_div_iff_of_pos_right hU).mp ht

theorem eventually_two_scalar_semiprime_values (A B : Fin 3 → ℕ)
    (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i)
    (hne : ∀ i j, i ≠ j → A i * B j ≠ A j * B i)
    (hadm : ∀ p, p.Prime → ∃ n : ℕ, ∀ i, ¬ p ∣ A i * n + B i)
    (v K : ℕ) (hv : ∀ i, (A i * v + B i).Coprime (affineNormalizationModulus A B))
    (hK : 1 ≤ K)
    (hKsize : ∀ j, 2 * (A j * affineNormalizationModulus A B) + (A j * v + B j) ≤ K ^ 2)
    (η β θβ θp : ℝ) (hη : 0 < η) (hηβ : η < β)
    (hβθβ : 2 * β ≤ θβ) (hθβ1 : θβ < 1) (hβθp : β < θp) (hθphalf : θp < 1 / 2)
    (hmargin : (19 / 15 : ℝ) < 3 * (β / 2) * scalarPrimeIntegral η β) :
    ∀ᶠ t : ℕ in atTop, ∃ n ∈ Finset.Ico (t ^ 2) (2 * t ^ 2), ∃ i j : Fin 3,
      i < j ∧
        A i * affineNormalizationModulus A B * n + (A i * v + B i) ∈
          scalarAffineSemiprimeSet (A i * affineNormalizationModulus A B) (A i * v + B i) K η t ∧
        A j * affineNormalizationModulus A B * n + (A j * v + B j) ∈
          scalarAffineSemiprimeSet (A j * affineNormalizationModulus A B)
            (A j * v + B j) K η t := by
  classical
  have h := eventually_scalar_sieve_excess A B hA hB hne hadm v K hv hK hKsize
    η β θβ θp hη hηβ hβθβ hθβ1 hβθp hθphalf hmargin
  filter_upwards [h] with t ht
  apply exists_two_of_sum_filtered_weights_gt (Finset.Ico (t ^ 2) (2 * t ^ 2))
    (normalizedScalarCandidateWeight A B hA hne hadm v (t ^ 2) (modulusCutoff β t))
    (fun i n => A i * affineNormalizationModulus A B * n + (A i * v + B i) ∈
      scalarAffineSemiprimeSet (A i * affineNormalizationModulus A B) (A i * v + B i) K η t)
  · intro n hn
    exact normalizedScalarCandidateWeight_nonneg A B hA hne hadm v _ _ n
  · simp only [normalizedScalarCandidateFirstSum,
      normalizedScalarCandidateSecondSum_eq_filter, Finset.sum_filter] at ht ⊢
    convert ht using 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro n hn
    split_ifs <;> rfl

end Erdos964
