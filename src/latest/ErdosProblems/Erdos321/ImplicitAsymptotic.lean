import ErdosProblems.Erdos321.ModelComparison
import ErdosProblems.Erdos321.ModelThreshold

namespace Erdos321

/-- The entropy link after taking exact real logarithms. -/
theorem extremal_mul_log_two_le_entropy (N : ℕ) :
    (extremalSize N : ℝ) * Real.log 2 ≤ harmonicEntropy N := by
  have hpow := pow_extremalSize_le_harmonicSubsetSumCount N
  have hpos : (0 : ℝ) < (2 ^ extremalSize N : ℕ) := by positivity
  have hcast : ((2 ^ extremalSize N : ℕ) : ℝ) ≤
      harmonicSubsetSumCount N := by exact_mod_cast hpow
  calc
    (extremalSize N : ℝ) * Real.log 2 =
        Real.log (((2 ^ extremalSize N : ℕ) : ℝ)) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    _ ≤ Real.log (harmonicSubsetSumCount N : ℝ) :=
      Real.log_le_log hpos hcast
    _ = harmonicEntropy N := rfl

/-- Normalized form of the entropy link. -/
theorem normalizedExtremal_mul_log_two_le_entropy
    {N : ℕ} (hN : 1 ≤ N) :
    normalizedExtremal N * Real.log 2 ≤ normalizedEntropy N := by
  have hscale : 0 ≤ Real.log N / N := by
    have hlog : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hN)
    positivity
  have h := mul_le_mul_of_nonneg_left (extremal_mul_log_two_le_entropy N) hscale
  dsimp [normalizedExtremal, normalizedEntropy]
  nlinarith

/-- A clean implicit asymptotic answer: after one fixed terminal choice, the
normalized original extremal function is bounded above and below by fixed
multiples of the same explicit finite Neumann model. -/
theorem exists_normalizedExtremal_neumannModel_bounds :
    ∃ A : ℕ, ∃ C : ℝ, 64 ≤ A ∧ 0 ≤ C ∧ ∀ n, A ≤ n →
      (1 / 8 : ℝ) * adaptiveNeumannModel A n ≤ normalizedExtremal n ∧
        normalizedExtremal n ≤ C * adaptiveNeumannModel A n := by
  obtain ⟨Aₗ, hAₗ64, hlower⟩ := exists_neumannModel_le_normalizedExtremal
  obtain ⟨Aᵤ, K, hAᵤ64, hK0, hupper⟩ :=
    exists_normalizedEntropy_le_neumannModel
  let A := max Aₗ Aᵤ
  have hA64 : 64 ≤ A := hAₗ64.trans (le_max_left _ _)
  have hAₗ2 : 2 ≤ Aₗ := (show 2 ≤ 64 by norm_num).trans hAₗ64
  have hAᵤ2 : 2 ≤ Aᵤ := (show 2 ≤ 64 by norm_num).trans hAᵤ64
  have hAₗA : Aₗ ≤ A := le_max_left _ _
  have hAᵤA : Aᵤ ≤ A := le_max_right _ _
  obtain ⟨K₂, hK₂1, hcompare⟩ :=
    adaptiveNeumannModel_threshold_comparable hAᵤ2 hAᵤA
  let C := K * K₂ / Real.log 2
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨A, C, hA64, hC0, ?_⟩
  intro n hn
  have hnₗ : Aₗ ≤ n := hAₗA.trans hn
  have hnᵤ : Aᵤ ≤ n := hAᵤA.trans hn
  have hmodelLower := adaptiveNeumannModel_anti_threshold hAₗ2 hAₗA n
  have hlowerN := hlower n hnₗ
  have hleft : (1 / 8 : ℝ) * adaptiveNeumannModel A n ≤
      normalizedExtremal n := by
    have hm := mul_le_mul_of_nonneg_left hmodelLower (by norm_num : (0 : ℝ) ≤ 1 / 8)
    exact hm.trans hlowerN
  have hentropy := hupper n hnᵤ
  have hmodelUpper := hcompare n
  have hKM : K * adaptiveNeumannModel Aᵤ n ≤
      K * (K₂ * adaptiveNeumannModel A n) :=
    mul_le_mul_of_nonneg_left hmodelUpper hK0
  have hentropyBound : normalizedEntropy n ≤
      K * K₂ * adaptiveNeumannModel A n := by
    calc
      normalizedEntropy n ≤ K * adaptiveNeumannModel Aᵤ n := hentropy
      _ ≤ K * (K₂ * adaptiveNeumannModel A n) := hKM
      _ = K * K₂ * adaptiveNeumannModel A n := by ring
  have hn1 : 1 ≤ n := by omega
  have hlink := normalizedExtremal_mul_log_two_le_entropy hn1
  have hright : normalizedExtremal n ≤ C * adaptiveNeumannModel A n := by
    have hdiv : normalizedExtremal n ≤
        (K * K₂ * adaptiveNeumannModel A n) / Real.log 2 :=
      (le_div_iff₀ hlog2).2 (hlink.trans hentropyBound)
    dsimp [C]
    calc
      normalizedExtremal n ≤
          (K * K₂ * adaptiveNeumannModel A n) / Real.log 2 := hdiv
      _ = (K * K₂ / Real.log 2) * adaptiveNeumannModel A n := by ring
  exact ⟨hleft, hright⟩

end Erdos321
