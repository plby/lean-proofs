import ErdosProblems.Erdos964.ScalarWirsing
import ErdosProblems.Erdos964.ScalarTransformLinear
import BoundedGaps.Maynard.CoprimeHarmonicGlobalBound

/-!
# The real-endpoint cumulative bound for the scalar transform

The natural-floor correction costs at most the fixed density times `log 2`.
The resulting error is uniform in the outer squarefree divisor `r<R`.
-/

namespace Erdos964

open BoundedGaps.Maynard

theorem exists_uniform_scalar_transform_cumulative_error :
    ∃ K C : ℝ, 0 < K ∧ 0 ≤ C ∧
      ∀ M r R : ℕ, 0 < M → 0 < r → Squarefree r → M.Coprime r → r < R →
        2 ≤ Real.log R → ∀ t : ℝ, 1 ≤ t →
      |abelCumulative (scalarTransformCoefficient M r) t -
        coprimeHarmonicDensity M * Real.log t| ≤
        11 * coprimeHarmonicDensity M *
          (K + primeLogDivisorMass M + (Real.log (Real.log R) + C + 2) + Real.log 2) := by
  obtain ⟨K, C, hK, hC, hmean⟩ := exists_uniform_scalar_scaled_mean_error
  refine ⟨K, C, hK, hC, ?_⟩
  intro M r R hM hr hrsq hcop hrR hlogR t ht
  let δ := coprimeHarmonicDensity M
  let B := K + primeLogDivisorMass M + (Real.log (Real.log R) + C + 2) + Real.log 2
  have hδ : 0 ≤ δ := by dsimp [δ, coprimeHarmonicDensity]; positivity
  have hmass : 0 ≤ primeLogDivisorMass M := by unfold primeLogDivisorMass; positivity
  have hloglog : 0 ≤ Real.log (Real.log R) := Real.log_nonneg (by linarith)
  have hlog2B : Real.log 2 ≤ B := by dsimp [B]; linarith
  have hbase := hmean M r R ⌊t⌋₊ hM hr hrsq hcop hrR hlogR
  have hfloor : |δ * Real.log (⌊t⌋₊ : ℕ) - δ * Real.log t| ≤ δ * Real.log 2 := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hδ]
    exact mul_le_mul_of_nonneg_left (abs_log_natFloor_sub_log_le_log_two_global ht) hδ
  rw [scalarTransformCoefficient_cumulative]
  calc
    _ ≤ |((r : ℝ) / r.totient) * squarefreeCoprimeInvTotientMean (M * r) ⌊t⌋₊ -
          δ * Real.log (⌊t⌋₊ : ℕ)| + |δ * Real.log (⌊t⌋₊ : ℕ) - δ * Real.log t| :=
      abs_sub_le _ _ _
    _ ≤ 10 * δ * B + δ * Real.log 2 := add_le_add hbase hfloor
    _ ≤ 11 * δ * B := by nlinarith [mul_le_mul_of_nonneg_left hlog2B hδ]
    _ = _ := rfl

end Erdos964
