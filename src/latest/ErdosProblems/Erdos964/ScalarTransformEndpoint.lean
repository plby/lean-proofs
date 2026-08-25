import ErdosProblems.Erdos964.ScalarTransformCumulative
import ErdosProblems.Erdos964.LinearLogAbel

/-!
# Evaluating the transformed coefficient at its strict arithmetic endpoint

Abel summation gives the quadratic primitive with a uniform logarithmic
error. Replacing the strict endpoint by `log(R/r)` is a separate step.
-/

namespace Erdos964

open BoundedGaps.Maynard

theorem exists_uniform_scalar_transform_endpoint_error :
    ∃ K C : ℝ, 0 < K ∧ 0 ≤ C ∧
      ∀ M R r : ℕ, 0 < M → r ∣ scalarSievePrimeProduct M R → r < R →
        2 ≤ Real.log R →
      let Q := (R - 1) / r
      |scalarSemiprimeTransform (scalarSievePrimeProduct M R) (scalarLinearY R) r -
        coprimeHarmonicDensity M *
          ((7 - 6 * Real.log r / Real.log R) * Real.log Q -
            (3 / Real.log R) * (Real.log Q) ^ 2)| ≤
        77 * coprimeHarmonicDensity M *
          (K + primeLogDivisorMass M + (Real.log (Real.log R) + C + 2) + Real.log 2) := by
  obtain ⟨K, C, hK, hC, hcumulative⟩ := exists_uniform_scalar_transform_cumulative_error
  refine ⟨K, C, hK, hC, ?_⟩
  intro M R r hM hr hrR hlogR
  dsimp only
  let Q := (R - 1) / r
  let a := 7 - 6 * Real.log r / Real.log R
  let b := 6 / Real.log R
  let δ := coprimeHarmonicDensity M
  let B := K + primeLogDivisorMass M + (Real.log (Real.log R) + C + 2) + Real.log 2
  let E := 11 * δ * B
  have hrsq := (scalarSievePrimeProduct_squarefree M R).squarefree_of_dvd hr
  have hr0 := Nat.pos_of_ne_zero hrsq.ne_zero
  have hrM := ((scalarSievePrimeProduct_coprime M R).coprime_dvd_left hr).symm
  have hR : 1 ≤ R := by omega
  have hQ : 1 ≤ Q := Nat.div_pos (by omega) hr0
  have hδ : 0 ≤ δ := by dsimp [δ, coprimeHarmonicDensity]; positivity
  have hmass : 0 ≤ primeLogDivisorMass M := by unfold primeLogDivisorMass; positivity
  have hloglog : 0 ≤ Real.log (Real.log R) := Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hB : 0 ≤ B := by dsimp [B]; linarith
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hlinear : scalarLinearY R (r * Q) = a - b * Real.log Q :=
    scalarLinearY_mul_eq_linear_log R r Q hR hr0 (Finset.mem_Icc.mpr ⟨hQ, le_rfl⟩)
  have hba : b * Real.log Q ≤ a := by
    have h := (scalarLinearY_bounds R (r * Q)).1
    rw [hlinear] at h
    linarith
  have ha7 : a ≤ 7 := by
    dsimp only [a]
    have hlogr := Real.log_natCast_nonneg r
    have hnonneg : 0 ≤ 6 * Real.log r / Real.log R := by positivity
    linarith
  have happrox : ∀ t ∈ Set.Icc (1 : ℝ) Q,
      |abelCumulative (scalarTransformCoefficient M r) t - δ * Real.log t| ≤ E := by
    intro t ht
    exact hcumulative M r R hM hr0 hrsq hrM hrR hlogR t ht.1
  have hAbel := linear_log_weighted_abel_error Q hQ (scalarTransformCoefficient M r)
    (scalarTransformCoefficient_zero M r) δ E a b hE hb hba happrox
  rw [← scalarSemiprimeTransform_eq_linear_log_sum M R r hR hr] at hAbel
  have hb2 : b / 2 = 3 / Real.log R := by dsimp only [b]; ring
  rw [hb2] at hAbel
  calc
    _ ≤ E * a := hAbel
    _ ≤ E * 7 := mul_le_mul_of_nonneg_left ha7 hE
    _ = _ := by dsimp only [E, δ, B]; ring

end Erdos964
