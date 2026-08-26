/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Complex maximal second moments for the polynomial estimates in Erdős 521.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.MaximalMoment
import ErdosProblems.Erdos521.InteriorBounds

namespace Erdos521

open MeasureTheory Filter
open scoped BigOperators

theorem complexPowerSum_re (n : ℕ) (z : ℂ) (ε : ℕ → ℝ) :
    (complexPowerSum ε n z).re = weightedPartialSum (fun i ↦ (z ^ i).re) n ε := by
  simp [complexPowerSum, weightedPartialSum, weightedIncrement, Complex.re_sum, mul_comm]

theorem complexPowerSum_im (n : ℕ) (z : ℂ) (ε : ℕ → ℝ) :
    (complexPowerSum ε n z).im = weightedPartialSum (fun i ↦ (z ^ i).im) n ε := by
  simp [complexPowerSum, weightedPartialSum, weightedIncrement, Complex.im_sum, mul_comm]

noncomputable def maximumSquaredComplexPowerSum (n : ℕ) (z : ℂ) (ε : ℕ → ℝ) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    (fun k ↦ ‖complexPowerSum ε k z‖ ^ 2)

theorem maximumSquaredComplexPowerSum_nonneg (n : ℕ) (z : ℂ) (ε : ℕ → ℝ) :
    0 ≤ maximumSquaredComplexPowerSum n z ε := by
  exact (sq_nonneg ‖complexPowerSum ε 0 z‖).trans
    (Finset.le_sup' (fun k ↦ ‖complexPowerSum ε k z‖ ^ 2) (by simp))

theorem maximumSquaredComplexPowerSum_measurable (n : ℕ) (z : ℂ) :
    Measurable (maximumSquaredComplexPowerSum n z) := by
  apply Finset.measurable_range_sup''
  intro k _
  unfold complexPowerSum
  fun_prop

theorem maximumSquaredComplexPowerSum_le (n : ℕ) (z : ℂ) (ε : ℕ → ℝ) :
    maximumSquaredComplexPowerSum n z ε ≤
      maximumSquaredPartialSum (fun i ↦ (z ^ i).re) n ε +
        maximumSquaredPartialSum (fun i ↦ (z ^ i).im) n ε := by
  apply Finset.sup'_le
  intro k hk
  rw [Complex.sq_norm, Complex.normSq_apply, complexPowerSum_re, complexPowerSum_im]
  have hre := Finset.le_sup' (fun k ↦ (weightedPartialSum (fun i ↦ (z ^ i).re) k ε) ^ 2) hk
  have him := Finset.le_sup' (fun k ↦ (weightedPartialSum (fun i ↦ (z ^ i).im) k ε) ^ 2) hk
  simpa only [maximumSquaredPartialSum, pow_two] using add_le_add hre him

theorem maximumSquaredComplexPowerSum_integrable (n : ℕ) (z : ℂ) :
    Integrable (maximumSquaredComplexPowerSum n z) sequenceLaw := by
  apply Integrable.mono' ((maximumSquaredPartialSum_integrable (fun i ↦ (z ^ i).re) n).add
    (maximumSquaredPartialSum_integrable (fun i ↦ (z ^ i).im) n))
    (maximumSquaredComplexPowerSum_measurable n z).aestronglyMeasurable
  exact Eventually.of_forall fun ε ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (maximumSquaredComplexPowerSum_nonneg n z ε)]
    exact maximumSquaredComplexPowerSum_le n z ε

theorem integral_maximumSquaredComplexPowerSum_le (n : ℕ) (z : ℂ) :
    (∫ ε, maximumSquaredComplexPowerSum n z ε ∂sequenceLaw) ≤
      geometricVariance ‖z‖ (n + 1) * (1 + Real.log (n + 1)) := by
  have hre := integral_maximumSquaredPartialSum_le (fun i ↦ (z ^ i).re) n
  have him := integral_maximumSquaredPartialSum_le (fun i ↦ (z ^ i).im) n
  have hmono := integral_mono (maximumSquaredComplexPowerSum_integrable n z)
    ((maximumSquaredPartialSum_integrable (fun i ↦ (z ^ i).re) n).add
      (maximumSquaredPartialSum_integrable (fun i ↦ (z ^ i).im) n))
    (maximumSquaredComplexPowerSum_le n z)
  simp only [Pi.add_apply] at hmono
  rw [integral_add (maximumSquaredPartialSum_integrable (fun i ↦ (z ^ i).re) n)
    (maximumSquaredPartialSum_integrable (fun i ↦ (z ^ i).im) n)] at hmono
  have hvariance : (∑ i ∈ Finset.range (n + 1), ((z ^ i).re) ^ 2) +
      (∑ i ∈ Finset.range (n + 1), ((z ^ i).im) ^ 2) = geometricVariance ‖z‖ (n + 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    calc
      (z ^ i).re ^ 2 + (z ^ i).im ^ 2 = ‖z ^ i‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
      _ = _ := by rw [norm_pow, ← pow_mul, Nat.mul_comm]
  calc
    _ ≤ _ := hmono.trans (add_le_add hre him)
    _ = _ := by rw [← add_mul, hvariance]

end Erdos521
