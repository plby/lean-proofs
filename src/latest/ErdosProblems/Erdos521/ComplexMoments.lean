/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Exact second moments for a single complex Littlewood polynomial.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.ComplexMaximal

namespace Erdos521

open MeasureTheory
open scoped BigOperators

theorem complexPowerSum_norm_sq_eq (n : ℕ) (z : ℂ) (ε : ℕ → ℝ) :
    ‖complexPowerSum ε n z‖ ^ 2 =
      (weightedPartialSum (fun i ↦ (z ^ i).re) n ε) ^ 2 +
        (weightedPartialSum (fun i ↦ (z ^ i).im) n ε) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, complexPowerSum_re, complexPowerSum_im]
  ring

theorem complexPowerSum_norm_sq_integrable (n : ℕ) (z : ℂ) :
    Integrable (fun ε ↦ ‖complexPowerSum ε n z‖ ^ 2) sequenceLaw := by
  simp_rw [complexPowerSum_norm_sq_eq]
  exact (weightedPartialSum_memLp (fun i ↦ (z ^ i).re) n 2).integrable_sq.add
    (weightedPartialSum_memLp (fun i ↦ (z ^ i).im) n 2).integrable_sq

theorem sum_complex_weight_sq (n : ℕ) (z : ℂ) :
    (∑ i ∈ Finset.range (n + 1), ((z ^ i).re) ^ 2) +
      (∑ i ∈ Finset.range (n + 1), ((z ^ i).im) ^ 2) = geometricVariance ‖z‖ (n + 1) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (z ^ i).re ^ 2 + (z ^ i).im ^ 2 = ‖z ^ i‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    _ = _ := by rw [norm_pow, ← pow_mul, Nat.mul_comm]

theorem integral_complexPowerSum_norm_sq (n : ℕ) (z : ℂ) :
    (∫ ε, ‖complexPowerSum ε n z‖ ^ 2 ∂sequenceLaw) = geometricVariance ‖z‖ (n + 1) := by
  simp_rw [complexPowerSum_norm_sq_eq]
  rw [integral_add (weightedPartialSum_memLp (fun i ↦ (z ^ i).re) n 2).integrable_sq
    (weightedPartialSum_memLp (fun i ↦ (z ^ i).im) n 2).integrable_sq]
  simp only [weightedPartialSum, weightedIncrement, integral_linearForm_sq]
  exact sum_complex_weight_sq n z

end Erdos521
