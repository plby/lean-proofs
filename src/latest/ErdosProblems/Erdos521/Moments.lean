/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Second moments of weighted sign sums for the analytic estimates in Erdős 521.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.Model
import ErdosProblems.Erdos521.GeometricVariance
import Mathlib

namespace Erdos521

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

theorem integral_coordinate (k : ℕ) : ∫ ε, ε k ∂sequenceLaw = 0 := by
  have h : HasLaw (fun ε : ℕ → ℝ ↦ ε k) signLaw sequenceLaw :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ signLaw) k).hasLaw
  rw [h.integral_eq]
  rw [signLaw, integral_bernoulliMeasure]
  norm_num

theorem coordinate_memLp (k : ℕ) (p : ℝ≥0∞) : MemLp (fun ε ↦ ε k) p sequenceLaw := by
  apply MemLp.of_bound (measurable_pi_apply k).aestronglyMeasurable 1
  filter_upwards [ae_sequence_signs] with ε hε
  rcases hε k with h | h <;> simp [h]

theorem integral_coordinate_sq (k : ℕ) : ∫ ε, (ε k) ^ 2 ∂sequenceLaw = 1 := by
  have heq : (fun ε ↦ (ε k) ^ 2) =ᵐ[sequenceLaw] fun _ ↦ (1 : ℝ) := by
    filter_upwards [ae_sequence_signs] with ε hε
    rcases hε k with h | h <;> simp [h]
  rw [integral_congr_ae heq]
  simp

theorem variance_coordinate (k : ℕ) : variance (fun ε ↦ ε k) sequenceLaw = 1 := by
  rw [variance_eq_integral (measurable_pi_apply k).aemeasurable, integral_coordinate]
  simpa using integral_coordinate_sq k

theorem integral_linearForm (s : Finset ℕ) (a : ℕ → ℝ) :
    (∫ ε, ∑ k ∈ s, a k * ε k ∂sequenceLaw) = 0 := by
  rw [integral_finsetSum s (fun k _ ↦ ((coordinate_memLp k 1).integrable le_rfl).const_mul (a k))]
  simp [integral_const_mul, integral_coordinate]

theorem variance_linearForm (s : Finset ℕ) (a : ℕ → ℝ) :
    variance (fun ε ↦ ∑ k ∈ s, a k * ε k) sequenceLaw = ∑ k ∈ s, (a k) ^ 2 := by
  have hind : iIndepFun (fun k ε ↦ a k * ε k) sequenceLaw :=
    independent_coefficients.comp (fun k x ↦ a k * x) (fun _ ↦ by fun_prop)
  have hLp (k : ℕ) (_ : k ∈ s) : MemLp (fun ε ↦ a k * ε k) 2 sequenceLaw :=
    (coordinate_memLp k 2).const_mul (a k)
  have hvar := IndepFun.variance_sum hLp (fun i _ j _ hij ↦ hind.indepFun hij)
  simp only [variance_const_mul, variance_coordinate, mul_one] at hvar
  convert hvar using 1
  congr 1
  ext ε
  simp

theorem integral_linearForm_sq (s : Finset ℕ) (a : ℕ → ℝ) :
    (∫ ε, (∑ k ∈ s, a k * ε k) ^ 2 ∂sequenceLaw) = ∑ k ∈ s, (a k) ^ 2 := by
  have hmeas : Measurable (fun ε : ℕ → ℝ ↦ ∑ k ∈ s, a k * ε k) :=
    Finset.measurable_sum _ fun k _ ↦ measurable_const.mul (measurable_pi_apply k)
  have h := variance_linearForm s a
  rw [variance_eq_integral hmeas.aemeasurable, integral_linearForm] at h
  simpa only [sub_zero] using h

theorem integral_powerSum_sq (n : ℕ) (x : ℝ) :
    (∫ ε, (powerSum ε (n + 1) x) ^ 2 ∂sequenceLaw) = geometricVariance x (n + 1) := by
  have heq : (fun ε ↦ powerSum ε (n + 1) x) =
      (fun ε ↦ ∑ k ∈ Finset.range (n + 1), x ^ k * ε k) := by
    funext ε
    simp only [powerSum, mul_comm]
  simp_rw [show ∀ ε, powerSum ε (n + 1) x =
    ∑ k ∈ Finset.range (n + 1), x ^ k * ε k from congrFun heq]
  rw [integral_linearForm_sq]
  simp [geometricVariance, ← pow_mul, Nat.mul_comm]

end Erdos521
