import ErdosProblems.Erdos67.StationaryModulationShift

/-!
# Residue balancing for observables almost invariant under translation

An observable whose one-step translation error is small has nearly equal
weighted expectations on all residue classes. This does not assume that the
observable and the residues are independent.
-/

open scoped BigOperators
open Finset Filter MeasureTheory

namespace Erdos67.StationaryModel

theorem abs_observable_shift_nat_sub_le (F : Configuration → ℝ) (ε : ℝ)
    (hε : ∀ ω, |F (shift 1 ω) - F ω| ≤ ε) (k : ℕ) (ω : Configuration) :
    |F (shift (k : ℤ) ω) - F ω| ≤ (k : ℝ) * ε := by
  induction k with
  | zero => simp [shift_zero]
  | succ k ih =>
    have he : shift ((k + 1 : ℕ) : ℤ) ω = shift 1 (shift (k : ℤ) ω) := by
      rw [Nat.cast_add, Nat.cast_one, add_comm, shift_add]
    rw [he]
    have ht := abs_sub_le (F (shift 1 (shift (k : ℤ) ω))) (F (shift (k : ℤ) ω)) (F ω)
    push_cast
    linarith [hε (shift (k : ℤ) ω)]

theorem sum_residueAtIndicator (d : ℕ+) (ω : Configuration) :
    (∑ a : ZMod d.val, residueAtIndicator d a ω) = 1 := by
  unfold residueAtIndicator
  simp

theorem integral_sum_residueAtIndicator (Q : ProbabilityMeasure Configuration)
    (d : ℕ+) (F : Configuration → ℝ) (hF : Continuous F) :
    (∑ a : ZMod d.val, ∫ ω, residueAtIndicator d a ω * F ω ∂(Q : Measure Configuration)) =
      ∫ ω, F ω ∂(Q : Measure Configuration) := by
  rw [← integral_finsetSum]
  · simp_rw [← sum_mul, sum_residueAtIndicator, one_mul]
  · intro a _
    exact integrable_configuration_continuous Q _ ((continuous_residueAtIndicator d a).mul hF)

theorem abs_residue_weight_sub_zero_le (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (d : ℕ+) (F : Configuration → ℝ) (hF : Continuous F) (ε : ℝ) (hε : 0 ≤ ε)
    (hshift : ∀ ω, |F (shift 1 ω) - F ω| ≤ ε) (a : ZMod d.val) :
    |(∫ ω, residueZeroIndicator d ω * F ω ∂(Q : Measure Configuration)) -
      ∫ ω, residueAtIndicator d a ω * F ω ∂(Q : Measure Configuration)| ≤ (d.val : ℝ) * ε := by
  let k : ℕ := (-a).val
  have hk : k ≤ d.val := (ZMod.val_lt (-a)).le
  have hka : -(k : ZMod d.val) = a := by simp [k]
  have hs := integral_shift_nat Q hQ k (fun ω ↦ residueZeroIndicator d ω * F ω)
    ((continuous_residueZeroIndicator d).mul hF)
  simp only [residueZeroIndicator_shift_nat, hka] at hs
  rw [← hs, ← integral_sub
    (f := fun ω ↦ residueAtIndicator d a ω * F (shift (k : ℤ) ω))
    (g := fun ω ↦ residueAtIndicator d a ω * F ω)
    (integrable_configuration_continuous Q _
      ((continuous_residueAtIndicator d a).mul (hF.comp (continuous_shift (k : ℤ)))))
    (integrable_configuration_continuous Q _ ((continuous_residueAtIndicator d a).mul hF))]
  have hbound (ω : Configuration) :
      ‖residueAtIndicator d a ω * F (shift (k : ℤ) ω) - residueAtIndicator d a ω * F ω‖ ≤
        (d.val : ℝ) * ε := by
    rw [← mul_sub, Real.norm_eq_abs, abs_mul]
    have ht := (abs_observable_shift_nat_sub_le F ε hshift k ω).trans
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) hε)
    unfold residueAtIndicator
    split_ifs
    · simpa using ht
    · simp only [abs_zero, zero_mul]
      exact mul_nonneg (Nat.cast_nonneg _) hε
  have hi := norm_integral_le_of_norm_le_const (μ := (Q : Measure Configuration))
    (Eventually.of_forall hbound)
  simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using hi

theorem abs_residue_normalized_weight_sub_le (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (d : ℕ+) (F : Configuration → ℝ) (hF : Continuous F) (ε : ℝ) (hε : 0 ≤ ε)
    (hshift : ∀ ω, |F (shift 1 ω) - F ω| ≤ ε) :
    |(d.val : ℝ) * (∫ ω, residueZeroIndicator d ω * F ω ∂(Q : Measure Configuration)) -
      ∫ ω, F ω ∂(Q : Measure Configuration)| ≤ (d.val : ℝ) ^ 2 * ε := by
  have he : (d.val : ℝ) * (∫ ω, residueZeroIndicator d ω * F ω ∂(Q : Measure Configuration)) =
      ∑ a : ZMod d.val, ∫ ω, residueZeroIndicator d ω * F ω ∂(Q : Measure Configuration) := by
    simp
  rw [he, ← integral_sum_residueAtIndicator Q d F hF, ← sum_sub_distrib]
  calc
    _ ≤ ∑ a : ZMod d.val,
        |(∫ ω, residueZeroIndicator d ω * F ω ∂(Q : Measure Configuration)) -
          ∫ ω, residueAtIndicator d a ω * F ω ∂(Q : Measure Configuration)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : ZMod d.val, (d.val : ℝ) * ε :=
      sum_le_sum fun a _ ↦ abs_residue_weight_sub_zero_le Q hQ d F hF ε hε hshift a
    _ = _ := by simp [pow_two, mul_assoc]

end Erdos67.StationaryModel
