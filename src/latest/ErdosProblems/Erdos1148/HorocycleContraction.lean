import ErdosProblems.Erdos1148.GaussRelativeFrames
import ErdosProblems.Erdos1148.BowenTube
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Contracted horocycle conjugates tend to the identity -/

namespace Erdos1148.DukeArithmetic

open Filter
open scoped MatrixGroups Topology

noncomputable def stableHorocycle (r : ℝ) : SL(2, ℝ) :=
  ⟨!![1, r; 0, 1], by simp [Matrix.det_fin_two]⟩

lemma stableHorocycle_zero : stableHorocycle 0 = 1 := by
  apply Subtype.ext
  simp [stableHorocycle, Matrix.one_fin_two]

lemma continuous_stableHorocycle : Continuous stableHorocycle := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> simp [stableHorocycle] <;> fun_prop

lemma continuous_unstableHorocycle : Continuous unstableHorocycle := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> simp [unstableHorocycle] <;> fun_prop

lemma diagonal_conjugate_stableHorocycle (r t : ℝ) :
    diagonalFlow (-t) * stableHorocycle r * diagonalFlow t =
      stableHorocycle (r * Real.exp (-t)) := by
  apply Subtype.ext
  rw [diagonalFlow_conjugate_matrix]
  simp [stableHorocycle]

lemma diagonal_conjugate_unstableHorocycle (r t : ℝ) :
    diagonalFlow (-t) * unstableHorocycle r * diagonalFlow t =
      unstableHorocycle (r * Real.exp t) := by
  apply Subtype.ext
  rw [diagonalFlow_conjugate_matrix]
  simp [unstableHorocycle]

lemma tendsto_exp_neg_nat_zero : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)

theorem stableHorocycle_conjugates_tendsto_one (r : ℝ) :
    Tendsto (fun n : ℕ => (diagonalFlow (n : ℝ))⁻¹ * stableHorocycle r * diagonalFlow (n : ℝ))
      atTop (𝓝 1) := by
  have hparam : Tendsto (fun n : ℕ => r * Real.exp (-(n : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := r)).mul tendsto_exp_neg_nat_zero
  simpa only [← diagonalFlow_neg, diagonal_conjugate_stableHorocycle, stableHorocycle_zero,
    Function.comp_def] using
    continuous_stableHorocycle.continuousAt.tendsto.comp hparam

theorem unstableHorocycle_conjugates_tendsto_one (r : ℝ) :
    Tendsto (fun n : ℕ => (diagonalFlow (-(n : ℝ)))⁻¹ * unstableHorocycle r *
      diagonalFlow (-(n : ℝ))) atTop (𝓝 1) := by
  have hparam : Tendsto (fun n : ℕ => r * Real.exp (-(n : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := r)).mul tendsto_exp_neg_nat_zero
  simpa only [← diagonalFlow_neg, diagonal_conjugate_unstableHorocycle, unstableHorocycle_zero,
    Function.comp_def] using
    continuous_unstableHorocycle.continuousAt.tendsto.comp hparam

end Erdos1148.DukeArithmetic
