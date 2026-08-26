import ErdosProblems.Erdos1148.FlowPeriods

/-!
# A uniform gap between nonzero integral flow periods

Conjugacy identifies the trace of an integral period matrix with
`exp(T/2)+exp(-T/2)`. For `T != 0` this integer is at least three,
which excludes a fixed neighborhood of zero from the period group.
-/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma trace_eq_of_intertwining (g h k : SL(2, ℝ)) (heq : h * g = g * k) :
    Matrix.trace (h : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.trace (k : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hh : h = g * k * g⁻¹ := by rw [← heq]; simp [mul_assoc]
  rw [hh, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]

lemma trace_diagonalFlow (T : ℝ) :
    Matrix.trace (diagonalFlow T : Matrix (Fin 2) (Fin 2) ℝ) =
      Real.exp (T / 2) + Real.exp (-(T / 2)) := by
  simp [diagonalFlow, Matrix.trace, Fin.sum_univ_two]

lemma trace_intCast (γ : SL(2, ℤ)) :
    Matrix.trace ((γ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((γ 0 0 + γ 1 1 : ℤ) : ℝ) := by
  simp [Matrix.trace, Fin.sum_univ_two]

lemma integral_flow_period_trace (g : SL(2, ℝ)) (γ : SL(2, ℤ)) (T : ℝ)
    (h : (γ : SL(2, ℝ)) * g = g * diagonalFlow T) :
    ((γ 0 0 + γ 1 1 : ℤ) : ℝ) = Real.exp (T / 2) + Real.exp (-(T / 2)) := by
  simpa only [trace_intCast, trace_diagonalFlow] using trace_eq_of_intertwining g _ _ h

theorem integral_flow_period_gap (g : SL(2, ℝ)) (γ : SL(2, ℤ)) {T : ℝ} (hT : T ≠ 0)
    (h : (γ : SL(2, ℝ)) * g = g * diagonalFlow T) :
    2 * Real.log (3 / 2 : ℝ) ≤ |T| := by
  have htrace := integral_flow_period_trace g γ T h
  have hhalf : T / 2 ≠ 0 := div_ne_zero hT (by norm_num)
  have hcosh := Real.one_lt_cosh.mpr hhalf
  rw [Real.cosh_eq] at hcosh
  have htrace2 : (2 : ℝ) < ((γ 0 0 + γ 1 1 : ℤ) : ℝ) := by linarith
  have htrace2Z : (2 : ℤ) < γ 0 0 + γ 1 1 := by exact_mod_cast htrace2
  have htrace3 : (3 : ℝ) ≤ ((γ 0 0 + γ 1 1 : ℤ) : ℝ) := by
    exact_mod_cast (show (3 : ℤ) ≤ γ 0 0 + γ 1 1 by omega)
  by_contra hgap
  have habs : |T| < 2 * Real.log (3 / 2 : ℝ) := lt_of_not_ge hgap
  have hinterval := abs_lt.mp habs
  have he1 : Real.exp (T / 2) < (3 / 2 : ℝ) := by
    apply (Real.lt_log_iff_exp_lt (by norm_num)).mp
    linarith
  have he2 : Real.exp (-(T / 2)) < (3 / 2 : ℝ) := by
    apply (Real.lt_log_iff_exp_lt (by norm_num)).mp
    linarith
  linarith

lemma period_gap_pos : 0 < 2 * Real.log (3 / 2 : ℝ) :=
  mul_pos (by norm_num) (Real.log_pos (by norm_num))

end Erdos1148.DukeArithmetic
