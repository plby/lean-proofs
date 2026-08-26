import ErdosProblems.Erdos1148.RealDirichletLogBound
import ErdosProblems.Erdos1148.RealDirichletProduct

/-! # Absorbing the product-character logarithm into a small power -/

namespace Erdos1148.DukeArithmetic

lemma log_nat_mul_add_three_le_rpow {q r : ℕ} (hr : 0 < r)
    {a : ℝ} (ha : 0 < a) :
    Real.log ((q * r : ℕ) : ℝ) + 3 ≤ ((q : ℝ) ^ a / a + 3) * (r : ℝ) ^ a := by
  have hlog := Real.log_le_rpow_div (Nat.cast_nonneg (q * r)) ha
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hp : (1 : ℝ) ≤ (r : ℝ) ^ a := Real.one_le_rpow hr1 ha.le
  rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg q) (Nat.cast_nonneg r)] at hlog
  rw [show (q : ℝ) ^ a * (r : ℝ) ^ a / a = ((q : ℝ) ^ a / a) * (r : ℝ) ^ a by ring] at hlog
  rw [Nat.cast_mul]
  nlinarith

theorem productDirichletValue_one_le_rpow {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℝ q) (ψ : DirichletCharacter ℝ r)
    (hprod : productDirichletCharacter χ ψ ≠ 1) {a : ℝ} (ha : 0 < a) :
    realDirichletValue (productDirichletCharacter χ ψ) 1 ≤
      ((q : ℝ) ^ a / a + 3) * (r : ℝ) ^ a := by
  have h := realDirichletValue_one_norm_le_log_add_three (productDirichletCharacter χ ψ) hprod
  rw [Real.norm_eq_abs] at h
  exact ((le_abs_self _).trans h).trans (log_nat_mul_add_three_le_rpow (NeZero.pos r) ha)

end Erdos1148.DukeArithmetic
