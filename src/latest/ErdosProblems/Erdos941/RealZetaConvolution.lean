/- Adapted from the checked repository proof in Erdos1148/RealZetaConvolution.lean. -/
import ErdosProblems.Erdos941.RealDirichletPositivity

/-! # Real zeta-character convolution coefficients -/

namespace Erdos941.Analytic

open Finset ArithmeticFunction
open scoped ComplexOrder

def realCharacterArithmetic {q : ℕ} (χ : DirichletCharacter ℝ q) : ArithmeticFunction ℝ :=
  toArithmeticFunction (χ ·)

noncomputable def realZetaConvolution {q : ℕ} (χ : DirichletCharacter ℝ q) : ArithmeticFunction ℝ :=
  (zeta : ArithmeticFunction ℝ) * realCharacterArithmetic χ

lemma realDirichletPartialSum_eq_sum_Ioc {q : ℕ} (χ : DirichletCharacter ℝ q)
    (s : ℝ) (N : ℕ) :
    realDirichletPartialSum χ s N = ∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s) * χ n := by
  rw [← Ico_add_one_add_one_eq_Ioc, sum_Ico_eq_sum_range]
  simp only [realDirichletPartialSum, Nat.add_sub_cancel, zero_add, add_comm 1,
    Nat.cast_add, Nat.cast_one]

lemma complexified_realZetaConvolution {q : ℕ} (χ : DirichletCharacter ℝ q) (n : ℕ) :
    (realZetaConvolution χ n : ℂ) = (complexDirichletCharacter χ).zetaMul n := by
  simp only [realZetaConvolution, DirichletCharacter.zetaMul, mul_apply]
  push_cast
  apply sum_congr rfl
  intro p hp
  have hmul0 : p.1 * p.2 ≠ 0 := by
    rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]
    exact (Nat.mem_divisorsAntidiagonal.mp hp).2
  have hp0 : p.1 ≠ 0 := left_ne_zero_of_mul hmul0
  have hq0 : p.2 ≠ 0 := right_ne_zero_of_mul hmul0
  simp [realCharacterArithmetic, toArithmeticFunction, complexDirichletCharacter,
    MulChar.ringHomComp_apply, hp0, hq0]

theorem realZetaConvolution_nonneg {q : ℕ} (χ : DirichletCharacter ℝ q) (n : ℕ) :
    0 ≤ realZetaConvolution χ n := by
  have hψ := ((realDirichletCharacter_isQuadratic χ).comp Complex.ofRealHom).sq_eq_one
  have h := (complexDirichletCharacter χ).zetaMul_nonneg hψ n
  rw [← complexified_realZetaConvolution] at h
  exact Complex.zero_le_real.mp h

@[simp] lemma realZetaConvolution_one {q : ℕ} (χ : DirichletCharacter ℝ q) :
    realZetaConvolution χ 1 = 1 := by
  apply Complex.ofReal_injective
  rw [complexified_realZetaConvolution,
    (complexDirichletCharacter χ).isMultiplicative_zetaMul.map_one, Complex.ofReal_one]

end Erdos941.Analytic
