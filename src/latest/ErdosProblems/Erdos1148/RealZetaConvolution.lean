import ErdosProblems.Erdos1148.WeightedConvolution
import ErdosProblems.Erdos1148.RealDirichletPositivity
import ErdosProblems.Erdos1148.RealSeriesCutoff

/-! # Positive real zeta-character convolutions and their hyperbola decomposition -/

namespace Erdos1148.DukeArithmetic

open Finset ArithmeticFunction
open scoped ComplexOrder

def realCharacterArithmetic {q : ℕ} (χ : DirichletCharacter ℝ q) : ArithmeticFunction ℝ :=
  toArithmeticFunction (χ ·)

noncomputable def realZetaConvolution {q : ℕ} (χ : DirichletCharacter ℝ q) : ArithmeticFunction ℝ :=
  (zeta : ArithmeticFunction ℝ) * realCharacterArithmetic χ

noncomputable def realPowerPartialSum (s : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, (n + 1 : ℝ) ^ (-s)

lemma realDirichletPartialSum_eq_sum_Ioc {q : ℕ} (χ : DirichletCharacter ℝ q)
    (s : ℝ) (N : ℕ) :
    realDirichletPartialSum χ s N = ∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s) * χ n := by
  rw [← Ico_add_one_add_one_eq_Ioc, sum_Ico_eq_sum_range]
  simp only [realDirichletPartialSum, Nat.add_sub_cancel, zero_add, add_comm 1,
    Nat.cast_add, Nat.cast_one]

lemma realPowerPartialSum_eq_sum_Ioc (s : ℝ) (N : ℕ) :
    realPowerPartialSum s N = ∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s) := by
  rw [← Ico_add_one_add_one_eq_Ioc, sum_Ico_eq_sum_range]
  simp only [realPowerPartialSum, Nat.add_sub_cancel, zero_add, add_comm 1,
    Nat.cast_add, Nat.cast_one]

lemma weighted_realCharacter_eq_partialSum {q : ℕ} (χ : DirichletCharacter ℝ q)
    (s : ℝ) (N : ℕ) :
    weightedArithmeticPartialSum (realCharacterArithmetic χ) s N =
      realDirichletPartialSum χ s N := by
  rw [weightedArithmeticPartialSum_eq_sum_range]
  apply sum_congr rfl
  intro n hn
  rw [realCharacterArithmetic, ← χ.apply_eq_toArithmeticFunction_apply (Nat.succ_ne_zero n)]
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]

lemma weighted_zeta_eq_realPowerPartialSum (s : ℝ) (N : ℕ) :
    weightedArithmeticPartialSum (zeta : ArithmeticFunction ℝ) s N =
      realPowerPartialSum s N := by
  rw [weightedArithmeticPartialSum_eq_sum_range]
  simp only [realPowerPartialSum, natCoe_apply, zeta_apply, Nat.add_one_ne_zero,
    if_false, Nat.cast_one, mul_one, Nat.cast_add]

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

theorem one_le_weighted_realZetaConvolution {q : ℕ} (χ : DirichletCharacter ℝ q)
    (s : ℝ) {X : ℕ} (hX : 1 ≤ X) :
    1 ≤ weightedArithmeticPartialSum (realZetaConvolution χ) s X := by
  have h := single_le_sum
    (s := Ioc 0 X) (f := fun n : ℕ => (n : ℝ) ^ (-s) * realZetaConvolution χ n)
    (fun n _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (realZetaConvolution_nonneg χ n)) (mem_Ioc.mpr ⟨zero_lt_one, hX⟩)
  simpa only [Nat.cast_one, Real.one_rpow, realZetaConvolution_one, mul_one,
    weightedArithmeticPartialSum] using h

theorem realZetaConvolution_hyperbola {q : ℕ} (χ : DirichletCharacter ℝ q)
    (s : ℝ) {N : ℕ} (hN : 0 < N) :
    weightedArithmeticPartialSum (realZetaConvolution χ) s (N * N) =
      (∑ m ∈ Ioc 0 N, (m : ℝ) ^ (-s) * χ m * realPowerPartialSum s (N * N / m)) +
      (∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s) * realDirichletPartialSum χ s (N * N / n)) -
      realDirichletPartialSum χ s N * realPowerPartialSum s N := by
  have hle : N ≤ N * N := by nlinarith
  have h := weighted_convolution_hyperbola (realCharacterArithmetic χ)
    (zeta : ArithmeticFunction ℝ) s hle hle le_rfl
    (by nlinarith : N * N < (N + 1) * (N + 1))
  rw [mul_comm (realCharacterArithmetic χ), ← realZetaConvolution] at h
  simp only [weighted_zeta_eq_realPowerPartialSum, weighted_realCharacter_eq_partialSum] at h
  rw [h]
  congr 2
  · apply sum_congr rfl
    intro m hm
    rw [realCharacterArithmetic, ← χ.apply_eq_toArithmeticFunction_apply
      (Nat.ne_zero_of_lt (mem_Ioc.mp hm).1)]
  · apply sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := Nat.ne_zero_of_lt (mem_Ioc.mp hn).1
    simp only [natCoe_apply, zeta_apply, hn0, if_false, Nat.cast_one, mul_one]

end Erdos1148.DukeArithmetic
