import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

/-! # Möbius inversion on the upper intervals of a divisor lattice -/

namespace Erdos421

open scoped ArithmeticFunction.Moebius

noncomputable def lowerMobiusTransform (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ v ∈ n.divisorsAntidiagonal, (μ v.1 : ℝ) * f v.2

theorem sum_lowerMobiusTransform (f : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    (∑ d ∈ n.divisors, lowerMobiusTransform f d) = f n := by
  exact (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mpr (fun _ _ ↦ rfl)) n hn

theorem sum_upper_divisors_complement (f : ℕ → ℝ) {P l : ℕ} (hP : P ≠ 0) (hl : l ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d then f d else 0) =
      ∑ r ∈ (P / l).divisors, f (P / r) := by
  classical
  rw [← Nat.sum_div_divisors P (fun d ↦ if l ∣ d then f d else 0)]
  have hcond (r : ℕ) (hr : r ∈ P.divisors) : l ∣ P / r ↔ r ∣ P / l := by
    have hrP := Nat.dvd_of_mem_divisors hr
    rw [Nat.dvd_div_iff_mul_dvd hrP, Nat.dvd_div_iff_mul_dvd hl, mul_comm l r]
  have he : (∑ r ∈ P.divisors, if l ∣ P / r then f (P / r) else 0) =
      ∑ r ∈ P.divisors, if r ∣ P / l then f (P / r) else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    simp only [hcond r hr]
  rw [he, ← Finset.sum_filter,
    Nat.divisors_filter_dvd_of_dvd hP (Nat.div_dvd_of_dvd hl)]

noncomputable def upperMobiusTransform (P : ℕ) (y : ℕ → ℝ) (d : ℕ) : ℝ :=
  lowerMobiusTransform (fun r ↦ y (P / r)) (P / d)

theorem sum_upperMobiusTransform (y : ℕ → ℝ) {P l : ℕ} (hP : P ≠ 0) (hl : l ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d then upperMobiusTransform P y d else 0) = y l := by
  rw [sum_upper_divisors_complement _ hP hl]
  have he : (∑ r ∈ (P / l).divisors, upperMobiusTransform P y (P / r)) =
      ∑ r ∈ (P / l).divisors, lowerMobiusTransform (fun k ↦ y (P / k)) r := by
    apply Finset.sum_congr rfl
    intro r hr
    have hrP : r ∣ P := (Nat.dvd_of_mem_divisors hr).trans (Nat.div_dvd_of_dvd hl)
    rw [upperMobiusTransform, Nat.div_div_self hrP hP]
  rw [he, sum_lowerMobiusTransform, Nat.div_div_self hl hP]
  exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) hl)
    (Nat.pos_of_dvd_of_pos hl (Nat.pos_of_ne_zero hP))

theorem upperMobiusTransform_one (y : ℕ → ℝ) {P : ℕ} (hP : P ≠ 0) :
    upperMobiusTransform P y 1 = ∑ d ∈ P.divisors, (μ d : ℝ) * y d := by
  simp only [upperMobiusTransform, Nat.div_one, lowerMobiusTransform]
  rw [Nat.sum_divisorsAntidiagonal (fun a b : ℕ ↦ (μ a : ℝ) * y (P / b))]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hP]

end Erdos421
