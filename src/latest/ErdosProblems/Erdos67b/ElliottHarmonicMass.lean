import ErdosProblems.Erdos67b.LogElliott
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Uniform harmonic mass of the exact Elliott window -/

open scoped BigOperators
open Finset

namespace Erdos67b

theorem sum_Ioc_inv_eq_harmonic_sub {N X : ℕ} (hNX : N ≤ X) :
    (∑ n ∈ Ioc N X, (n : ℝ)⁻¹) = (harmonic X : ℝ) - harmonic N := by
  have hu : Icc 1 N ∪ Ioc N X = Icc 1 X := by
    ext n
    simp only [mem_union, mem_Icc, mem_Ioc]
    omega
  have hd : Disjoint (Icc 1 N) (Ioc N X) := by
    apply disjoint_left.2
    intro n hn hm
    have := (mem_Icc.1 hn).2
    have := (mem_Ioc.1 hm).1
    omega
  have hs := sum_union hd (f := fun n : ℕ ↦ (n : ℝ)⁻¹)
  rw [hu] at hs
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  linarith

theorem elliottLogMass_eq_harmonic_sub {X W : ℕ} (hW : 0 < W) :
    elliottLogMass X W = (harmonic X : ℝ) - harmonic (X / W) := by
  rw [elliottLogMass, elliottLogWindow_eq_Ioc hW]
  exact sum_Ioc_inv_eq_harmonic_sub (Nat.div_le_self X W)

theorem elliottLogMass_bounds {X W : ℕ} (hW : 0 < W) (hWX : W ≤ X) :
    Real.log W - 1 ≤ elliottLogMass X W ∧
      elliottLogMass X W ≤ Real.log W + 1 := by
  let N := X / W
  have hN : 0 < N := Nat.div_pos hWX hW
  have hX : 0 < X := hW.trans_le hWX
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hlo : W * N ≤ X := by simpa [N, mul_comm] using Nat.div_mul_le_self X W
  have hhi : X < W * (N + 1) := by
    simpa [N, mul_comm] using Nat.lt_mul_div_succ X hW
  have hloglo : Real.log W + Real.log N ≤ Real.log ((X + 1 : ℕ) : ℝ) := by
    rw [← Real.log_mul hWr.ne' hNr.ne']
    apply Real.log_le_log (mul_pos hWr hNr)
    exact_mod_cast (by omega : W * N ≤ X + 1)
  have hloghi : Real.log X ≤ Real.log W + Real.log ((N + 1 : ℕ) : ℝ) := by
    rw [← Real.log_mul hWr.ne' (by positivity : ((N + 1 : ℕ) : ℝ) ≠ 0)]
    exact Real.log_le_log hXr (by exact_mod_cast hhi.le)
  have hXlo := log_add_one_le_harmonic X
  have hXhi := harmonic_le_one_add_log X
  have hNlo := log_add_one_le_harmonic N
  have hNhi := harmonic_le_one_add_log N
  rw [elliottLogMass_eq_harmonic_sub hW]
  change Real.log W - 1 ≤ (harmonic X : ℝ) - harmonic N ∧
    (harmonic X : ℝ) - harmonic N ≤ Real.log W + 1
  constructor <;> linarith

end Erdos67b
