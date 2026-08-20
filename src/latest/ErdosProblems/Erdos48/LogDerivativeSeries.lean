/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.ZeroDetector
import BoundedGaps.BombieriVinogradov.Analytic.ThreeFourOne
import Mathlib.NumberTheory.LSeries.Deriv

/-!
# High logarithmic derivatives as Dirichlet series

On the half-plane `re s > 1`, the high derivatives of `-L'/L` are the
logarithmically weighted von Mangoldt series.  The statements here retain
Mathlib's `LSeries.logMul` representation and also identify its coefficients
pointwise.
-/

namespace Erdos48

open Complex LSeries

noncomputable section

/-- Iterating `LSeries.logMul` simply multiplies a coefficient by the
corresponding power of `log n`. -/
theorem iterate_logMul_apply (k : ℕ) (a : ℕ → ℂ) (n : ℕ) :
    (logMul^[k]) a n = (Real.log n : ℂ) ^ k * a n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      change Complex.log n * (logMul^[k]) a n = _
      rw [ih, ← Complex.natCast_log]
      ring

/-- The twist of the von Mangoldt function has abscissa of absolute
convergence at most one. -/
theorem abscissaOfAbsConv_twist_vonMangoldt_le_one
    {q : ℕ} (chi : DirichletCharacter ℂ q) :
    abscissaOfAbsConv
        ((fun n : ℕ ↦ chi n) *
          fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro sigma hsigma
  have hsigma' : 1 < sigma := by exact_mod_cast hsigma
  simpa using DirichletCharacter.LSeriesSummable_twist_vonMangoldt
    chi (s := (sigma : ℂ)) hsigma'

/-- Exact high-derivative Dirichlet-series identity for a continued
Dirichlet `L`-function on `re s > 1`. -/
theorem iteratedDeriv_neg_logDeriv_LFunction_eq_LSeries
    {q k : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv k
        (fun z ↦ -logDeriv (DirichletCharacter.LFunction chi) z) s =
      (-1 : ℂ) ^ k *
        LSeries ((logMul^[k])
          ((fun n : ℕ ↦ chi n) *
            fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℂ))) s := by
  let U : Set ℂ := {z | 1 < z.re}
  let a : ℕ → ℂ :=
    (fun n : ℕ ↦ chi n) *
      fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℂ)
  have hUopen : IsOpen U := by
    exact isOpen_lt continuous_const continuous_re
  have heq : Set.EqOn
      (fun z ↦ -logDeriv (DirichletCharacter.LFunction chi) z)
      (LSeries a) U := by
    intro z hz
    change 1 < z.re at hz
    change -logDeriv (DirichletCharacter.LFunction chi) z = LSeries a z
    rw [BoundedGaps.Maynard.neg_logDeriv_LFunction_eq_LSeries chi hz,
      logDeriv_apply, ← neg_div,
      ← DirichletCharacter.LSeries_twist_vonMangoldt_eq chi hz]
  have hderiv := heq.iteratedDeriv_of_isOpen hUopen k hs
  have habsle : abscissaOfAbsConv a ≤ 1 := by
    simpa only [a] using abscissaOfAbsConv_twist_vonMangoldt_le_one chi
  have habs : abscissaOfAbsConv a < s.re :=
    habsle.trans_lt (by exact_mod_cast hs)
  exact hderiv.trans (LSeries_iteratedDeriv k habs)

/-- Coefficient-level version of
`iteratedDeriv_neg_logDeriv_LFunction_eq_LSeries`. -/
theorem iteratedDeriv_neg_logDeriv_LFunction_eq_weighted_LSeries
    {q k : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv k
        (fun z ↦ -logDeriv (DirichletCharacter.LFunction chi) z) s =
      (-1 : ℂ) ^ k *
        LSeries (fun n : ℕ ↦
          (Real.log n : ℂ) ^ k * chi n *
            (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  rw [iteratedDeriv_neg_logDeriv_LFunction_eq_LSeries chi hs]
  congr 2
  funext n
  rw [iterate_logMul_apply]
  simp only [Pi.mul_apply]
  ring

end

end Erdos48
