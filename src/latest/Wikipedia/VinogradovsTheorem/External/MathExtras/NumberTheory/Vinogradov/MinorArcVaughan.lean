/-
This file is derived from Gershon Bialer's ternary-Goldbach development.

The reused upstream material was released under the Apache License,
Version 2.0, as described in the file LICENSE. This file has been modified.
The upstream copyright and author notices are retained below.

Copyright (c) 2026 Gershon Bialer. All rights reserved.
-/
import Wikipedia.VinogradovsTheorem.External.MathExtras.NumberTheory.Vinogradov.CircleMethod
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Minor Arcs via Vaughan Identity

This module is the planned home for the Vaughan-identity infrastructure behind
true minor-arc cancellation.

Target contents:

* finite Vaughan identity for von-Mangoldt sums;
* Type I and Type II sum definitions;
* denominator-range hypotheses for rational approximants;
* logarithmic-saving bounds for minor arcs.
-/

namespace Vinogradov

open Finset
open scoped ArithmeticFunction

/-! ## Finite Vaughan identity -/

/-- Coefficient sequence for finite Vaughan-style decompositions. -/
abbrev CoeffSeq := ℕ → ℂ

/-- The `μ` coefficients with the Vaughan cutoff `c ≤ U`. -/
noncomputable def vaughanMuLow (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ U then (ArithmeticFunction.moebius n : ℝ) else 0, by simp⟩

/-- The complementary `μ` coefficients with `U < c`. -/
noncomputable def vaughanMuHigh (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if U < n then (ArithmeticFunction.moebius n : ℝ) else 0, by simp⟩

/-- The small direct von-Mangoldt contribution `Λ(n) 1[n ≤ V]`. -/
noncomputable def vaughanLambdaLow (V : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ V then ArithmeticFunction.vonMangoldt n else 0, by simp⟩

/-- The complementary von-Mangoldt contribution `Λ(n) 1[V < n]`. -/
noncomputable def vaughanLambdaHigh (V : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if V < n then ArithmeticFunction.vonMangoldt n else 0, by simp⟩

/-- Type-I part of Vaughan's identity:
`μ_{≤U} * (log - ζ * Λ_{≤V})`.
Unfolding convolution gives
`∑_{c|n, c≤U} μ(c) (log(n/c) - ∑_{d|n/c, d≤V} Λ(d))`. -/
noncomputable def vaughanTypeIArithmetic (U V : ℕ) : ArithmeticFunction ℝ :=
  vaughanMuLow U *
    (ArithmeticFunction.log -
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLambdaLow V)

/-- Type-II tail of Vaughan's identity:
`Λ_{>V} * (μ_{>U} * ζ)`.
Unfolding convolution gives
`∑_{d|n, V<d} Λ(d) ∑_{c|n/d, U<c} μ(c)`. -/
noncomputable def vaughanTypeIIArithmetic (U V : ℕ) : ArithmeticFunction ℝ :=
  vaughanLambdaHigh V *
    (vaughanMuHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))

theorem vaughanMuLow_add_high (U : ℕ) :
    vaughanMuLow U + vaughanMuHigh U = (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
  ext n
  unfold vaughanMuLow vaughanMuHigh
  change (if n ≤ U then (ArithmeticFunction.moebius n : ℝ) else 0) +
      (if U < n then (ArithmeticFunction.moebius n : ℝ) else 0) =
        (ArithmeticFunction.moebius n : ℝ)
  by_cases hn : n ≤ U
  · have hnot : ¬ U < n := not_lt.mpr hn
    simp [hn, hnot]
  · have hlt : U < n := lt_of_not_ge hn
    simp [hn, hlt]

theorem vaughanLambdaLow_add_high (V : ℕ) :
    vaughanLambdaLow V + vaughanLambdaHigh V = ArithmeticFunction.vonMangoldt := by
  ext n
  unfold vaughanLambdaLow vaughanLambdaHigh
  change (if n ≤ V then ArithmeticFunction.vonMangoldt n else 0) +
      (if V < n then ArithmeticFunction.vonMangoldt n else 0) =
        ArithmeticFunction.vonMangoldt n
  by_cases hn : n ≤ V
  · have hnot : ¬ V < n := not_lt.mpr hn
    simp [hn, hnot]
  · have hlt : V < n := lt_of_not_ge hn
    simp [hn, hlt]

/-- At the degenerate Vaughan cutoff `U = 1`, the low Möbius truncation is the
Dirichlet-convolution identity. -/
theorem vaughanMuLow_one_eq_one :
    vaughanMuLow 1 = (1 : ArithmeticFunction ℝ) := by
  ext n
  unfold vaughanMuLow
  by_cases hnle : n ≤ 1
  · interval_cases n <;> simp
  · have hn1 : n ≠ 1 := by omega
    simp [hnle, hn1]

/-- At the degenerate Vaughan cutoff `U = 1`, the high Möbius tail convolved
with `ζ` is `1 - ζ`. -/
theorem vaughanMuHigh_one_mul_zeta :
    vaughanMuHigh 1 * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
      (1 : ArithmeticFunction ℝ) - (ArithmeticFunction.zeta : ArithmeticFunction ℝ) := by
  have hsum := vaughanMuLow_add_high 1
  have hhigh :
      vaughanMuHigh 1 =
        (ArithmeticFunction.moebius : ArithmeticFunction ℝ) - (1 : ArithmeticFunction ℝ) := by
    rw [vaughanMuLow_one_eq_one] at hsum
    rw [← hsum]
    abel
  rw [hhigh, sub_mul, ArithmeticFunction.coe_moebius_mul_coe_zeta]
  simp

/-- At the degenerate Vaughan cutoff `V = 1`, the high von-Mangoldt truncation
is all of `Λ`, since `Λ(0)=Λ(1)=0`. -/
theorem vaughanLambdaHigh_one_eq_vonMangoldt :
    vaughanLambdaHigh 1 = ArithmeticFunction.vonMangoldt := by
  ext n
  unfold vaughanLambdaHigh
  by_cases hn : n ≤ 1
  · interval_cases n <;> simp [ArithmeticFunction.map_zero]
  · have hlt : 1 < n := lt_of_not_ge hn
    simp [hlt]

/-- The Type-II Vaughan arithmetic piece at `U = V = 1` collapses to the
single coefficient sequence `Λ - log`. -/
theorem vaughanTypeIIArithmetic_one_one_eq :
    vaughanTypeIIArithmetic 1 1 =
      ArithmeticFunction.vonMangoldt - ArithmeticFunction.log := by
  unfold vaughanTypeIIArithmetic
  rw [vaughanLambdaHigh_one_eq_vonMangoldt, vaughanMuHigh_one_mul_zeta,
    mul_sub, mul_one, ArithmeticFunction.vonMangoldt_mul_zeta]

theorem vaughanTypeIArithmetic_eq (U V : ℕ) :
    vaughanTypeIArithmetic U V =
      vaughanLambdaHigh V *
        (vaughanMuLow U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) := by
  have hlog :
      ArithmeticFunction.log -
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLambdaLow V =
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLambdaHigh V := by
    calc
      ArithmeticFunction.log -
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLambdaLow V =
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * ArithmeticFunction.vonMangoldt -
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLambdaLow V := by
            rw [ArithmeticFunction.zeta_mul_vonMangoldt]
      _ = (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            (vaughanLambdaLow V + vaughanLambdaHigh V) -
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLambdaLow V := by
            rw [vaughanLambdaLow_add_high]
      _ = (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLambdaHigh V := by ring
  unfold vaughanTypeIArithmetic
  rw [hlog]
  ring

theorem vaughanTypeI_add_typeII (U V : ℕ) :
    vaughanTypeIArithmetic U V + vaughanTypeIIArithmetic U V = vaughanLambdaHigh V := by
  rw [vaughanTypeIArithmetic_eq, vaughanTypeIIArithmetic]
  calc
    vaughanLambdaHigh V * (vaughanMuLow U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) +
        vaughanLambdaHigh V *
          (vaughanMuHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) =
        vaughanLambdaHigh V *
          ((vaughanMuLow U + vaughanMuHigh U) *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) := by ring
    _ = vaughanLambdaHigh V *
          ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) := by
          rw [vaughanMuLow_add_high]
    _ = vaughanLambdaHigh V := by simp

/-- Finite Vaughan identity for the von Mangoldt function.

The form used here is the three-piece grouped identity
`Λ = Λ_{≤V} + μ_{≤U} * (log - ζ * Λ_{≤V}) + Λ_{>V} * (μ_{>U} * ζ)`.
The first summand is the small direct contribution, the middle summand is
the Type-I truncation, and the final summand is the Type-II tail. -/
theorem vaughan_identity_finite
    (U V : ℕ) (_hU : 0 < U) (_hV : 0 < V) (n : ℕ) (_hn : 0 < n) :
    ArithmeticFunction.vonMangoldt n =
      vaughanLambdaLow V n + vaughanTypeIArithmetic U V n + vaughanTypeIIArithmetic U V n := by
  have hmain :
      ArithmeticFunction.vonMangoldt =
        vaughanLambdaLow V + vaughanTypeIArithmetic U V + vaughanTypeIIArithmetic U V := by
    calc
      ArithmeticFunction.vonMangoldt = vaughanLambdaLow V + vaughanLambdaHigh V := by
        rw [← vaughanLambdaLow_add_high]
      _ = vaughanLambdaLow V + (vaughanTypeIArithmetic U V + vaughanTypeIIArithmetic U V) := by
        rw [vaughanTypeI_add_typeII]
      _ = vaughanLambdaLow V + vaughanTypeIArithmetic U V + vaughanTypeIIArithmetic U V := by ring
  exact congr_arg (fun f : ArithmeticFunction ℝ => f n) hmain

/-! ## Finite Type I/II sums -/

/-- A Type I sum, schematically `∑_m a_m ∑_n e(αmn)`. -/
noncomputable def typeISum (a : CoeffSeq) (M N : ℕ) (α : ℝ) : ℂ :=
  ∑ m ∈ Finset.range (M + 1), a m * ∑ n ∈ Finset.range (N + 1), addChar α (m * n)

/-- A Type II bilinear sum, schematically `∑_m∑_n a_m b_n e(αmn)`. -/
noncomputable def typeIISum (a b : CoeffSeq) (M N : ℕ) (α : ℝ) : ℂ :=
  ∑ m ∈ Finset.range (M + 1),
    ∑ n ∈ Finset.range (N + 1), a m * b n * addChar α (m * n)

/-- Exponential sum attached to a real-valued arithmetic function. -/
noncomputable def arithmeticExpSum (F : ArithmeticFunction ℝ) (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1), (F n : ℂ) * addChar α n

/-- Type-I coefficient encoder for a single arithmetic exponential sum.

The existing `typeISum` is rectangular and its inner sum includes the zero
frequency.  The coefficient at `0` cancels that zero-mode contribution, so
`typeISum (oneStepTypeICoeff F N) N 1 α` is exactly
`∑_{n≤N} F(n)e(αn)`. -/
noncomputable def oneStepTypeICoeff (F : ArithmeticFunction ℝ) (N : ℕ) : CoeffSeq :=
  fun m =>
    if m = 0 then
      -((∑ k ∈ (Finset.range (N + 1)).filter (fun k => k ≠ 0), (F k : ℂ)) / 2)
    else
      (F m : ℂ)

/-- Delta coefficient at `1`, used to embed a single arithmetic exponential
sum into the rectangular Type-II bilinear form. -/
noncomputable def deltaOneCoeff : CoeffSeq :=
  fun n => if n = 1 then 1 else 0

/-- Type-I coefficient sequence for the Vaughan Type-I arithmetic piece. -/
noncomputable def vaughanTypeICoeff (U V N : ℕ) : CoeffSeq :=
  oneStepTypeICoeff (vaughanTypeIArithmetic U V) N

/-- Inner arithmetic factor in the Type-I Vaughan convolution,
`log - ζ * Λ_{≤V}`. -/
noncomputable def vaughanTypeIInnerArithmetic (V : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.log -
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLambdaLow V

/-- Bilinear outer coefficient for the Type-I Vaughan piece.  This is just
the truncated Möbius factor; unlike `oneStepTypeICoeff`, it has no ambient
`N`-dependent zero-mode correction. -/
noncomputable def vaughanTypeIBilinearCoeff (U _V : ℕ) : CoeffSeq :=
  fun d => (vaughanMuLow U d : ℂ)

/-- Bilinear inner coefficient for the Type-I Vaughan piece. -/
noncomputable def vaughanTypeIBilinearInnerCoeff (V : ℕ) : CoeffSeq :=
  fun m => (vaughanTypeIInnerArithmetic V m : ℂ)

/-- Divisor-pair Type-I Vaughan sum.  This is the exact bilinear convolution
form `∑_{dm≤N} μ_{≤U}(d) (log - ζ*Λ_{≤V})(m) e(αdm)`, expressed through
`Nat.divisorsAntidiagonal` to avoid the rectangular encoder's zero mode. -/
noncomputable def vaughanTypeIBilinearSum (U V N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1),
    ∑ dm ∈ n.divisorsAntidiagonal,
      vaughanTypeIBilinearCoeff U V dm.1 *
        vaughanTypeIBilinearInnerCoeff V dm.2 *
        addChar α (dm.1 * dm.2)

/-- Inner arithmetic factor for the Type-II Vaughan piece: `μ_{>U} * ζ`. -/
noncomputable def vaughanTypeIIInnerArithmetic (U : ℕ) : ArithmeticFunction ℝ :=
  vaughanMuHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)

/-- Bilinear outer coefficient for the Type-II Vaughan piece: truncated von Mangoldt. -/
noncomputable def vaughanTypeIIBilinearCoeff (V : ℕ) : CoeffSeq :=
  fun d => (vaughanLambdaHigh V d : ℂ)

/-- Bilinear inner coefficient for the Type-II Vaughan piece. -/
noncomputable def vaughanTypeIIBilinearInnerCoeff (U : ℕ) : CoeffSeq :=
  fun m => (vaughanTypeIIInnerArithmetic U m : ℂ)

/-- Divisor-pair Type-II Vaughan sum. -/
noncomputable def vaughanTypeIIBilinearSum (U V N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1),
    ∑ dm ∈ n.divisorsAntidiagonal,
      vaughanTypeIIBilinearCoeff V dm.1 *
        vaughanTypeIIBilinearInnerCoeff U dm.2 *
        addChar α (dm.1 * dm.2)

/-- Left coefficient sequence for the Vaughan Type-II arithmetic piece. -/
noncomputable def vaughanTypeIICoeffLeft (U V : ℕ) : CoeffSeq :=
  fun m => (vaughanTypeIIArithmetic U V m : ℂ)

/-- Right delta coefficient sequence for the Vaughan Type-II arithmetic piece. -/
noncomputable def vaughanTypeIICoeffRight : CoeffSeq :=
  deltaOneCoeff


private lemma log_nat_succ_nonneg (m : ℕ) : 0 ≤ Real.log (m + 1 : ℝ) := by
  exact Real.log_nonneg (by exact_mod_cast Nat.succ_pos m)

private lemma vonMangoldt_le_log_succ_local (n : ℕ) :
    ArithmeticFunction.vonMangoldt n ≤ Real.log (n + 1 : ℝ) := by
  by_cases hn0 : n = 0
  · subst n
    simp [ArithmeticFunction.map_zero]
  · have hn_pos_nat : 0 < n := Nat.pos_of_ne_zero hn0
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos_nat
    have hn_le_succ : (n : ℝ) ≤ (n + 1 : ℝ) := by
      exact_mod_cast Nat.le_succ n
    exact (ArithmeticFunction.vonMangoldt_le_log (n := n)).trans
      (Real.log_le_log hn_pos hn_le_succ)

private lemma vaughanLambdaLow_abs_le_log_succ_of_le
    (V N n : ℕ) (hn : n ≤ N) :
    |vaughanLambdaLow V n| ≤ Real.log (N + 1 : ℝ) := by
  have hn_succ : (n + 1 : ℝ) ≤ (N + 1 : ℝ) := by
    exact_mod_cast Nat.succ_le_succ hn
  have hlog :
      Real.log (n + 1 : ℝ) ≤ Real.log (N + 1 : ℝ) :=
    Real.log_le_log (by exact_mod_cast Nat.succ_pos n) hn_succ
  unfold vaughanLambdaLow
  by_cases hlow : n ≤ V
  · simp only [ArithmeticFunction.coe_mk, ge_iff_le]
    exact (vonMangoldt_le_log_succ_local n).trans hlog
  · simp [hlow, log_nat_succ_nonneg N]


theorem sum_vonMangoldt_range_eq_psi (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) =
      Chebyshev.psi N := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext n
  simp [Finset.mem_range, Finset.mem_Icc]

/-- Pointwise Mertens input for the von-Mangoldt second moment:
`∑_{m≤N} Λ(m)^2 ≤ log(N+1) ∑_{m≤N} Λ(m)`. -/
theorem sum_vonMangoldt_sq_le_log_succ_sum (N : ℕ) :
    ∑ m ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt m : ℝ)^2 ≤
      Real.log (N + 1 : ℝ) *
        ∑ m ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt m : ℝ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro m hm
  have hm_le : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hm_succ_le : (m + 1 : ℝ) ≤ (N + 1 : ℝ) := by
    exact_mod_cast Nat.succ_le_succ hm_le
  have hlog_le :
      Real.log (m + 1 : ℝ) ≤ Real.log (N + 1 : ℝ) :=
    Real.log_le_log (by exact_mod_cast Nat.succ_pos m) hm_succ_le
  have hΛ_nonneg : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt m :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hΛ_le_logN :
      (ArithmeticFunction.vonMangoldt m : ℝ) ≤ Real.log (N + 1 : ℝ) :=
    (vonMangoldt_le_log_succ_local m).trans hlog_le
  calc
    (ArithmeticFunction.vonMangoldt m : ℝ)^2 =
        (ArithmeticFunction.vonMangoldt m : ℝ) *
          (ArithmeticFunction.vonMangoldt m : ℝ) := sq _
    _ ≤ Real.log (N + 1 : ℝ) * (ArithmeticFunction.vonMangoldt m : ℝ) :=
        mul_le_mul_of_nonneg_right hΛ_le_logN hΛ_nonneg

theorem sum_vonMangoldt_sq_le_log_succ_psi (N : ℕ) :
    ∑ m ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt m : ℝ)^2 ≤
      Real.log (N + 1 : ℝ) * Chebyshev.psi N := by
  simpa [sum_vonMangoldt_range_eq_psi N] using
    sum_vonMangoldt_sq_le_log_succ_sum N

/-- Chebyshev-grade `O(N log N)` control for the von-Mangoldt second moment. -/
theorem sum_vonMangoldt_sq_le_chebyshev_log_succ (N : ℕ) :
    ∑ m ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt m : ℝ)^2 ≤
      (Real.log 4 + 4) * ((N : ℝ) + 1) * Real.log (N + 1 : ℝ) := by
  have hmain := sum_vonMangoldt_sq_le_log_succ_psi N
  have hK_nonneg : 0 ≤ Real.log 4 + 4 := by
    have hlog4_nonneg : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
    linarith
  have hpsi_self : Chebyshev.psi N ≤ (Real.log 4 + 4) * (N : ℝ) :=
    Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg N)
  have hN_le_succ : (N : ℝ) ≤ (N : ℝ) + 1 := by norm_num
  have hpsi_succ :
      Chebyshev.psi N ≤ (Real.log 4 + 4) * ((N : ℝ) + 1) :=
    hpsi_self.trans (mul_le_mul_of_nonneg_left hN_le_succ hK_nonneg)
  have hlog_nonneg : 0 ≤ Real.log (N + 1 : ℝ) := log_nat_succ_nonneg N
  have hmul :
      Real.log (N + 1 : ℝ) * Chebyshev.psi N ≤
        Real.log (N + 1 : ℝ) * ((Real.log 4 + 4) * ((N : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left hpsi_succ hlog_nonneg
  exact hmain.trans (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul)


private lemma vaughanMuHigh_mul_zeta_abs_le_card_divisors (U m : ℕ) :
    |(vaughanMuHigh U *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m| ≤ (#m.divisors : ℝ) := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  calc
    |∑ d ∈ m.divisors, vaughanMuHigh U d| ≤
        ∑ d ∈ m.divisors, |vaughanMuHigh U d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ m.divisors, (1 : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro d _hd
      unfold vaughanMuHigh
      by_cases h : U < d
      · simp only [ArithmeticFunction.coe_mk]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      · simp [h]
    _ = (#m.divisors : ℝ) := by simp

private lemma vaughanMuHigh_mul_zeta_abs_le_self (U m : ℕ) :
    |(vaughanMuHigh U *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m| ≤ (m : ℝ) := by
  exact (vaughanMuHigh_mul_zeta_abs_le_card_divisors U m).trans
    (by exact_mod_cast Nat.card_divisors_le_self m)

private lemma vaughanLambdaHigh_abs_le_log_succ (V m : ℕ) {d : ℕ}
    (hd : d ∈ m.divisors) : |vaughanLambdaHigh V d| ≤ Real.log (m + 1 : ℝ) := by
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdle : d ≤ m := Nat.divisor_le hd
  have hdle_succ : (d : ℝ) ≤ (m + 1 : ℝ) := by
    exact_mod_cast (le_trans hdle (Nat.le_succ m))
  have hlog_le : Real.log (d : ℝ) ≤ Real.log (m + 1 : ℝ) := by
    exact Real.log_le_log (by exact_mod_cast hdpos) hdle_succ
  unfold vaughanLambdaHigh
  by_cases h : V < d
  · simp only [ArithmeticFunction.coe_mk, ge_iff_le]
    exact (ArithmeticFunction.vonMangoldt_le_log (n := d)).trans hlog_le
  · simp [h, log_nat_succ_nonneg m]

private lemma card_divisors_le_succ_of_mem_antidiagonal {m : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ m.divisorsAntidiagonal) : (#x.2.divisors : ℝ) ≤ (m + 1 : ℝ) := by
  have hx2div : x.2 ∈ m.divisors := Nat.snd_mem_divisors_of_mem_antidiagonal hx
  have hx2le : x.2 ≤ m := Nat.divisor_le hx2div
  have hcard : #x.2.divisors ≤ m + 1 :=
    (Nat.card_divisors_le_self x.2).trans (le_trans hx2le (Nat.le_succ m))
  exact_mod_cast hcard

private lemma card_divisorsAntidiagonal_le_succ (m : ℕ) :
    (#m.divisorsAntidiagonal : ℝ) ≤ (m + 1 : ℝ) := by
  have hcard : #m.divisorsAntidiagonal ≤ m + 1 := by
    rw [← Nat.map_div_right_divisors]
    simp only [Finset.card_map]
    exact (Nat.card_divisors_le_self m).trans (Nat.le_succ m)
  exact_mod_cast hcard

private lemma card_divisorsAntidiagonal_le_two_nat_sqrt (m : ℕ) :
    #m.divisorsAntidiagonal ≤ 2 * Nat.sqrt m := by
  classical
  have hleft :
      #(m.divisorsAntidiagonal.filter (fun x : ℕ × ℕ => x.1 ≤ x.2)) ≤ Nat.sqrt m := by
    refine (Finset.card_le_card_of_injOn Prod.fst
      (t := Finset.Icc 1 (Nat.sqrt m)) ?_ ?_).trans ?_
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter] at hx
      simp only [Finset.mem_coe, Finset.mem_Icc]
      have hxmem : x ∈ m.divisorsAntidiagonal := hx.1
      have hle : x.1 ≤ x.2 := hx.2
      have hprod : x.1 * x.2 = m := (Nat.mem_divisorsAntidiagonal.mp hxmem).1
      have hxne : x.1 ≠ 0 := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hxmem
      constructor
      · exact Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hxne)
      · rw [Nat.le_sqrt]
        exact (Nat.mul_le_mul_left x.1 hle).trans_eq hprod
    · intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_filter] at hx hy
      have hxmem : x ∈ m.divisorsAntidiagonal := hx.1
      have hymem : y ∈ m.divisorsAntidiagonal := hy.1
      have hxprod : x.1 * x.2 = m := (Nat.mem_divisorsAntidiagonal.mp hxmem).1
      have hyprod : y.1 * y.2 = m := (Nat.mem_divisorsAntidiagonal.mp hymem).1
      have hxpos : 0 < x.1 :=
        Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hxmem)
      apply Prod.ext hxy
      apply Nat.mul_left_cancel hxpos
      calc
        x.1 * x.2 = m := hxprod
        _ = y.1 * y.2 := hyprod.symm
        _ = x.1 * y.2 := by rw [hxy]
    · rw [Nat.card_Icc]
      omega
  have hright :
      #(m.divisorsAntidiagonal.filter (fun x : ℕ × ℕ => ¬ x.1 ≤ x.2)) ≤
        Nat.sqrt m := by
    refine (Finset.card_le_card_of_injOn Prod.snd
      (t := Finset.Icc 1 (Nat.sqrt m)) ?_ ?_).trans ?_
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter] at hx
      simp only [Finset.mem_coe, Finset.mem_Icc]
      have hxmem : x ∈ m.divisorsAntidiagonal := hx.1
      have hlt : x.2 < x.1 := lt_of_not_ge hx.2
      have hprod : x.1 * x.2 = m := (Nat.mem_divisorsAntidiagonal.mp hxmem).1
      have hxne : x.2 ≠ 0 := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hxmem
      constructor
      · exact Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hxne)
      · rw [Nat.le_sqrt]
        exact (Nat.mul_le_mul_right x.2 (le_of_lt hlt)).trans_eq (by rw [hprod])
    · intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_filter] at hx hy
      have hxmem : x ∈ m.divisorsAntidiagonal := hx.1
      have hymem : y ∈ m.divisorsAntidiagonal := hy.1
      have hxprod : x.1 * x.2 = m := (Nat.mem_divisorsAntidiagonal.mp hxmem).1
      have hyprod : y.1 * y.2 = m := (Nat.mem_divisorsAntidiagonal.mp hymem).1
      have hxpos : 0 < x.2 :=
        Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hxmem)
      apply Prod.ext ?_ hxy
      apply Nat.mul_left_cancel hxpos
      calc
        x.2 * x.1 = x.1 * x.2 := by rw [mul_comm]
        _ = m := hxprod
        _ = y.1 * y.2 := hyprod.symm
        _ = x.2 * y.1 := by rw [← hxy, mul_comm]
    · rw [Nat.card_Icc]
      omega
  calc
    #m.divisorsAntidiagonal =
        #(m.divisorsAntidiagonal.filter (fun x : ℕ × ℕ => x.1 ≤ x.2)) +
          #(m.divisorsAntidiagonal.filter (fun x : ℕ × ℕ => ¬ x.1 ≤ x.2)) := by
      rw [Finset.card_filter_add_card_filter_not]
    _ ≤ Nat.sqrt m + Nat.sqrt m := Nat.add_le_add hleft hright
    _ = 2 * Nat.sqrt m := by omega

private lemma card_divisorsAntidiagonal_le_two_real_sqrt_succ (m : ℕ) :
    (#m.divisorsAntidiagonal : ℝ) ≤ 2 * Real.sqrt (m + 1 : ℝ) := by
  have hcard := card_divisorsAntidiagonal_le_two_nat_sqrt m
  have hsqrtn :
      (Nat.sqrt m : ℝ) ≤ Real.sqrt (m + 1 : ℝ) := by
    have hmle : (m : ℝ) ≤ (m + 1 : ℝ) := by exact_mod_cast Nat.le_succ m
    exact Real.nat_sqrt_le_real_sqrt.trans (Real.sqrt_le_sqrt hmle)
  calc
    (#m.divisorsAntidiagonal : ℝ) ≤ (2 * Nat.sqrt m : ℕ) := by exact_mod_cast hcard
    _ = 2 * (Nat.sqrt m : ℝ) := by norm_num
    _ ≤ 2 * Real.sqrt (m + 1 : ℝ) :=
      mul_le_mul_of_nonneg_left hsqrtn (by norm_num)

private lemma card_divisors_le_two_real_sqrt_succ (m : ℕ) :
    (#m.divisors : ℝ) ≤ 2 * Real.sqrt (m + 1 : ℝ) := by
  have hcard : #m.divisors = #m.divisorsAntidiagonal := by
    rw [← Nat.map_div_right_divisors]
    simp
  calc
    (#m.divisors : ℝ) = (#m.divisorsAntidiagonal : ℝ) := by exact_mod_cast hcard
    _ ≤ 2 * Real.sqrt (m + 1 : ℝ) := card_divisorsAntidiagonal_le_two_real_sqrt_succ m

private lemma card_divisors_sq_le_four_succ (m : ℕ) :
    (#m.divisors : ℝ) ^ 2 ≤ 4 * (m + 1 : ℝ) := by
  have hcard := card_divisors_le_two_real_sqrt_succ m
  calc
    (#m.divisors : ℝ) ^ 2 ≤ (2 * Real.sqrt (m + 1 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hcard 2
    _ = 4 * (m + 1 : ℝ) := by
      have hm : 0 ≤ (m + 1 : ℝ) := by positivity
      rw [mul_pow, Real.sq_sqrt hm]
      ring


private theorem sum_card_divisors_sq_eq_sum_lcm_floor_nat (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1), (#m.divisors) ^ 2) =
      ∑ d ∈ Finset.range (N + 1), ∑ e ∈ Finset.range (N + 1),
        N / Nat.lcm d e := by
  classical
  let source : Finset (Sigma fun _m : ℕ => ℕ × ℕ) :=
    (Finset.range (N + 1)).sigma fun m => m.divisors.product m.divisors
  let target : Finset (Sigma fun _de : ℕ × ℕ => ℕ) :=
    ((Finset.range (N + 1)).product (Finset.range (N + 1))).sigma fun de =>
      (Finset.range (N + 1)).filter fun m => m ≠ 0 ∧ Nat.lcm de.1 de.2 ∣ m
  have hcard : #source = #target := by
    refine Finset.card_bij
      (fun x _hx => ⟨(x.2.1, x.2.2), x.1⟩) ?_ ?_ ?_
    · intro x hx
      rcases x with ⟨m, de⟩
      rcases de with ⟨d, e⟩
      simp only [source, target, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter,
        Nat.lt_succ_iff] at hx ⊢
      rcases hx with ⟨hmN, hdemem⟩
      rcases Finset.mem_product.mp hdemem with ⟨hdmem, hemem⟩
      have hmne : m ≠ 0 := Nat.ne_zero_of_mem_divisors hdmem
      have hdle : d ≤ N := (Nat.divisor_le hdmem).trans hmN
      have hele : e ≤ N := (Nat.divisor_le hemem).trans hmN
      have hdlcm : Nat.lcm d e ∣ m :=
        lcm_dvd (Nat.dvd_of_mem_divisors hdmem) (Nat.dvd_of_mem_divisors hemem)
      exact ⟨Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hdle),
            Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hele)⟩,
        hmN, hmne, hdlcm⟩
    · intro x₁ _hx₁ x₂ _hx₂ hmap
      rcases x₁ with ⟨m₁, de₁⟩
      rcases x₂ with ⟨m₂, de₂⟩
      rcases de₁ with ⟨d₁, e₁⟩
      rcases de₂ with ⟨d₂, e₂⟩
      simp only at hmap
      cases hmap
      rfl
    · intro y hy
      rcases y with ⟨de, m⟩
      rcases de with ⟨d, e⟩
      simp only [target, source, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter,
        Nat.lt_succ_iff] at hy ⊢
      rcases hy with ⟨hdeN, hmN, hmne, hlcm⟩
      rcases Finset.mem_product.mp hdeN with ⟨_hdN, _heN⟩
      have hdm : d ∣ m := (dvd_lcm_left d e).trans hlcm
      have hem : e ∣ m := (dvd_lcm_right d e).trans hlcm
      refine ⟨⟨m, (d, e)⟩, ?_, rfl⟩
      exact ⟨hmN, Finset.mem_product.mpr
        ⟨Nat.mem_divisors.mpr ⟨hdm, hmne⟩,
          Nat.mem_divisors.mpr ⟨hem, hmne⟩⟩⟩
  calc
    (∑ m ∈ Finset.range (N + 1), (#m.divisors) ^ 2) = #source := by
      simp [source, Finset.card_product, pow_two]
    _ = #target := hcard
    _ = ∑ de ∈ (Finset.range (N + 1)).product (Finset.range (N + 1)),
          N / Nat.lcm de.1 de.2 := by
      simp [target, Nat.card_multiples']
    _ = ∑ d ∈ Finset.range (N + 1), ∑ e ∈ Finset.range (N + 1),
          N / Nat.lcm d e := by
      simpa using
        (Finset.sum_product' (Finset.range (N + 1)) (Finset.range (N + 1))
          (fun d e => N / Nat.lcm d e))

/-- Divisor-pair inversion for the second moment of the divisor-counting
function.  A pair `(d, e)` contributes once for every nonzero multiple of
`lcm d e` up to `N`; Mathlib's `Nat.card_multiples'` evaluates that count as
`N / lcm d e`. -/
theorem sum_card_divisors_sq_eq_sum_lcm_inv_floor (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1), (#m.divisors : ℝ) ^ 2) =
      ∑ d ∈ Finset.range (N + 1), ∑ e ∈ Finset.range (N + 1),
        ((N / Nat.lcm d e : ℕ) : ℝ) := by
  exact_mod_cast sum_card_divisors_sq_eq_sum_lcm_floor_nat N

/-- A lcm-floor term is bounded by the corresponding real reciprocal term.
For zero lcms both sides use the Lean convention `x / 0 = 0`. -/
theorem lcm_floor_le_real_inv (N d e : ℕ) :
    ((N / Nat.lcm d e : ℕ) : ℝ) ≤ (N : ℝ) / (Nat.lcm d e : ℝ) := by
  exact Nat.cast_div_le

/-- For positive indices, the reciprocal lcm kernel is the usual
`gcd(d,e)/(d*e)` kernel. -/
theorem real_div_lcm_eq_mul_gcd_div (N d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    (N : ℝ) / (Nat.lcm d e : ℝ) =
      (N : ℝ) * (Nat.gcd d e : ℝ) / ((d : ℝ) * (e : ℝ)) := by
  have hlcm_ne : (Nat.lcm d e : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.lcm_pos hd he).ne'
  have hgcd_lcm :
      (Nat.gcd d e : ℝ) * (Nat.lcm d e : ℝ) = (d : ℝ) * (e : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm d e
  calc
    (N : ℝ) / (Nat.lcm d e : ℝ) =
        (N : ℝ) * ((Nat.gcd d e : ℝ) * (Nat.lcm d e : ℝ)) /
          (((d : ℝ) * (e : ℝ)) * (Nat.lcm d e : ℝ)) := by
      rw [hgcd_lcm]
      field_simp [hlcm_ne]
    _ = (N : ℝ) * (Nat.gcd d e : ℝ) / ((d : ℝ) * (e : ℝ)) := by
      field_simp [hlcm_ne]

/-- The gcd is bounded by the sum of all common divisors. -/
theorem gcd_le_sum_common_divisors (d e : ℕ) (hd : 0 < d) :
    (Nat.gcd d e : ℝ) ≤ ∑ g ∈ d.divisors.filter (fun g => g ∣ e), (g : ℝ) := by
  have hmem : Nat.gcd d e ∈ d.divisors.filter (fun g => g ∣ e) := by
    rw [Finset.mem_filter]
    exact ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left d e, hd.ne'⟩, Nat.gcd_dvd_right d e⟩
  exact Finset.single_le_sum (fun g _hg => Nat.cast_nonneg g) hmem

/-- Positive lcm reciprocal majorized by summing over common divisors.  This is
the algebraic inequality behind the `N log^3 N` estimate after swapping the
finite sums. -/
theorem real_div_lcm_le_common_divisor_sum (N d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    (N : ℝ) / (Nat.lcm d e : ℝ) ≤
      ∑ g ∈ d.divisors.filter (fun g => g ∣ e),
        ((N : ℝ) * (g : ℝ)) / ((d : ℝ) * (e : ℝ)) := by
  have hgcd := gcd_le_sum_common_divisors d e hd
  have hsum_eq :
      (∑ g ∈ d.divisors.filter (fun g => g ∣ e),
        ((N : ℝ) * (g : ℝ)) / ((d : ℝ) * (e : ℝ))) =
        ((N : ℝ) / ((d : ℝ) * (e : ℝ))) *
          ∑ g ∈ d.divisors.filter (fun g => g ∣ e), (g : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro g _hg
    ring
  calc
    (N : ℝ) / (Nat.lcm d e : ℝ) =
        (N : ℝ) * (Nat.gcd d e : ℝ) / ((d : ℝ) * (e : ℝ)) :=
      real_div_lcm_eq_mul_gcd_div N d e hd he
    _ = ((N : ℝ) / ((d : ℝ) * (e : ℝ))) * (Nat.gcd d e : ℝ) := by ring
    _ ≤ ((N : ℝ) / ((d : ℝ) * (e : ℝ))) *
          ∑ g ∈ d.divisors.filter (fun g => g ∣ e), (g : ℝ) :=
      mul_le_mul_of_nonneg_left hgcd (by positivity)
    _ = ∑ g ∈ d.divisors.filter (fun g => g ∣ e),
        ((N : ℝ) * (g : ℝ)) / ((d : ℝ) * (e : ℝ)) := hsum_eq.symm

/-- Double lcm reciprocal sum over positive indices bounded by the common-divisor
majorant.  The next step is to swap the three finite sums and evaluate the
filtered harmonic sums over multiples of `g`. -/
theorem sum_lcm_reciprocal_Icc_le_common_divisor_sum (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        (N : ℝ) / (Nat.lcm d e : ℝ)) ≤
      ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        ∑ g ∈ d.divisors.filter (fun g => g ∣ e),
          ((N : ℝ) * (g : ℝ)) / ((d : ℝ) * (e : ℝ)) := by
  refine Finset.sum_le_sum ?_
  intro d hdmem
  have hd : 0 < d := (Finset.mem_Icc.mp hdmem).1
  refine Finset.sum_le_sum ?_
  intro e hemel
  have he : 0 < e := (Finset.mem_Icc.mp hemel).1
  exact real_div_lcm_le_common_divisor_sum N d e hd he


/-- First analytic reduction after the divisor-pair lcm identity: replace each
integer floor term by a real reciprocal lcm term. -/
theorem sum_lcm_inv_floor_le_real_lcm_inv (N : ℕ) :
    (∑ d ∈ Finset.range (N + 1), ∑ e ∈ Finset.range (N + 1),
        ((N / Nat.lcm d e : ℕ) : ℝ)) ≤
      ∑ d ∈ Finset.range (N + 1), ∑ e ∈ Finset.range (N + 1),
        (N : ℝ) / (Nat.lcm d e : ℝ) := by
  refine Finset.sum_le_sum ?_
  intro d _hd
  refine Finset.sum_le_sum ?_
  intro e _he
  exact lcm_floor_le_real_inv N d e

/-- Step 56's structural identity followed by the floor-to-reciprocal
analytic reduction.  The remaining work is the gcd/common-divisor harmonic
majorization of the double reciprocal lcm sum. -/
theorem sum_card_divisors_sq_le_lcm_reciprocal_sum (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1), (#m.divisors : ℝ) ^ 2) ≤
      ∑ d ∈ Finset.range (N + 1), ∑ e ∈ Finset.range (N + 1),
        (N : ℝ) / (Nat.lcm d e : ℝ) := by
  rw [sum_card_divisors_sq_eq_sum_lcm_inv_floor]
  exact sum_lcm_inv_floor_le_real_lcm_inv N


private lemma multiple_reciprocal_term_eq
    {d g : ℕ} (hg : 0 < g) (hdvd : g ∣ d) :
    (g : ℝ) / (d : ℝ) = 1 / ((d / g : ℕ) : ℝ) := by
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hcast : ((d / g : ℕ) : ℝ) = (d : ℝ) / (g : ℝ) := by
    exact Nat.cast_div hdvd hg0
  rw [hcast]
  field_simp [hg0]

private lemma sum_Icc_dvd_div_le_harmonic (N g : ℕ) (hg : 0 < g) :
    (∑ d ∈ Finset.Icc 1 N, if g ∣ d then (g : ℝ) / (d : ℝ) else 0) ≤
      ∑ k ∈ Finset.Icc 1 N, (1 / (k : ℝ)) := by
  let S := (Finset.Icc 1 N).filter (fun d => g ∣ d)
  let T := S.image (fun d => d / g)
  have hinj : Set.InjOn (fun d => d / g) (S : Set ℕ) := by
    intro a ha b hb hdiv
    have hadvd : g ∣ a := (Finset.mem_filter.mp ha).2
    have hbdvd : g ∣ b := (Finset.mem_filter.mp hb).2
    exact (Nat.div_left_inj hadvd hbdvd).mp hdiv
  have hTsubset : T ⊆ Finset.Icc 1 N := by
    intro k hk
    rw [Finset.mem_image] at hk
    rcases hk with ⟨d, hdS, rfl⟩
    rw [Finset.mem_Icc]
    have hdI := (Finset.mem_filter.mp hdS).1
    have hdvd := (Finset.mem_filter.mp hdS).2
    have hdpos : 0 < d := Nat.succ_le_iff.mp (Finset.mem_Icc.mp hdI).1
    exact ⟨Nat.succ_le_iff.mpr (Nat.div_pos (Nat.le_of_dvd hdpos hdvd) hg),
      (Nat.div_le_self d g).trans (Finset.mem_Icc.mp hdI).2⟩
  have hsum_filter :
      (∑ d ∈ Finset.Icc 1 N, if g ∣ d then (g : ℝ) / (d : ℝ) else 0) =
        ∑ d ∈ S, (g : ℝ) / (d : ℝ) := by
    dsimp [S]
    rw [Finset.sum_filter]
  have hsum_image :
      ∑ k ∈ T, (1 / (k : ℝ)) = ∑ d ∈ S, (1 / ((d / g : ℕ) : ℝ)) := by
    dsimp [T]
    exact Finset.sum_image hinj
  calc
    (∑ d ∈ Finset.Icc 1 N, if g ∣ d then (g : ℝ) / (d : ℝ) else 0)
        = ∑ d ∈ S, (g : ℝ) / (d : ℝ) := hsum_filter
    _ = ∑ d ∈ S, (1 / ((d / g : ℕ) : ℝ)) := by
      refine Finset.sum_congr rfl ?_
      intro d hdS
      exact multiple_reciprocal_term_eq hg (Finset.mem_filter.mp hdS).2
    _ = ∑ k ∈ T, (1 / (k : ℝ)) := hsum_image.symm
    _ ≤ ∑ k ∈ Finset.Icc 1 N, (1 / (k : ℝ)) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hTsubset ?_
      intro k _hkI _hknot
      positivity

private lemma common_divisor_kernel_factor
    (N d e g : ℕ) (hg : 0 < g) (hd : 0 < d) (he : 0 < e) :
    (if g ∣ d ∧ g ∣ e then
        ((N : ℝ) * (g : ℝ)) / ((d : ℝ) * (e : ℝ)) else 0) =
      ((N : ℝ) / (g : ℝ)) *
        (if g ∣ d then (g : ℝ) / (d : ℝ) else 0) *
        (if g ∣ e then (g : ℝ) / (e : ℝ) else 0) := by
  by_cases hdvd : g ∣ d
  · by_cases hevd : g ∣ e
    · simp [hdvd, hevd]
      have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
      have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
      field_simp [hg0, hd0, he0]
    · simp [hdvd, hevd]
  · simp [hdvd]

private lemma common_divisor_kernel_factor_sum (N g : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
      ((N : ℝ) / (g : ℝ)) *
        (if g ∣ d then (g : ℝ) / (d : ℝ) else 0) *
        (if g ∣ e then (g : ℝ) / (e : ℝ) else 0)) =
      ((N : ℝ) / (g : ℝ)) *
        (∑ d ∈ Finset.Icc 1 N, if g ∣ d then (g : ℝ) / (d : ℝ) else 0) *
        (∑ e ∈ Finset.Icc 1 N, if g ∣ e then (g : ℝ) / (e : ℝ) else 0) := by
  let S := Finset.Icc 1 N
  let C : ℝ := (N : ℝ) / (g : ℝ)
  let A : ℕ → ℝ := fun d => if g ∣ d then (g : ℝ) / (d : ℝ) else 0
  change (∑ d ∈ S, ∑ e ∈ S, C * A d * A e) =
      C * (∑ d ∈ S, A d) * (∑ e ∈ S, A e)
  calc
    (∑ d ∈ S, ∑ e ∈ S, C * A d * A e)
        = ∑ d ∈ S, (C * A d) * ∑ e ∈ S, A e := by
      refine Finset.sum_congr rfl ?_
      intro d _hd
      exact (Finset.mul_sum S A (C * A d)).symm
    _ = (∑ d ∈ S, C * A d) * ∑ e ∈ S, A e := by
      exact (Finset.sum_mul S (fun d => C * A d) (∑ e ∈ S, A e)).symm
    _ = (C * ∑ d ∈ S, A d) * ∑ e ∈ S, A e := by
      exact congrArg (fun x : ℝ => x * ∑ e ∈ S, A e) (Finset.mul_sum S A C).symm
    _ = C * (∑ d ∈ S, A d) * (∑ e ∈ S, A e) := by ring

private lemma common_divisor_fixed_g_le_harmonic_sq (N g : ℕ) (hg : 0 < g) :
    (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
      if g ∣ d ∧ g ∣ e then
        ((N : ℝ) * (g : ℝ)) / ((d : ℝ) * (e : ℝ)) else 0) ≤
      ((N : ℝ) / (g : ℝ)) *
        (∑ k ∈ Finset.Icc 1 N, (1 / (k : ℝ))) ^ 2 := by
  let H : ℝ := ∑ k ∈ Finset.Icc 1 N, (1 / (k : ℝ))
  let A : ℝ := ∑ d ∈ Finset.Icc 1 N, if g ∣ d then (g : ℝ) / (d : ℝ) else 0
  have hpoint :
      (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        if g ∣ d ∧ g ∣ e then
          ((N : ℝ) * (g : ℝ)) / ((d : ℝ) * (e : ℝ)) else 0) =
        ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
          ((N : ℝ) / (g : ℝ)) *
            (if g ∣ d then (g : ℝ) / (d : ℝ) else 0) *
            (if g ∣ e then (g : ℝ) / (e : ℝ) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro d hdI
    refine Finset.sum_congr rfl ?_
    intro e heI
    exact common_divisor_kernel_factor N d e g hg
      (Nat.succ_le_iff.mp (Finset.mem_Icc.mp hdI).1)
      (Nat.succ_le_iff.mp (Finset.mem_Icc.mp heI).1)
  have hfactor := common_divisor_kernel_factor_sum N g
  have hAle : A ≤ H := by
    dsimp [A, H]
    exact sum_Icc_dvd_div_le_harmonic N g hg
  have hAnonneg : 0 ≤ A := by
    dsimp [A]
    refine Finset.sum_nonneg ?_
    intro d _hd
    by_cases hdvd : g ∣ d
    · simp [hdvd]
      positivity
    · simp [hdvd]
  have hHnonneg : 0 ≤ H := hAnonneg.trans hAle
  have hCnonneg : 0 ≤ (N : ℝ) / (g : ℝ) := by positivity
  calc
    (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
      if g ∣ d ∧ g ∣ e then
        ((N : ℝ) * (g : ℝ)) / ((d : ℝ) * (e : ℝ)) else 0)
        = ((N : ℝ) / (g : ℝ)) * A * A := by
      rw [hpoint, hfactor]
    _ ≤ ((N : ℝ) / (g : ℝ)) * H * H := by
      have hmul :=
        mul_le_mul_of_nonneg_left (mul_le_mul hAle hAle hAnonneg hHnonneg) hCnonneg
      simpa [mul_assoc] using hmul
    _ = ((N : ℝ) / (g : ℝ)) * H ^ 2 := by ring

private lemma common_divisor_sum_Icc_le_harmonic_cube (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        ∑ g ∈ d.divisors.filter (fun g => g ∣ e),
          ((N : ℝ) * (g : ℝ)) / ((d : ℝ) * (e : ℝ))) ≤
      (N : ℝ) * (∑ k ∈ Finset.Icc 1 N, (1 / (k : ℝ))) ^ 3 := by
  let H : ℝ := ∑ k ∈ Finset.Icc 1 N, (1 / (k : ℝ))
  have hmajor :
      (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
          ∑ g ∈ d.divisors.filter (fun g => g ∣ e),
            ((N : ℝ) * (g : ℝ)) / ((d : ℝ) * (e : ℝ))) ≤
        ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
          ∑ g ∈ (Finset.Icc 1 N).filter (fun g => g ∣ d ∧ g ∣ e),
            ((N : ℝ) * (g : ℝ)) / ((d : ℝ) * (e : ℝ)) := by
    refine Finset.sum_le_sum ?_
    intro d hdI
    refine Finset.sum_le_sum ?_
    intro e _heI
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro g hgde
      rw [Finset.mem_filter]
      rw [Finset.mem_filter] at hgde
      have hgdiv := hgde.1
      have hge := hgde.2
      have hgd : g ∣ d := Nat.dvd_of_mem_divisors hgdiv
      have hgpos : 0 < g := Nat.pos_of_mem_divisors hgdiv
      have hgle : g ≤ d := Nat.le_of_dvd
        (Nat.succ_le_iff.mp (Finset.mem_Icc.mp hdI).1) hgd
      exact ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr hgpos,
        hgle.trans (Finset.mem_Icc.mp hdI).2⟩, hgd, hge⟩
    · intro g hgI _hgnot
      positivity
  have hswap :
      (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
          ∑ g ∈ (Finset.Icc 1 N).filter (fun g => g ∣ d ∧ g ∣ e),
            ((N : ℝ) * (g : ℝ)) / ((d : ℝ) * (e : ℝ))) =
        ∑ g ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
          if g ∣ d ∧ g ∣ e then
            ((N : ℝ) * (g : ℝ)) / ((d : ℝ) * (e : ℝ)) else 0 := by
    simp only [Finset.sum_filter]
    calc
      (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, ∑ g ∈ Finset.Icc 1 N,
          if g ∣ d ∧ g ∣ e then
            ((N : ℝ) * (g : ℝ)) / ((d : ℝ) * (e : ℝ)) else 0) =
          ∑ d ∈ Finset.Icc 1 N, ∑ g ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
            if g ∣ d ∧ g ∣ e then
              ((N : ℝ) * (g : ℝ)) / ((d : ℝ) * (e : ℝ)) else 0 := by
        refine Finset.sum_congr rfl ?_
        intro d _hd
        rw [Finset.sum_comm]
      _ = ∑ g ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
          if g ∣ d ∧ g ∣ e then
            ((N : ℝ) * (g : ℝ)) / ((d : ℝ) * (e : ℝ)) else 0 := by
        rw [Finset.sum_comm]
  have hfixed :
      (∑ g ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
          if g ∣ d ∧ g ∣ e then
            ((N : ℝ) * (g : ℝ)) / ((d : ℝ) * (e : ℝ)) else 0) ≤
        ∑ g ∈ Finset.Icc 1 N, ((N : ℝ) / (g : ℝ)) * H ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro g hgI
    dsimp [H]
    exact common_divisor_fixed_g_le_harmonic_sq N g
      (Nat.succ_le_iff.mp (Finset.mem_Icc.mp hgI).1)
  have houter :
      (∑ g ∈ Finset.Icc 1 N, ((N : ℝ) / (g : ℝ)) * H ^ 2) =
        (N : ℝ) * H ^ 3 := by
    calc
      (∑ g ∈ Finset.Icc 1 N, ((N : ℝ) / (g : ℝ)) * H ^ 2)
          = ∑ g ∈ Finset.Icc 1 N, ((N : ℝ) * H ^ 2) * (1 / (g : ℝ)) := by
        refine Finset.sum_congr rfl ?_
        intro g _hg
        ring
      _ = ((N : ℝ) * H ^ 2) * ∑ g ∈ Finset.Icc 1 N, (1 / (g : ℝ)) := by
        exact (Finset.mul_sum (Finset.Icc 1 N) (fun g => (1 / (g : ℝ)))
          ((N : ℝ) * H ^ 2)).symm
      _ = (N : ℝ) * H ^ 3 := by
        dsimp [H]
        ring
  exact hmajor.trans (by rw [hswap]; exact hfixed.trans_eq houter)

private lemma lcm_reciprocal_range_eq_Icc (N : ℕ) :
    (∑ d ∈ Finset.range (N + 1), ∑ e ∈ Finset.range (N + 1),
        (N : ℝ) / (Nat.lcm d e : ℝ)) =
      ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        (N : ℝ) / (Nat.lcm d e : ℝ) := by
  let S := Finset.range (N + 1)
  have hfilter : S.filter (fun d => d ≠ 0) = Finset.Icc 1 N := by
    ext d
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, Nat.lt_succ_iff]
    constructor
    · intro hd
      exact ⟨Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hd.2), hd.1⟩
    · intro hd
      exact ⟨hd.2, (Nat.succ_le_iff.mp hd.1).ne'⟩
  have hinner (d : ℕ) :
      (∑ e ∈ S, (N : ℝ) / (Nat.lcm d e : ℝ)) =
        ∑ e ∈ Finset.Icc 1 N, (N : ℝ) / (Nat.lcm d e : ℝ) := by
    rw [← hfilter]
    symm
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro e _he
    by_cases he0 : e = 0
    · simp [he0, Nat.lcm_zero_right]
    · simp [he0]
  rw [← hfilter]
  symm
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro d _hd
  by_cases hd0 : d = 0
  · simp [hd0, Nat.lcm_zero_left]
  · rw [hfilter]
    simp only [ne_eq, ite_not]
    exact (hinner d).symm

private lemma harmonic_sum_le_log_succ_early (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, (1 / (k : ℝ))) ≤
      1 + Real.log ((N : ℝ) + 1) := by
  have hcast :
      (∑ k ∈ Finset.Icc 1 N, (1 / (k : ℝ))) = (harmonic N : ℝ) := by
    have h := congr_arg (fun x : ℚ => (x : ℝ)) (harmonic_eq_sum_Icc (n := N))
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
    simpa [one_div] using h.symm
  by_cases hN : N = 0
  · simp [hN]
  · have hNpos_nat : 0 < N := Nat.pos_of_ne_zero hN
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNpos_nat
    have hlog :
        Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 1) := by
      exact Real.log_le_log hNpos (by linarith)
    calc
      (∑ k ∈ Finset.Icc 1 N, (1 / (k : ℝ))) = (harmonic N : ℝ) := hcast
      _ ≤ 1 + Real.log (N : ℝ) := harmonic_le_one_add_log N
      _ ≤ 1 + Real.log ((N : ℝ) + 1) := by linarith

/-- Mertens-grade second-moment bound for the divisor-counting function.  The
constant is deliberately loose; the proof uses the lcm/gcd common-divisor
majorant and three finite harmonic estimates. -/
theorem sum_card_divisors_sq_le_mertens_log_cube (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1), (#m.divisors : ℝ) ^ 2) ≤
      8 * ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) ^ 3 := by
  let H : ℝ := ∑ k ∈ Finset.Icc 1 N, (1 / (k : ℝ))
  let L : ℝ := 1 + Real.log ((N : ℝ) + 1)
  have hHnonneg : 0 ≤ H := by
    dsimp [H]
    refine Finset.sum_nonneg ?_
    intro k _hk
    positivity
  have hHleL : H ≤ L := by
    dsimp [H, L]
    exact harmonic_sum_le_log_succ_early N
  have hLnonneg : 0 ≤ L := hHnonneg.trans hHleL
  have hcube :
      (N : ℝ) * H ^ 3 ≤ 8 * ((N : ℝ) + 1) * L ^ 3 := by
    have hN : (N : ℝ) ≤ (8 : ℝ) * ((N : ℝ) + 1) := by
      have hNnonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      nlinarith
    have hpow : H ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ hHnonneg hHleL 3
    have hRnonneg : 0 ≤ (8 : ℝ) * ((N : ℝ) + 1) := by positivity
    have hmul := mul_le_mul hN hpow (pow_nonneg hHnonneg 3) hRnonneg
    simpa [mul_assoc] using hmul
  calc
    (∑ m ∈ Finset.range (N + 1), (#m.divisors : ℝ) ^ 2)
        ≤ ∑ d ∈ Finset.range (N + 1), ∑ e ∈ Finset.range (N + 1),
          (N : ℝ) / (Nat.lcm d e : ℝ) :=
      sum_card_divisors_sq_le_lcm_reciprocal_sum N
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
          (N : ℝ) / (Nat.lcm d e : ℝ) :=
      lcm_reciprocal_range_eq_Icc N
    _ ≤ ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        ∑ g ∈ d.divisors.filter (fun g => g ∣ e),
          ((N : ℝ) * (g : ℝ)) / ((d : ℝ) * (e : ℝ)) :=
      sum_lcm_reciprocal_Icc_le_common_divisor_sum N
    _ ≤ (N : ℝ) * H ^ 3 := by
      dsimp [H]
      exact common_divisor_sum_Icc_le_harmonic_cube N
    _ ≤ 8 * ((N : ℝ) + 1) * L ^ 3 := hcube
    _ = 8 * ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) ^ 3 := by
      rfl

private lemma vaughanLambdaHigh_nonneg (V n : ℕ) :
    0 ≤ vaughanLambdaHigh V n := by
  unfold vaughanLambdaHigh
  by_cases h : V < n
  · simp [h, ArithmeticFunction.vonMangoldt_nonneg]
  · simp [h]

private lemma vaughanLambdaHigh_le_vonMangoldt (V n : ℕ) :
    vaughanLambdaHigh V n ≤ ArithmeticFunction.vonMangoldt n := by
  unfold vaughanLambdaHigh
  by_cases h : V < n
  · simp [h]
  · simp [h, ArithmeticFunction.vonMangoldt_nonneg]

/-- A crude pointwise bound for the left Vaughan Type-II coefficients.  The
constant is intentionally weak: it bounds the two divisor convolutions by the
number of divisor pairs and the von-Mangoldt factor by `log (m+1)`. -/
theorem vaughanTypeIICoeffLeft_norm_le (U V m : ℕ) :
    ‖vaughanTypeIICoeffLeft U V m‖ ≤
      ((m + 1 : ℝ) ^ 2) * Real.log (m + 1 : ℝ) := by
  unfold vaughanTypeIICoeffLeft vaughanTypeIIArithmetic
  rw [ArithmeticFunction.mul_apply]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  calc
    |∑ x ∈ m.divisorsAntidiagonal,
        vaughanLambdaHigh V x.fst *
          (vaughanMuHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) x.snd| ≤
        ∑ x ∈ m.divisorsAntidiagonal,
          |vaughanLambdaHigh V x.fst *
            (vaughanMuHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) x.snd| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ m.divisorsAntidiagonal, (m + 1 : ℝ) * Real.log (m + 1 : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro x hx
      have hLambda : |vaughanLambdaHigh V x.fst| ≤ Real.log (m + 1 : ℝ) :=
        vaughanLambdaHigh_abs_le_log_succ V m (Nat.fst_mem_divisors_of_mem_antidiagonal hx)
      have hinner :
          |(vaughanMuHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) x.snd| ≤
            (m + 1 : ℝ) :=
        (vaughanMuHigh_mul_zeta_abs_le_card_divisors U x.snd).trans
          (card_divisors_le_succ_of_mem_antidiagonal hx)
      rw [abs_mul]
      calc
        |vaughanLambdaHigh V x.fst| *
            |(vaughanMuHigh U *
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) x.snd| ≤
            Real.log (m + 1 : ℝ) * (m + 1 : ℝ) :=
          mul_le_mul hLambda hinner (abs_nonneg _) (log_nat_succ_nonneg m)
        _ = (m + 1 : ℝ) * Real.log (m + 1 : ℝ) := by ring
    _ = (#m.divisorsAntidiagonal : ℝ) *
          ((m + 1 : ℝ) * Real.log (m + 1 : ℝ)) := by simp
    _ ≤ (m + 1 : ℝ) * ((m + 1 : ℝ) * Real.log (m + 1 : ℝ)) := by
      exact mul_le_mul_of_nonneg_right (card_divisorsAntidiagonal_le_succ m)
        (mul_nonneg (by positivity) (log_nat_succ_nonneg m))
    _ = ((m + 1 : ℝ) ^ 2) * Real.log (m + 1 : ℝ) := by ring

private lemma vaughanTypeIIArithmetic_abs_le_mul_log_succ (U V m : ℕ) :
    |vaughanTypeIIArithmetic U V m| ≤ (m : ℝ) * Real.log (m + 1 : ℝ) := by
  unfold vaughanTypeIIArithmetic
  rw [ArithmeticFunction.mul_apply]
  by_cases hm0 : m = 0
  · subst m
    simp
  · calc
      |∑ x ∈ m.divisorsAntidiagonal,
          vaughanLambdaHigh V x.fst *
            (vaughanMuHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) x.snd| ≤
          ∑ x ∈ m.divisorsAntidiagonal,
            |vaughanLambdaHigh V x.fst *
              (vaughanMuHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) x.snd| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ m.divisorsAntidiagonal, vaughanLambdaHigh V x.fst * (m : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro x hx
        have hlambda_nonneg : 0 ≤ vaughanLambdaHigh V x.fst :=
          vaughanLambdaHigh_nonneg V x.fst
        have hinner :
            |(vaughanMuHigh U *
                (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) x.snd| ≤ (m : ℝ) := by
          have hsnd_le : (x.snd : ℝ) ≤ (m : ℝ) := by
            exact_mod_cast Nat.divisor_le (Nat.snd_mem_divisors_of_mem_antidiagonal hx)
          exact (vaughanMuHigh_mul_zeta_abs_le_self U x.snd).trans hsnd_le
        rw [abs_mul, abs_of_nonneg hlambda_nonneg]
        exact mul_le_mul_of_nonneg_left hinner hlambda_nonneg
      _ = (∑ x ∈ m.divisorsAntidiagonal, vaughanLambdaHigh V x.fst) * (m : ℝ) := by
        rw [Finset.sum_mul]
      _ ≤ (∑ d ∈ m.divisors, ArithmeticFunction.vonMangoldt d) * (m : ℝ) := by
        have hsum_le :
            ∑ x ∈ m.divisorsAntidiagonal, vaughanLambdaHigh V x.fst ≤
              ∑ x ∈ m.divisorsAntidiagonal, ArithmeticFunction.vonMangoldt x.fst := by
          exact Finset.sum_le_sum fun x _hx => vaughanLambdaHigh_le_vonMangoldt V x.fst
        have hsum_eq :
            ∑ x ∈ m.divisorsAntidiagonal, ArithmeticFunction.vonMangoldt x.fst =
              ∑ d ∈ m.divisors, ArithmeticFunction.vonMangoldt d := by
          rw [Nat.sum_divisorsAntidiagonal
            (fun d _m => ArithmeticFunction.vonMangoldt d)]
        exact mul_le_mul_of_nonneg_right (hsum_le.trans_eq hsum_eq) (by positivity)
      _ = Real.log (m : ℝ) * (m : ℝ) := by
        rw [ArithmeticFunction.vonMangoldt_sum]
      _ ≤ Real.log (m + 1 : ℝ) * (m : ℝ) := by
        have hlog : Real.log (m : ℝ) ≤ Real.log (m + 1 : ℝ) := by
          exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hm0)
            (by exact_mod_cast Nat.le_succ m)
        exact mul_le_mul_of_nonneg_right hlog (by positivity)
      _ = (m : ℝ) * Real.log (m + 1 : ℝ) := by ring


private lemma vaughanTypeIIArithmetic_abs_le_two_sqrt_log (U V m : ℕ) :
    |vaughanTypeIIArithmetic U V m| ≤
      2 * Real.sqrt (m + 1 : ℝ) * Real.log (m + 1 : ℝ) := by
  unfold vaughanTypeIIArithmetic
  rw [ArithmeticFunction.mul_apply]
  by_cases hm0 : m = 0
  · subst m
    simp
  · let D : ℝ := 2 * Real.sqrt (m + 1 : ℝ)
    calc
      |∑ x ∈ m.divisorsAntidiagonal,
          vaughanLambdaHigh V x.fst *
            (vaughanMuHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) x.snd| ≤
          ∑ x ∈ m.divisorsAntidiagonal,
            |vaughanLambdaHigh V x.fst *
              (vaughanMuHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) x.snd| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ m.divisorsAntidiagonal, vaughanLambdaHigh V x.fst * D := by
        refine Finset.sum_le_sum ?_
        intro x hx
        have hlambda_nonneg : 0 ≤ vaughanLambdaHigh V x.fst :=
          vaughanLambdaHigh_nonneg V x.fst
        have hinner :
            |(vaughanMuHigh U *
                (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) x.snd| ≤ D := by
          have hsnd_succ : (x.snd + 1 : ℝ) ≤ (m + 1 : ℝ) := by
            exact_mod_cast Nat.succ_le_succ
              (Nat.divisor_le (Nat.snd_mem_divisors_of_mem_antidiagonal hx))
          exact (vaughanMuHigh_mul_zeta_abs_le_card_divisors U x.snd).trans
            ((card_divisors_le_two_real_sqrt_succ x.snd).trans
              (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsnd_succ) (by norm_num)))
        rw [abs_mul, abs_of_nonneg hlambda_nonneg]
        exact mul_le_mul_of_nonneg_left hinner hlambda_nonneg
      _ = (∑ x ∈ m.divisorsAntidiagonal, vaughanLambdaHigh V x.fst) * D := by
        rw [Finset.sum_mul]
      _ ≤ (∑ d ∈ m.divisors, ArithmeticFunction.vonMangoldt d) * D := by
        have hsum_le :
            ∑ x ∈ m.divisorsAntidiagonal, vaughanLambdaHigh V x.fst ≤
              ∑ x ∈ m.divisorsAntidiagonal, ArithmeticFunction.vonMangoldt x.fst := by
          exact Finset.sum_le_sum fun x _hx => vaughanLambdaHigh_le_vonMangoldt V x.fst
        have hsum_eq :
            ∑ x ∈ m.divisorsAntidiagonal, ArithmeticFunction.vonMangoldt x.fst =
              ∑ d ∈ m.divisors, ArithmeticFunction.vonMangoldt d := by
          rw [Nat.sum_divisorsAntidiagonal
            (fun d _m => ArithmeticFunction.vonMangoldt d)]
        exact mul_le_mul_of_nonneg_right (hsum_le.trans_eq hsum_eq) (by positivity)
      _ = Real.log (m : ℝ) * D := by
        rw [ArithmeticFunction.vonMangoldt_sum]
      _ ≤ Real.log (m + 1 : ℝ) * D := by
        have hlog : Real.log (m : ℝ) ≤ Real.log (m + 1 : ℝ) := by
          exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hm0)
            (by exact_mod_cast Nat.le_succ m)
        exact mul_le_mul_of_nonneg_right hlog (by positivity)
      _ = 2 * Real.sqrt (m + 1 : ℝ) * Real.log (m + 1 : ℝ) := by
        dsimp [D]
        ring


private lemma vaughanTypeIICoeffLeft_norm_le_of_le
    (U V N m : ℕ) (hm : m ≤ N) :
    ‖vaughanTypeIICoeffLeft U V m‖ ≤
      ((N + 1 : ℝ) ^ 2) * Real.log (N + 1 : ℝ) := by
  have hbase := vaughanTypeIICoeffLeft_norm_le U V m
  have hm_succ : (m + 1 : ℝ) ≤ (N + 1 : ℝ) := by
    exact_mod_cast Nat.succ_le_succ hm
  have hpow : (m + 1 : ℝ) ^ 2 ≤ (N + 1 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hm_succ 2
  have hlog : Real.log (m + 1 : ℝ) ≤ Real.log (N + 1 : ℝ) :=
    Real.log_le_log (by exact_mod_cast Nat.succ_pos m) hm_succ
  exact hbase.trans (mul_le_mul hpow hlog (log_nat_succ_nonneg m) (by positivity))

private lemma vaughanMuLow_mul_zeta_abs_le_card_divisors (U m : ℕ) :
    |(vaughanMuLow U *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m| ≤ (#m.divisors : ℝ) := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  calc
    |∑ d ∈ m.divisors, vaughanMuLow U d| ≤
        ∑ d ∈ m.divisors, |vaughanMuLow U d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ m.divisors, (1 : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro d _hd
      unfold vaughanMuLow
      by_cases h : d ≤ U
      · simp only [ArithmeticFunction.coe_mk]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      · simp [h]
    _ = (#m.divisors : ℝ) := by simp

private lemma vaughanTypeITail_eq (V : ℕ) :
    ArithmeticFunction.log -
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLambdaLow V =
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLambdaHigh V := by
  calc
    ArithmeticFunction.log -
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLambdaLow V =
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * ArithmeticFunction.vonMangoldt -
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLambdaLow V := by
          rw [ArithmeticFunction.zeta_mul_vonMangoldt]
    _ = (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          (vaughanLambdaLow V + vaughanLambdaHigh V) -
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLambdaLow V := by
          rw [vaughanLambdaLow_add_high]
    _ = (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLambdaHigh V := by ring

private lemma vaughanTypeITail_abs_le_log_succ (V m : ℕ) {d : ℕ}
    (hd : d ∈ m.divisors) :
    |(ArithmeticFunction.log -
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLambdaLow V) d| ≤
      Real.log (m + 1 : ℝ) := by
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdle : d ≤ m := Nat.divisor_le hd
  have hdle_succ : (d : ℝ) ≤ (m + 1 : ℝ) := by
    exact_mod_cast (le_trans hdle (Nat.le_succ m))
  have hlog_le : Real.log (d : ℝ) ≤ Real.log (m + 1 : ℝ) :=
    Real.log_le_log (by exact_mod_cast hdpos) hdle_succ
  rw [vaughanTypeITail_eq]
  rw [mul_comm, ArithmeticFunction.coe_mul_zeta_apply]
  have hnonneg :
      0 ≤ ∑ e ∈ d.divisors, vaughanLambdaHigh V e := by
    exact Finset.sum_nonneg fun e _he => vaughanLambdaHigh_nonneg V e
  rw [abs_of_nonneg hnonneg]
  calc
    ∑ e ∈ d.divisors, vaughanLambdaHigh V e ≤
        ∑ e ∈ d.divisors, ArithmeticFunction.vonMangoldt e := by
      exact Finset.sum_le_sum fun e _he => vaughanLambdaHigh_le_vonMangoldt V e
    _ = Real.log (d : ℝ) := ArithmeticFunction.vonMangoldt_sum
    _ ≤ Real.log (m + 1 : ℝ) := hlog_le

private lemma vaughanTypeIInnerArithmetic_abs_le_of_le
    (V N m : ℕ) (hm : m ≤ N) :
    |vaughanTypeIInnerArithmetic V m| ≤ Real.log (N + 1 : ℝ) := by
  unfold vaughanTypeIInnerArithmetic
  by_cases hm0 : m = 0
  · subst m
    simp [ArithmeticFunction.map_zero, log_nat_succ_nonneg N]
  · have hself :
        |(ArithmeticFunction.log -
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLambdaLow V) m| ≤
          Real.log (m + 1 : ℝ) :=
      vaughanTypeITail_abs_le_log_succ V m (Nat.mem_divisors_self m hm0)
    have hm_succ : (m + 1 : ℝ) ≤ (N + 1 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ hm
    exact hself.trans (Real.log_le_log (by exact_mod_cast Nat.succ_pos m) hm_succ)

private lemma vaughanTypeIArithmetic_abs_le (U V m : ℕ) :
    |vaughanTypeIArithmetic U V m| ≤
      (m + 1 : ℝ) * Real.log (m + 1 : ℝ) := by
  unfold vaughanTypeIArithmetic
  rw [ArithmeticFunction.mul_apply]
  calc
    |∑ x ∈ m.divisorsAntidiagonal,
        vaughanMuLow U x.fst *
          (ArithmeticFunction.log -
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLambdaLow V) x.snd| ≤
        ∑ x ∈ m.divisorsAntidiagonal,
          |vaughanMuLow U x.fst *
            (ArithmeticFunction.log -
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLambdaLow V) x.snd| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ m.divisorsAntidiagonal, Real.log (m + 1 : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro x hx
      have hmu : |vaughanMuLow U x.fst| ≤ (1 : ℝ) := by
        unfold vaughanMuLow
        by_cases h : x.fst ≤ U
        · simp only [ArithmeticFunction.coe_mk]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := x.fst)
        · simp [h]
      have htail :
          |(ArithmeticFunction.log -
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLambdaLow V) x.snd| ≤
            Real.log (m + 1 : ℝ) :=
        vaughanTypeITail_abs_le_log_succ V m (Nat.snd_mem_divisors_of_mem_antidiagonal hx)
      rw [abs_mul]
      calc
        |vaughanMuLow U x.fst| *
            |(ArithmeticFunction.log -
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLambdaLow V) x.snd| ≤
            (1 : ℝ) * Real.log (m + 1 : ℝ) :=
          mul_le_mul hmu htail (abs_nonneg _) (by norm_num)
        _ = Real.log (m + 1 : ℝ) := by ring
    _ = (#m.divisorsAntidiagonal : ℝ) *
          Real.log (m + 1 : ℝ) := by simp
    _ ≤ (m + 1 : ℝ) * Real.log (m + 1 : ℝ) := by
      exact mul_le_mul_of_nonneg_right (card_divisorsAntidiagonal_le_succ m)
        (log_nat_succ_nonneg m)

private lemma vaughanTypeIArithmetic_abs_le_sqrt (U V m : ℕ) :
    |vaughanTypeIArithmetic U V m| ≤
      2 * Real.sqrt (m + 1 : ℝ) * Real.log (m + 1 : ℝ) := by
  unfold vaughanTypeIArithmetic
  rw [ArithmeticFunction.mul_apply]
  calc
    |∑ x ∈ m.divisorsAntidiagonal,
        vaughanMuLow U x.fst *
          (ArithmeticFunction.log -
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLambdaLow V) x.snd| ≤
        ∑ x ∈ m.divisorsAntidiagonal,
          |vaughanMuLow U x.fst *
            (ArithmeticFunction.log -
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLambdaLow V) x.snd| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ m.divisorsAntidiagonal, Real.log (m + 1 : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro x hx
      have hmu : |vaughanMuLow U x.fst| ≤ (1 : ℝ) := by
        unfold vaughanMuLow
        by_cases h : x.fst ≤ U
        · simp only [ArithmeticFunction.coe_mk]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := x.fst)
        · simp [h]
      have htail :
          |(ArithmeticFunction.log -
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLambdaLow V) x.snd| ≤
            Real.log (m + 1 : ℝ) :=
        vaughanTypeITail_abs_le_log_succ V m (Nat.snd_mem_divisors_of_mem_antidiagonal hx)
      rw [abs_mul]
      calc
        |vaughanMuLow U x.fst| *
            |(ArithmeticFunction.log -
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLambdaLow V) x.snd| ≤
            (1 : ℝ) * Real.log (m + 1 : ℝ) :=
          mul_le_mul hmu htail (abs_nonneg _) (by norm_num)
        _ = Real.log (m + 1 : ℝ) := by ring
    _ = (#m.divisorsAntidiagonal : ℝ) *
          Real.log (m + 1 : ℝ) := by simp
    _ ≤ (2 * Real.sqrt (m + 1 : ℝ)) * Real.log (m + 1 : ℝ) := by
      exact mul_le_mul_of_nonneg_right (card_divisorsAntidiagonal_le_two_real_sqrt_succ m)
        (log_nat_succ_nonneg m)
    _ = 2 * Real.sqrt (m + 1 : ℝ) * Real.log (m + 1 : ℝ) := by ring

private lemma vaughanTypeIArithmetic_abs_le_of_le
    (U V N m : ℕ) (hm : m ≤ N) :
    |vaughanTypeIArithmetic U V m| ≤
      (N + 1 : ℝ) * Real.log (N + 1 : ℝ) := by
  have hbase := vaughanTypeIArithmetic_abs_le U V m
  have hm_succ : (m + 1 : ℝ) ≤ (N + 1 : ℝ) := by
    exact_mod_cast Nat.succ_le_succ hm
  have hlog : Real.log (m + 1 : ℝ) ≤ Real.log (N + 1 : ℝ) :=
    Real.log_le_log (by exact_mod_cast Nat.succ_pos m) hm_succ
  exact hbase.trans (mul_le_mul hm_succ hlog (log_nat_succ_nonneg m) (by positivity))

private lemma vaughanTypeIArithmetic_abs_le_sqrt_of_le
    (U V N m : ℕ) (hm : m ≤ N) :
    |vaughanTypeIArithmetic U V m| ≤
      2 * Real.sqrt (N + 1 : ℝ) * Real.log (N + 1 : ℝ) := by
  have hbase := vaughanTypeIArithmetic_abs_le_sqrt U V m
  have hm_succ : (m + 1 : ℝ) ≤ (N + 1 : ℝ) := by
    exact_mod_cast Nat.succ_le_succ hm
  have hsqrt :
      Real.sqrt (m + 1 : ℝ) ≤ Real.sqrt (N + 1 : ℝ) :=
    Real.sqrt_le_sqrt hm_succ
  have hfactor :
      2 * Real.sqrt (m + 1 : ℝ) ≤ 2 * Real.sqrt (N + 1 : ℝ) :=
    mul_le_mul_of_nonneg_left hsqrt (by norm_num)
  have hlog : Real.log (m + 1 : ℝ) ≤ Real.log (N + 1 : ℝ) :=
    Real.log_le_log (by exact_mod_cast Nat.succ_pos m) hm_succ
  exact hbase.trans
    (mul_le_mul hfactor hlog (log_nat_succ_nonneg m)
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))

private lemma vaughanTypeICoeff_zero_norm_le (U V N : ℕ) :
    ‖vaughanTypeICoeff U V N 0‖ ≤
      ((N + 1 : ℝ) ^ 2) * Real.log (N + 1 : ℝ) := by
  unfold vaughanTypeICoeff oneStepTypeICoeff
  simp only [ite_true]
  set S : ℂ := ∑ k ∈ (Finset.range (N + 1)).filter (fun k => k ≠ 0),
    (vaughanTypeIArithmetic U V k : ℂ)
  have hsum_norm :
      ‖S‖ ≤
        ∑ _k ∈ (Finset.range (N + 1)).filter (fun k => k ≠ 0),
          (N + 1 : ℝ) * Real.log (N + 1 : ℝ) := by
    calc
      ‖S‖ ≤ ∑ k ∈ (Finset.range (N + 1)).filter (fun k => k ≠ 0),
          ‖(vaughanTypeIArithmetic U V k : ℂ)‖ := by
        dsimp [S]
        exact norm_sum_le _ _
      _ ≤ ∑ _k ∈ (Finset.range (N + 1)).filter (fun k => k ≠ 0),
          (N + 1 : ℝ) * Real.log (N + 1 : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro k hk
        have hk_le : k ≤ N :=
          Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
        simpa [Complex.norm_real, Real.norm_eq_abs] using
          vaughanTypeIArithmetic_abs_le_of_le U V N k hk_le
  have hcard :
      ((Finset.range (N + 1)).filter (fun k => k ≠ 0)).card ≤ N + 1 :=
    (Finset.card_filter_le _ _).trans_eq (Finset.card_range (N + 1))
  have hsum_bound :
      ∑ _k ∈ (Finset.range (N + 1)).filter (fun k => k ≠ 0),
          (N + 1 : ℝ) * Real.log (N + 1 : ℝ) ≤
        (N + 1 : ℝ) * ((N + 1 : ℝ) * Real.log (N + 1 : ℝ)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      (mul_nonneg (by positivity) (log_nat_succ_nonneg N))
  have hnormS :
      ‖S‖ ≤ (N + 1 : ℝ) *
        ((N + 1 : ℝ) * Real.log (N + 1 : ℝ)) :=
    hsum_norm.trans hsum_bound
  calc
    ‖-(S / 2)‖ ≤ ‖S‖ := by
      rw [norm_neg, norm_div]
      have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
      rw [htwo]
      exact div_le_self (norm_nonneg S) (by norm_num : (1 : ℝ) ≤ 2)
    _ ≤ (N + 1 : ℝ) * ((N + 1 : ℝ) * Real.log (N + 1 : ℝ)) := hnormS
    _ = ((N + 1 : ℝ) ^ 2) * Real.log (N + 1 : ℝ) := by ring

private lemma vaughanTypeICoeff_zero_norm_le_sqrt (U V N : ℕ) :
    ‖vaughanTypeICoeff U V N 0‖ ≤
      2 * (N + 1 : ℝ) * Real.sqrt (N + 1 : ℝ) * Real.log (N + 1 : ℝ) := by
  unfold vaughanTypeICoeff oneStepTypeICoeff
  simp only [ite_true]
  set S : ℂ := ∑ k ∈ (Finset.range (N + 1)).filter (fun k => k ≠ 0),
    (vaughanTypeIArithmetic U V k : ℂ)
  have hsum_norm :
      ‖S‖ ≤
        ∑ _k ∈ (Finset.range (N + 1)).filter (fun k => k ≠ 0),
          2 * Real.sqrt (N + 1 : ℝ) * Real.log (N + 1 : ℝ) := by
    calc
      ‖S‖ ≤ ∑ k ∈ (Finset.range (N + 1)).filter (fun k => k ≠ 0),
          ‖(vaughanTypeIArithmetic U V k : ℂ)‖ := by
        dsimp [S]
        exact norm_sum_le _ _
      _ ≤ ∑ _k ∈ (Finset.range (N + 1)).filter (fun k => k ≠ 0),
          2 * Real.sqrt (N + 1 : ℝ) * Real.log (N + 1 : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro k hk
        have hk_le : k ≤ N :=
          Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
        simpa [Complex.norm_real, Real.norm_eq_abs] using
          vaughanTypeIArithmetic_abs_le_sqrt_of_le U V N k hk_le
  have hcard :
      ((Finset.range (N + 1)).filter (fun k => k ≠ 0)).card ≤ N + 1 :=
    (Finset.card_filter_le _ _).trans_eq (Finset.card_range (N + 1))
  have hconst_nonneg :
      0 ≤ 2 * Real.sqrt (N + 1 : ℝ) * Real.log (N + 1 : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (log_nat_succ_nonneg N)
  have hsum_bound :
      ∑ _k ∈ (Finset.range (N + 1)).filter (fun k => k ≠ 0),
          2 * Real.sqrt (N + 1 : ℝ) * Real.log (N + 1 : ℝ) ≤
        (N + 1 : ℝ) *
          (2 * Real.sqrt (N + 1 : ℝ) * Real.log (N + 1 : ℝ)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hconst_nonneg
  have hnormS :
      ‖S‖ ≤ (N + 1 : ℝ) *
        (2 * Real.sqrt (N + 1 : ℝ) * Real.log (N + 1 : ℝ)) :=
    hsum_norm.trans hsum_bound
  calc
    ‖-(S / 2)‖ ≤ ‖S‖ := by
      rw [norm_neg, norm_div]
      have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
      rw [htwo]
      exact div_le_self (norm_nonneg S) (by norm_num : (1 : ℝ) ≤ 2)
    _ ≤ (N + 1 : ℝ) *
        (2 * Real.sqrt (N + 1 : ℝ) * Real.log (N + 1 : ℝ)) := hnormS
    _ = 2 * (N + 1 : ℝ) * Real.sqrt (N + 1 : ℝ) *
          Real.log (N + 1 : ℝ) := by ring


/-- The divisor-pair bilinear Type-I encoder is exactly the Vaughan Type-I
arithmetic exponential sum. -/
theorem vaughanTypeIBilinearSum_eq_arithmeticExpSum
    (U V N : ℕ) (α : ℝ) :
    vaughanTypeIBilinearSum U V N α =
      arithmeticExpSum (vaughanTypeIArithmetic U V) N α := by
  unfold vaughanTypeIBilinearSum arithmeticExpSum vaughanTypeIArithmetic
    vaughanTypeIBilinearCoeff vaughanTypeIBilinearInnerCoeff
    vaughanTypeIInnerArithmetic
  refine Finset.sum_congr rfl ?_
  intro n _hn
  simp only [ArithmeticFunction.mul_apply]
  symm
  rw [Complex.ofReal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro dm hdm
  have hprod : dm.1 * dm.2 = n := (Nat.mem_divisorsAntidiagonal.mp hdm).1
  simp [hprod, mul_assoc]

/-- The divisor-pair bilinear Type-II encoder is exactly the Vaughan Type-II
arithmetic exponential sum. -/
theorem vaughanTypeIIBilinearSum_eq_arithmeticExpSum
    (U V N : ℕ) (α : ℝ) :
    vaughanTypeIIBilinearSum U V N α =
      arithmeticExpSum (vaughanTypeIIArithmetic U V) N α := by
  unfold vaughanTypeIIBilinearSum arithmeticExpSum vaughanTypeIIArithmetic
    vaughanTypeIIBilinearCoeff vaughanTypeIIBilinearInnerCoeff
    vaughanTypeIIInnerArithmetic
  refine Finset.sum_congr rfl ?_
  intro n _hn
  simp only [ArithmeticFunction.mul_apply]
  symm
  rw [Complex.ofReal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro dm hdm
  have hprod : dm.1 * dm.2 = n := (Nat.mem_divisorsAntidiagonal.mp hdm).1
  simp [hprod, mul_assoc]

/-- At `U = V = 1`, the divisor-pair Type-II sum is the single exponential sum
with coefficient sequence `Λ - log`. -/
theorem vaughanTypeIIBilinearSum_one_one_eq_lambda_sub_log_expSum
    (N : ℕ) (α : ℝ) :
    vaughanTypeIIBilinearSum 1 1 N α =
      arithmeticExpSum (ArithmeticFunction.vonMangoldt - ArithmeticFunction.log) N α := by
  rw [vaughanTypeIIBilinearSum_eq_arithmeticExpSum,
    vaughanTypeIIArithmetic_one_one_eq]

/-- The delta-at-one Type-II encoder is exactly the arithmetic exponential sum. -/
theorem typeIISum_deltaOneCoeff_eq_arithmeticExpSum
    (F : ArithmeticFunction ℝ) (N : ℕ) (α : ℝ) :
    typeIISum (fun m => (F m : ℂ)) deltaOneCoeff N 1 α = arithmeticExpSum F N α := by
  simp [typeIISum, arithmeticExpSum, deltaOneCoeff]


/-- Vaughan's finite exponential-sum decomposition with the Type-I term kept
in divisor-pair bilinear form rather than routed through the rectangular
`oneStepTypeICoeff` encoder. -/
theorem vaughan_to_typeI_typeII_bilinear
    (U V N : ℕ) (hU : 0 < U) (hV : 0 < V) (α : ℝ) :
    Vinogradov.vonMangoldtExpSum α N =
      arithmeticExpSum (vaughanLambdaLow V) N α +
        vaughanTypeIBilinearSum U V N α +
        typeIISum (vaughanTypeIICoeffLeft U V) vaughanTypeIICoeffRight N 1 α := by
  unfold vaughanTypeIICoeffLeft vaughanTypeIICoeffRight
  rw [vaughanTypeIBilinearSum_eq_arithmeticExpSum,
    typeIISum_deltaOneCoeff_eq_arithmeticExpSum]
  unfold Vinogradov.vonMangoldtExpSum arithmeticExpSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  by_cases hn0 : n = 0
  · simp [hn0, ArithmeticFunction.map_zero]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hpoint := vaughan_identity_finite U V hU hV n hnpos
    have hpointC :
        (ArithmeticFunction.vonMangoldt n : ℂ) =
          (vaughanLambdaLow V n : ℂ) +
            (vaughanTypeIArithmetic U V n : ℂ) +
            (vaughanTypeIIArithmetic U V n : ℂ) := by
      exact_mod_cast hpoint
    rw [hpointC]
    ring

/-- Vaughan's finite exponential-sum decomposition with both Type-I and
Type-II terms kept in divisor-pair bilinear convolution form. -/
theorem vaughan_to_typeI_typeII_bilinear_full
    (U V N : ℕ) (hU : 0 < U) (hV : 0 < V) (α : ℝ) :
    Vinogradov.vonMangoldtExpSum α N =
      arithmeticExpSum (vaughanLambdaLow V) N α +
        vaughanTypeIBilinearSum U V N α +
        vaughanTypeIIBilinearSum U V N α := by
  rw [vaughan_to_typeI_typeII_bilinear U V N hU hV α]
  unfold vaughanTypeIICoeffLeft vaughanTypeIICoeffRight
  rw [typeIISum_deltaOneCoeff_eq_arithmeticExpSum,
    ← vaughanTypeIIBilinearSum_eq_arithmeticExpSum]

private lemma sum_divisorsAntidiagonal_indicator_le
    (U n : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    ∑ dm ∈ n.divisorsAntidiagonal, (if dm.1 ≤ U then L else 0) ≤
      ∑ d ∈ Finset.Icc 1 U, (if d ∣ n then L else 0) := by
  rw [Nat.sum_divisorsAntidiagonal (fun d _m => if d ≤ U then L else 0)]
  calc
    ∑ d ∈ n.divisors, (if d ≤ U then L else 0) =
        ∑ d ∈ n.divisors.filter (fun d => d ≤ U), L := by
      rw [Finset.sum_filter]
    _ = ∑ d ∈ n.divisors.filter (fun d => d ≤ U), (if d ∣ n then L else 0) := by
      refine Finset.sum_congr rfl ?_
      intro d hd
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
      simp [hdvd]
    _ ≤ ∑ d ∈ Finset.Icc 1 U, (if d ∣ n then L else 0) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro d hd
        rw [Finset.mem_Icc]
        exact ⟨Nat.succ_le_iff.mpr (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1),
          (Finset.mem_filter.mp hd).2⟩
      · intro d _hdI _hdnot
        by_cases hdvd : d ∣ n
        · simp [hdvd, hL]
        · simp [hdvd]

private lemma sum_Ioc_indicator_dvd_eq_div_mul
    (N d : ℕ) (L : ℝ) :
    ∑ n ∈ Finset.Ioc 0 N, (if d ∣ n then L else 0) = ((N / d : ℕ) : ℝ) * L := by
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div]


private lemma vaughanTypeIIInnerArithmetic_abs_le_two_sqrt_succ (U m : ℕ) :
    |vaughanTypeIIInnerArithmetic U m| ≤ 2 * Real.sqrt (m + 1 : ℝ) := by
  unfold vaughanTypeIIInnerArithmetic
  exact (vaughanMuHigh_mul_zeta_abs_le_card_divisors U m).trans
    (card_divisors_le_two_real_sqrt_succ m)

private lemma sum_divisorsAntidiagonal_indicator_Ioc_le
    (V N n : ℕ) {B : ℝ} (hB : 0 ≤ B) (hn : n ≤ N) :
    ∑ dm ∈ n.divisorsAntidiagonal, (if V < dm.1 then B else 0) ≤
      ∑ d ∈ Finset.Ioc V N, (if d ∣ n then B else 0) := by
  rw [Nat.sum_divisorsAntidiagonal (fun d _m => if V < d then B else 0)]
  calc
    ∑ d ∈ n.divisors, (if V < d then B else 0) =
        ∑ d ∈ n.divisors.filter (fun d => V < d), B := by
      rw [Finset.sum_filter]
    _ = ∑ d ∈ n.divisors.filter (fun d => V < d), (if d ∣ n then B else 0) := by
      refine Finset.sum_congr rfl ?_
      intro d hd
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
      simp [hdvd]
    _ ≤ ∑ d ∈ Finset.Ioc V N, (if d ∣ n then B else 0) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro d hd
        rw [Finset.mem_Ioc]
        have hdmem : d ∈ n.divisors := (Finset.mem_filter.mp hd).1
        exact ⟨(Finset.mem_filter.mp hd).2, (Nat.divisor_le hdmem).trans hn⟩
      · intro d _hdI _hdnot
        by_cases hdvd : d ∣ n
        · simp [hdvd, hB]
        · simp [hdvd]


private lemma vaughanTypeIIBilinearInnerCoeff_zero (U : ℕ) :
    vaughanTypeIIBilinearInnerCoeff U 0 = 0 := by
  simp [vaughanTypeIIBilinearInnerCoeff, vaughanTypeIIInnerArithmetic]

/-- Fixed-outer-divisor form of the divisor-pair Vaughan Type-II sum. -/
theorem vaughanTypeIIBilinearSum_eq_fixed_outer
    (U V N : ℕ) (α : ℝ) :
    vaughanTypeIIBilinearSum U V N α =
      ∑ d ∈ Finset.Ioc V N,
        vaughanTypeIIBilinearCoeff V d *
          ∑ m ∈ Finset.range (N / d + 1),
            vaughanTypeIIBilinearInnerCoeff U m * addChar α (d * m) := by
  classical
  let source : Finset (Sigma fun _n : ℕ => ℕ × ℕ) :=
    (Finset.range (N + 1)).sigma fun n => n.divisorsAntidiagonal
  let target : Finset (Sigma fun _d : ℕ => ℕ) :=
    (Finset.Ioc V N).sigma fun d =>
      (Finset.range (N / d + 1)).filter fun m => m ≠ 0
  let T : ℕ → ℕ → ℂ := fun d m =>
    vaughanTypeIIBilinearCoeff V d *
      vaughanTypeIIBilinearInnerCoeff U m * addChar α (d * m)
  have hsource_filter :
      ∑ x ∈ source.filter (fun x => V < x.2.1), T x.2.1 x.2.2 =
        ∑ y ∈ target, T y.1 y.2 := by
    refine Finset.sum_bij
      (fun x hx => ⟨x.2.1, x.2.2⟩) ?_ ?_ ?_ ?_
    · intro x hx
      rcases x with ⟨n, dm⟩
      simp only [source, target, Finset.mem_filter, Finset.mem_sigma, Finset.mem_range,
        Finset.mem_Ioc] at hx ⊢
      rcases hx with ⟨⟨hn_range, hdm⟩, hVd⟩
      have hnle : n ≤ N := Nat.lt_succ_iff.mp hn_range
      have hdmem : dm.1 ∈ n.divisors := Nat.fst_mem_divisors_of_mem_antidiagonal hdm
      have hdle : dm.1 ≤ N := (Nat.divisor_le hdmem).trans hnle
      have hdpos : 0 < dm.1 :=
        Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hdm)
      have hmpos : dm.2 ≠ 0 := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hdm
      have hprod : dm.1 * dm.2 = n := (Nat.mem_divisorsAntidiagonal.mp hdm).1
      have hmul_le : dm.2 * dm.1 ≤ N := by
        rw [Nat.mul_comm, hprod]
        exact hnle
      have hmle : dm.2 ≤ N / dm.1 :=
        (Nat.le_div_iff_mul_le hdpos).2 hmul_le
      exact ⟨⟨hVd, hdle⟩, ⟨Nat.lt_succ_iff.mpr hmle, hmpos⟩⟩
    · intro x₁ hx₁ x₂ hx₂ hmap
      rcases x₁ with ⟨n₁, dm₁⟩
      rcases x₂ with ⟨n₂, dm₂⟩
      simp only at hmap
      have hdm : dm₁ = dm₂ := by
        cases dm₁
        cases dm₂
        simpa using hmap
      subst dm₂
      simp only [source, Finset.mem_filter, Finset.mem_sigma] at hx₁ hx₂
      have hprod₁ : dm₁.1 * dm₁.2 = n₁ :=
        (Nat.mem_divisorsAntidiagonal.mp hx₁.1.2).1
      have hprod₂ : dm₁.1 * dm₁.2 = n₂ :=
        (Nat.mem_divisorsAntidiagonal.mp hx₂.1.2).1
      subst n₁
      subst n₂
      rfl
    · intro y hy
      rcases y with ⟨d, m⟩
      simp only [target, Finset.mem_sigma, Finset.mem_filter, Finset.mem_range,
        Finset.mem_Ioc] at hy
      rcases hy with ⟨⟨hVd, hdle⟩, hmrange, hmne⟩
      let n := d * m
      have hdpos : 0 < d := lt_of_le_of_lt (Nat.zero_le V) hVd
      have hmle : m ≤ N / d := Nat.lt_succ_iff.mp hmrange
      have hnle : n ≤ N := by
        dsimp [n]
        have hmul_le : m * d ≤ N := (Nat.le_div_iff_mul_le hdpos).1 hmle
        simpa [Nat.mul_comm] using hmul_le
      have hnne : n ≠ 0 := by
        dsimp [n]
        exact Nat.mul_ne_zero (Nat.ne_of_gt hdpos) hmne
      refine ⟨⟨n, (d, m)⟩, ?_, rfl⟩
      simp only [source, Finset.mem_filter, Finset.mem_sigma, Finset.mem_range]
      exact ⟨⟨Nat.lt_succ_iff.mpr hnle,
        (Nat.mem_divisorsAntidiagonal).2 ⟨rfl, hnne⟩⟩, hVd⟩
    · intro x hx
      rfl
  have hsource :
      ∑ x ∈ source, T x.2.1 x.2.2 =
        ∑ y ∈ target, T y.1 y.2 := by
    calc
      ∑ x ∈ source, T x.2.1 x.2.2 =
          ∑ x ∈ source, if V < x.2.1 then T x.2.1 x.2.2 else 0 := by
        refine Finset.sum_congr rfl ?_
        intro x _hx
        by_cases hVx : V < x.2.1
        · simp [hVx]
        · simp [hVx, T, vaughanTypeIIBilinearCoeff, vaughanLambdaHigh]
      _ = ∑ x ∈ source.filter (fun x => V < x.2.1), T x.2.1 x.2.2 := by
        rw [Finset.sum_filter]
      _ = ∑ y ∈ target, T y.1 y.2 := hsource_filter
  have htarget_full :
      ∑ y ∈ target, T y.1 y.2 =
        ∑ d ∈ Finset.Ioc V N,
          ∑ m ∈ Finset.range (N / d + 1), T d m := by
    calc
      ∑ y ∈ target, T y.1 y.2 =
          ∑ d ∈ Finset.Ioc V N,
            ∑ m ∈ (Finset.range (N / d + 1)).filter (fun m => m ≠ 0), T d m := by
        rw [Finset.sum_sigma]
      _ = ∑ d ∈ Finset.Ioc V N,
            ∑ m ∈ Finset.range (N / d + 1), T d m := by
        refine Finset.sum_congr rfl ?_
        intro d _hd
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        intro m _hm
        by_cases hm : m ≠ 0
        · simp [hm]
        · have hm0 : m = 0 := not_not.mp hm
          simp [hm0, T, vaughanTypeIIBilinearInnerCoeff_zero U]
  unfold vaughanTypeIIBilinearSum
  calc
    ∑ n ∈ Finset.range (N + 1),
        ∑ dm ∈ n.divisorsAntidiagonal,
          vaughanTypeIIBilinearCoeff V dm.1 *
            vaughanTypeIIBilinearInnerCoeff U dm.2 * addChar α (dm.1 * dm.2) =
        ∑ x ∈ source, T x.2.1 x.2.2 := by
      rw [Finset.sum_sigma]
    _ = ∑ d ∈ Finset.Ioc V N,
          ∑ m ∈ Finset.range (N / d + 1), T d m := hsource.trans htarget_full
    _ = ∑ d ∈ Finset.Ioc V N,
          vaughanTypeIIBilinearCoeff V d *
            ∑ m ∈ Finset.range (N / d + 1),
              vaughanTypeIIBilinearInnerCoeff U m * addChar α (d * m) := by
      refine Finset.sum_congr rfl ?_
      intro d _hd
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro m _hm
      simp [T, mul_assoc]

end Vinogradov
