/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the repository LICENSE.

The arithmetic-function proof below is adapted from
`AnalyticNT/Vaughan/Identity.lean` in `gersh/ternary-goldbach-lean`.
-/

import Mathlib

/-!
# A finite Vaughan identity for reciprocal exponential sums

This file proves Vaughan's identity first as an equality of arithmetic
functions and then applies it term by term to an arbitrary finite weighted
sum.  The latter formulation can be used with the reciprocal phase
`exp (2 * pi * I * x / n)` without any convergence side conditions.

With `muLow U` and `lambdaLow V` denoting the indicated truncations, the
three pieces are

* `lambdaLow V`;
* `typeI U V = muLow U * (log - zeta * lambdaLow V)`;
* `typeII U V = lambdaHigh V * (muHigh U * zeta)`.

The proved identity is

`vonMangoldt = lambdaLow V + typeI U V + typeII U V`.

The final two theorems also unfold the Type-I and Type-II convolutions as
finite sums over divisor antidiagonals.  These are the forms used before
applying exponential-sum estimates.
-/

noncomputable section

namespace Erdos175.Vaughan

open scoped ArithmeticFunction BigOperators

/-- The Möbius function truncated to indices at most `U`. -/
def muLow (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ U then (ArithmeticFunction.moebius n : ℝ) else 0, by simp⟩

/-- The complementary Möbius tail. -/
def muHigh (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if U < n then (ArithmeticFunction.moebius n : ℝ) else 0, by simp⟩

/-- The von Mangoldt function truncated to indices at most `V`. -/
def lambdaLow (V : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ V then ArithmeticFunction.vonMangoldt n else 0, by simp⟩

/-- The complementary von Mangoldt tail. -/
def lambdaHigh (V : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if V < n then ArithmeticFunction.vonMangoldt n else 0, by simp⟩

/-- The Type-I part of Vaughan's identity. -/
def typeI (U V : ℕ) : ArithmeticFunction ℝ :=
  muLow U *
    (ArithmeticFunction.log -
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaLow V)

/-- The Type-II part of Vaughan's identity. -/
def typeII (U V : ℕ) : ArithmeticFunction ℝ :=
  lambdaHigh V *
    (muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))

/-- The low and high Möbius truncations partition the Möbius function. -/
theorem muLow_add_muHigh (U : ℕ) :
    muLow U + muHigh U =
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
  ext n
  change (if n ≤ U then (ArithmeticFunction.moebius n : ℝ) else 0) +
      (if U < n then (ArithmeticFunction.moebius n : ℝ) else 0) =
    (ArithmeticFunction.moebius n : ℝ)
  by_cases hn : n ≤ U
  · have hnot : ¬ U < n := not_lt.mpr hn
    simp [hn, hnot]
  · have hlt : U < n := lt_of_not_ge hn
    simp [hn, hlt]

/-- The low and high von Mangoldt truncations partition `vonMangoldt`. -/
theorem lambdaLow_add_lambdaHigh (V : ℕ) :
    lambdaLow V + lambdaHigh V =
      (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) := by
  ext n
  change (if n ≤ V then ArithmeticFunction.vonMangoldt n else 0) +
      (if V < n then ArithmeticFunction.vonMangoldt n else 0) =
    ArithmeticFunction.vonMangoldt n
  by_cases hn : n ≤ V
  · have hnot : ¬ V < n := not_lt.mpr hn
    simp [hn, hnot]
  · have hlt : V < n := lt_of_not_ge hn
    simp [hn, hlt]

/-- The Type-I term can equivalently be written using the high von Mangoldt
tail.  This form makes the final convolution cancellation transparent. -/
theorem typeI_eq (U V : ℕ) :
    typeI U V =
      lambdaHigh V *
        (muLow U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) := by
  have hlog :
      ArithmeticFunction.log -
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaLow V =
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaHigh V := by
    calc
      ArithmeticFunction.log -
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaLow V =
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
              (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) -
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaLow V := by
              rw [ArithmeticFunction.zeta_mul_vonMangoldt]
      _ = (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
              (lambdaLow V + lambdaHigh V) -
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaLow V := by
              rw [lambdaLow_add_lambdaHigh]
      _ = (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaHigh V := by
              ring
  unfold typeI
  rw [hlog]
  ring

/-- The two non-low pieces add to the high von Mangoldt tail. -/
theorem typeI_add_typeII (U V : ℕ) :
    typeI U V + typeII U V = lambdaHigh V := by
  rw [typeI_eq, typeII]
  calc
    lambdaHigh V *
          (muLow U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) +
        lambdaHigh V *
          (muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) =
        lambdaHigh V *
          ((muLow U + muHigh U) *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) := by ring
    _ = lambdaHigh V *
          ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) := by
          rw [muLow_add_muHigh]
    _ = lambdaHigh V := by simp

/-- Vaughan's identity as an equality of arithmetic functions.  No positivity
hypothesis on the cutoffs is needed for this algebraic identity. -/
theorem identity (U V : ℕ) :
    (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
      lambdaLow V + typeI U V + typeII U V := by
  calc
    (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
        lambdaLow V + lambdaHigh V := (lambdaLow_add_lambdaHigh V).symm
    _ = lambdaLow V + (typeI U V + typeII U V) := by
      rw [typeI_add_typeII]
    _ = lambdaLow V + typeI U V + typeII U V := by ring

/-- Pointwise Vaughan identity. -/
theorem identity_apply (U V n : ℕ) :
    ArithmeticFunction.vonMangoldt n =
      lambdaLow V n + typeI U V n + typeII U V n := by
  exact congr_arg (fun f : ArithmeticFunction ℝ => f n) (identity U V)

/-- A finite sum of an arithmetic function with an arbitrary complex weight. -/
def finiteWeightedSum
    (s : Finset ℕ) (w : ℕ → ℂ) (F : ArithmeticFunction ℝ) : ℂ :=
  ∑ n ∈ s, (F n : ℂ) * w n

/-- Vaughan's identity applied term by term to an arbitrary finite weighted
sum.  Keeping the weight abstract makes the lemma reusable for every phase. -/
theorem finiteWeightedSum_identity
    (s : Finset ℕ) (w : ℕ → ℂ) (U V : ℕ) :
    finiteWeightedSum s w
        (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
      finiteWeightedSum s w (lambdaLow V) +
        finiteWeightedSum s w (typeI U V) +
        finiteWeightedSum s w (typeII U V) := by
  unfold finiteWeightedSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _hn => ?_
  rw [identity_apply U V n]
  push_cast
  ring

/-- The reciprocal additive character `e(x/n)`.  The value at `n = 0` is
harmless in finite sums because every arithmetic function vanishes at zero. -/
def reciprocalPhase (x : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((x / (n : ℝ) : ℝ) : ℂ))

/-- A finite reciprocal exponential sum weighted by an arithmetic function. -/
def reciprocalSum
    (s : Finset ℕ) (x : ℝ) (F : ArithmeticFunction ℝ) : ℂ :=
  finiteWeightedSum s (reciprocalPhase x) F

/-- Finite Vaughan decomposition for a reciprocal exponential sum over an
arbitrary finite set of natural numbers. -/
theorem reciprocalSum_identity
    (s : Finset ℕ) (x : ℝ) (U V : ℕ) :
    reciprocalSum s x
        (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
      reciprocalSum s x (lambdaLow V) +
        reciprocalSum s x (typeI U V) +
        reciprocalSum s x (typeII U V) := by
  exact finiteWeightedSum_identity s (reciprocalPhase x) U V

/-- Interval form of the reciprocal Vaughan decomposition. -/
theorem reciprocalSum_Ioc_identity
    (y y' : ℕ) (x : ℝ) (U V : ℕ) :
    reciprocalSum (Finset.Ioc y y') x
        (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
      reciprocalSum (Finset.Ioc y y') x (lambdaLow V) +
        reciprocalSum (Finset.Ioc y y') x (typeI U V) +
        reciprocalSum (Finset.Ioc y y') x (typeII U V) := by
  exact reciprocalSum_identity (Finset.Ioc y y') x U V

/-- Divisor-pair expansion of the Type-I reciprocal sum. -/
theorem reciprocalSum_typeI
    (s : Finset ℕ) (x : ℝ) (U V : ℕ) :
    reciprocalSum s x (typeI U V) =
      ∑ n ∈ s, ∑ dm ∈ n.divisorsAntidiagonal,
        (muLow U dm.1 : ℂ) *
          ((ArithmeticFunction.log -
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaLow V)
            dm.2 : ℂ) * reciprocalPhase x n := by
  unfold reciprocalSum finiteWeightedSum typeI
  refine Finset.sum_congr rfl fun n _hn => ?_
  rw [show
      (((muLow U *
          (ArithmeticFunction.log -
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaLow V)) n : ℝ) : ℂ) =
        ∑ dm ∈ n.divisorsAntidiagonal,
          (muLow U dm.1 : ℂ) *
            ((ArithmeticFunction.log -
                (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaLow V)
              dm.2 : ℂ) by
      rw [ArithmeticFunction.mul_apply]
      push_cast
      rfl]
  rw [Finset.sum_mul]

/-- Divisor-pair expansion of the Type-II reciprocal sum. -/
theorem reciprocalSum_typeII
    (s : Finset ℕ) (x : ℝ) (U V : ℕ) :
    reciprocalSum s x (typeII U V) =
      ∑ n ∈ s, ∑ dm ∈ n.divisorsAntidiagonal,
        (lambdaHigh V dm.1 : ℂ) *
          ((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))
            dm.2 : ℂ) * reciprocalPhase x n := by
  unfold reciprocalSum finiteWeightedSum typeII
  refine Finset.sum_congr rfl fun n _hn => ?_
  rw [show
      (((lambdaHigh V *
          (muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))) n : ℝ) : ℂ) =
        ∑ dm ∈ n.divisorsAntidiagonal,
          (lambdaHigh V dm.1 : ℂ) *
            ((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))
              dm.2 : ℂ) by
      rw [ArithmeticFunction.mul_apply]
      push_cast
      rfl]
  rw [Finset.sum_mul]

end Erdos175.Vaughan
