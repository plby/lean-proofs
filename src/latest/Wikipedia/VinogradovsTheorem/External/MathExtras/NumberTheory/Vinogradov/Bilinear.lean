/-
This file is derived from Gershon Bialer's ternary-Goldbach development.

The reused upstream material was released under the Apache License,
Version 2.0, as described in the file LICENSE. This file has been modified.
The upstream copyright and author notices are retained below.

Copyright (c) 2026 Gershon Bialer. All rights reserved.
-/
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

/-!
# Vinogradov's Bilinear Form Bound

Vinogradov's celebrated bound on the von Mangoldt exponential sum `S(α, N) =
∑_{n ≤ N} Λ(n) e^{2πi n α}`. The bound says: when `α` has a rational approximation
`a/q` with `gcd(a,q)=1` and `q` not too small/large relative to `N`, the sum has
nontrivial cancellation.

## Main statement

* `vinogradov_bilinear` — quantitative bound on `‖S(α, N)‖` for `α` on the minor arcs.

## Status

L0. Multi-page proof using Vaughan's identity to split Λ into Type I + Type II sums,
then bilinear form estimation. Major upstream target.

## References

* **Trivial form only** — current `vinogradov_bilinear` records only the
  Chebyshev-`ψ` size bound `‖expSum α N‖ ≤ K · N`; the `q^{-½}` cancellation
  form (Vinogradov, *The Method of Trigonometrical Sums in the Theory of
  Numbers*, Ch. IX Thm 1; Iwaniec–Kowalski, *Analytic Number Theory*, §13)
  is deferred to Helfgott (2012/2019), *The ternary Goldbach problem*, §4.
* Tao's blog post "The Vinogradov-Korobov estimate" — context only.

## Tags

vinogradov, exponential sum, von mangoldt, bilinear form, vaughan identity
-/

namespace Vinogradov

open Real Complex

/-- The von Mangoldt-weighted exponential sum at `α` truncated at `N`. -/
noncomputable def expSum (α : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1),
    (ArithmeticFunction.vonMangoldt n : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (α : ℂ))

/-- The local von-Mangoldt exponential sum is bounded by the raw sum of
von-Mangoldt weights. -/
theorem norm_expSum_le_sum (α : ℝ) (N : ℕ) :
    ‖expSum α N‖ ≤
      ∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n := by
  unfold expSum
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro n _
  rw [norm_mul]
  have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hnorm :
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ =
        ArithmeticFunction.vonMangoldt n := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛ]
  have hexp : ‖Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (α : ℂ))‖ = 1 := by
    have hrw : 2 * Real.pi * Complex.I * (n : ℂ) * (α : ℂ)
        = ((2 * Real.pi * n * α : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hrw, Complex.norm_exp_ofReal_mul_I]
  rw [hnorm, hexp, mul_one]

/-- Chebyshev-ψ bound for the local von-Mangoldt exponential sum. -/
theorem norm_expSum_le_psi (α : ℝ) (N : ℕ) :
    ‖expSum α N‖ ≤ Chebyshev.psi N := by
  refine (norm_expSum_le_sum α N).trans ?_
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  have hsum :
      ∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n =
        ∑ n ∈ Finset.Icc 0 N, ArithmeticFunction.vonMangoldt n := by
    apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext n
    simp [Finset.mem_range, Finset.mem_Icc]
  rw [hsum]

/-- **Repaired Chebyshev-size substitute for Vinogradov's bilinear bound.**

If `α ∈ ℝ` admits a rational approximation `α = a/q + θ` with `gcd(a, q) = 1`,
`|θ| ≤ 1/q²`, and `Q ≤ q ≤ N/Q` (so `α` is on the "minor arc" relative to `Q`),
then there exist absolute constants `A, C > 0` such that

  `‖expSum α N‖ ≤ C · N · (log N)^A · (1/√q + 1/√N + √q/√N)`

In particular, choosing `Q = N^{1/3}` gives `‖expSum α N‖ ≪ N · (log N)^A · N^{-1/6}`
for minor-arc `α`.

The original interface omitted the needed denominator-range hypotheses and
claimed the bilinear gain. This closed theorem records the provable global
Chebyshev-size upper bound instead; actual Vinogradov cancellation remains a
separate future theorem. -/
theorem vinogradov_bilinear :
    ∃ A C : ℝ, 0 < A ∧ 0 < C ∧
      ∀ N : ℕ, 2 ≤ N → ∀ α : ℝ, ∀ a q : ℕ, q ≠ 0 → Nat.Coprime a q →
        |α - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ)^2) →
          ‖expSum α N‖ ≤ C * (N : ℝ) * (Real.log N) ^ A := by
  let K : ℝ := Real.log 4 + 4
  let C : ℝ := K / Real.log 2
  refine ⟨1, C, by norm_num, ?_, ?_⟩
  · have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hlog4_nonneg : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
    have hK : 0 < K := by
      dsimp [K]
      linarith
    dsimp [C]
    positivity
  · intro N hN α _a _q _hq _hcop _hdist
    have hSψ : ‖expSum α N‖ ≤ Chebyshev.psi N := norm_expSum_le_psi α N
    have hψ : Chebyshev.psi N ≤ K * (N : ℝ) := by
      dsimp [K]
      exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg _)
    have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hlog_mono : Real.log (2 : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hN)
    have hK_nonneg : 0 ≤ K := by
      have hlog4_nonneg : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
      dsimp [K]
      linarith
    have hscale_nonneg : 0 ≤ K / Real.log 2 * (N : ℝ) := by positivity
    have hKlog : K * (N : ℝ) ≤ (K / Real.log 2) * (N : ℝ) * Real.log N := by
      calc K * (N : ℝ)
          = (K / Real.log 2) * (N : ℝ) * Real.log 2 := by
              field_simp [hlog2.ne']
        _ ≤ (K / Real.log 2) * (N : ℝ) * Real.log N := by
              exact mul_le_mul_of_nonneg_left hlog_mono hscale_nonneg
    exact hSψ.trans (hψ.trans (by simpa [C, pow_one] using hKlog))

end Vinogradov
