/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import PrimeNumberTheoremAnd.Wiener

/-!
# A Wiener--Ikehara bridge for prime-ideal counting

This file packages the form of Wiener--Ikehara used in the analytic proof of
the prime ideal theorem.  Its hypotheses deliberately expose the two inputs
that must be supplied by the number-field development: absolute convergence
to the right of `1`, and a continuous extension of the pole-subtracted
Dirichlet series to `re s ≥ 1`.

The strict partial sum `∑ n < N, f n` is `cumsum f N` in the source theorem.
-/

namespace Erdos980.NaturalChebotarev.PrimeIdealTheorem

open Asymptotics BigOperators Filter Set LSeries
open scoped Topology

noncomputable section

variable {f : ℕ → ℝ} {A : ℝ} {G : ℂ → ℂ}

/-- Wiener--Ikehara for a nonnegative real arithmetic sequence, in the ratio
form used directly by weighted prime-ideal counting. -/
theorem wienerIkehara_cumsum_div_tendsto
    (hpos : 0 ≤ f)
    (hsummable : ∀ σ : ℝ, 1 < σ →
      Summable (nterm (fun n ↦ (f n : ℂ)) σ))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G
      (fun s ↦ LSeries (fun n ↦ (f n : ℂ)) s - A / (s - 1))
      {s | 1 < s.re}) :
    Tendsto (fun N : ℕ ↦ cumsum f N / (N : ℝ)) atTop (𝓝 A) :=
  WienerIkeharaTheorem'' hpos hsummable hG hG'

/-- The same bridge with the strict finite sum written out explicitly. -/
theorem wienerIkehara_sum_range_div_tendsto
    (hpos : 0 ≤ f)
    (hsummable : ∀ σ : ℝ, 1 < σ →
      Summable (nterm (fun n ↦ (f n : ℂ)) σ))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G
      (fun s ↦ LSeries (fun n ↦ (f n : ℂ)) s - A / (s - 1))
      {s | 1 < s.re}) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.range N, f n) / (N : ℝ))
      atTop (𝓝 A) := by
  simpa only [cumsum] using
    wienerIkehara_cumsum_div_tendsto hpos hsummable hG hG'

/-- If the residue is nonzero, the ratio form of Wiener--Ikehara is equivalent
to the usual asymptotic statement for strict partial sums. -/
theorem wienerIkehara_sum_range_isEquivalent
    (hpos : 0 ≤ f)
    (hsummable : ∀ σ : ℝ, 1 < σ →
      Summable (nterm (fun n ↦ (f n : ℂ)) σ))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G
      (fun s ↦ LSeries (fun n ↦ (f n : ℂ)) s - A / (s - 1))
      {s | 1 < s.re})
    (hA : A ≠ 0) :
    (fun N : ℕ ↦ ∑ n ∈ Finset.range N, f n) ~[atTop]
      (fun N : ℕ ↦ A * (N : ℝ)) := by
  have hden : ∀ᶠ N : ℕ in atTop, A * (N : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact mul_ne_zero hA (Nat.cast_ne_zero.mpr (by omega))
  apply (isEquivalent_iff_tendsto_one hden).2
  have hnormalized :=
    wienerIkehara_sum_range_div_tendsto hpos hsummable hG hG'
  have hratio :
      Tendsto
        (fun N : ℕ ↦ ((∑ n ∈ Finset.range N, f n) / (N : ℝ)) / A)
        atTop (𝓝 (A / A)) :=
    hnormalized.div_const A
  have hratio' :
      Tendsto
        (fun N : ℕ ↦ ((∑ n ∈ Finset.range N, f n) / (N : ℝ)) / A)
        atTop (𝓝 1) := by
    simpa [hA] using hratio
  convert hratio' using 1
  funext N
  simp only [Pi.div_apply, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The strict real-cutoff sum.  The use of `Nat.ceil` makes its summation
condition exactly `n < x`, including when `x` is not an integer. -/
def strictCumulative (f : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range ⌈x⌉₊, f n

@[simp] theorem strictCumulative_natCast (f : ℕ → ℝ) (N : ℕ) :
    strictCumulative f N = ∑ n ∈ Finset.range N, f n := by
  simp [strictCumulative]

/-- Real-endpoint Wiener--Ikehara for the strict sum `∑ n < x, f n`. -/
theorem wienerIkehara_strictCumulative_div_tendsto
    (hpos : 0 ≤ f)
    (hsummable : ∀ σ : ℝ, 1 < σ →
      Summable (nterm (fun n ↦ (f n : ℂ)) σ))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G
      (fun s ↦ LSeries (fun n ↦ (f n : ℂ)) s - A / (s - 1))
      {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ strictCumulative f x / x) atTop (𝓝 A) := by
  have hnat := wienerIkehara_sum_range_div_tendsto hpos hsummable hG hG'
  have hcomp :
      Tendsto
        (fun x : ℝ ↦
          (∑ n ∈ Finset.range ⌈x⌉₊, f n) / (⌈x⌉₊ : ℝ))
        atTop (𝓝 A) :=
    hnat.comp tendsto_nat_ceil_atTop
  have hprod := hcomp.mul (tendsto_nat_ceil_div_atTop (R := ℝ))
  have heq :
      (fun x : ℝ ↦ strictCumulative f x / x) =ᶠ[atTop]
        fun x : ℝ ↦
          ((∑ n ∈ Finset.range ⌈x⌉₊, f n) / (⌈x⌉₊ : ℝ)) *
            ((⌈x⌉₊ : ℝ) / x) := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hceil : (⌈x⌉₊ : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ceil_pos.mpr hx).ne'
    simp only [strictCumulative]
    field_simp
  simpa using hprod.congr' heq.symm

/-- Asymptotic-equivalence form of the real strict-cutoff bridge. -/
theorem wienerIkehara_strictCumulative_isEquivalent
    (hpos : 0 ≤ f)
    (hsummable : ∀ σ : ℝ, 1 < σ →
      Summable (nterm (fun n ↦ (f n : ℂ)) σ))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G
      (fun s ↦ LSeries (fun n ↦ (f n : ℂ)) s - A / (s - 1))
      {s | 1 < s.re})
    (hA : A ≠ 0) :
    strictCumulative f ~[atTop] (fun x : ℝ ↦ A * x) := by
  have hden : ∀ᶠ x : ℝ in atTop, A * x ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    exact mul_ne_zero hA hx.ne'
  apply (isEquivalent_iff_tendsto_one hden).2
  have hnormalized :=
    wienerIkehara_strictCumulative_div_tendsto hpos hsummable hG hG'
  have hratio :
      Tendsto (fun x : ℝ ↦ (strictCumulative f x / x) / A)
        atTop (𝓝 (A / A)) :=
    hnormalized.div_const A
  have hratio' :
      Tendsto (fun x : ℝ ↦ (strictCumulative f x / x) / A)
        atTop (𝓝 1) := by
    simpa [hA] using hratio
  convert hratio' using 1
  funext x
  simp only [Pi.div_apply, div_eq_mul_inv, mul_inv_rev]
  ring

end

end Erdos980.NaturalChebotarev.PrimeIdealTheorem
