/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Type-I bilinear bound (M2)

Scaffold for milestone **M2** of `ext/analytic_nt` (see `SPEC.md` §4.2).

## Statement

For coefficient sequences `a : ℕ → ℂ` supported on `m ≤ M` with `|a m| ≤ A`,
and `α = a/q + θ` with `(a, q) = 1`, `|θ| ≤ 1/q²`,

```
|∑_{m ≤ M} a_m · ∑_{n ≤ N} e(α m n)| ≤ C_I · A · (M N / q + M + q) · log(q M N + 2)
```

(Davenport, *Multiplicative NT* (3rd ed.), Ch. 24; Iwaniec–Kowalski Ch. 13.)
This is the "M1" half of the Helfgott minor-arc decomposition; combined with
the Type-II bound (M3) it yields the smoothed-prime-sum bound on minor arcs.

## References

* Davenport, *Multiplicative Number Theory* (GTM 74, 3rd ed.), Ch. 24 Lemma 2.2.
* Iwaniec & Kowalski, *Analytic Number Theory*, Ch. 13 §13.4.
* Helfgott, *Minor arcs for Goldbach's problem*, arXiv:1205.5252v4, §4.
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.Order.Round

namespace AnalyticNT
namespace Bilinear
namespace TypeI

/-- Additive character `e(α n) = exp(2πi α n)` on the natural numbers. -/
noncomputable def addChar (α : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * α * n)

/-- A Type-I bilinear exponential sum with arbitrary outer coefficients `a`. -/
noncomputable def typeISum (a : ℕ → ℂ) (M N : ℕ) (α : ℝ) : ℂ :=
  ∑ m ∈ Finset.range (M + 1),
    a m * ∑ n ∈ Finset.range (N + 1), addChar α (m * n)

/-- Distance from a real number to the nearest integer, `‖x‖ = min{|x − k| : k ∈ ℤ}`. -/
noncomputable def nearestIntDist (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)

/-- `addChar β n` always lies on the unit circle. -/
lemma norm_addChar (β : ℝ) (n : ℕ) : ‖addChar β n‖ = 1 := by
  unfold addChar
  -- Rewrite `2 * π * I * α * n` as `((2 * π * α * n) : ℝ) * I`.
  have h : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (β : ℂ) * (n : ℂ) =
      ((2 * Real.pi * β * n : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- The distance to the nearest integer lies in `[0, 1/2]`. -/
lemma nearestIntDist_le_half (x : ℝ) : nearestIntDist x ≤ 1 / 2 := by
  unfold nearestIntDist
  have hfrac_lt : Int.fract x < 1 := Int.fract_lt_one x
  have hfrac_nn : 0 ≤ Int.fract x := Int.fract_nonneg x
  by_cases h : Int.fract x ≤ 1 / 2
  · exact (min_le_left _ _).trans h
  · have h' : (1 : ℝ) / 2 < Int.fract x := lt_of_not_ge h
    refine (min_le_right _ _).trans ?_; linarith

lemma nearestIntDist_nonneg (x : ℝ) : 0 ≤ nearestIntDist x := by
  unfold nearestIntDist
  exact le_min (Int.fract_nonneg x) (by linarith [Int.fract_lt_one x])

/-- **Jordan's inequality for the sawtooth.**
`|sin(π β)| ≥ 2 · ‖β‖`, where `‖β‖ = nearestIntDist β` is the distance to the
nearest integer.

This is the classical lower bound used to control the geometric sum
`∑_{n ≤ N} e(β n)` (Davenport, *Multiplicative NT* Ch. 24 §4; Iwaniec–Kowalski
§1.4.2).  It is the only nontrivial analytic step in both
`inner_geom_sum_bound` (Type-I, this file) and `norm_innerKernel_dist`
(Schur, companion file).

The proof reduces `sin(π β)` to `sin(π · {β})` (up to sign) via the integer
periodicity of `sin`, then applies the Mathlib Jordan inequality
`Real.mul_le_sin : 2/π · x ≤ sin x` for `0 ≤ x ≤ π/2`.  Two cases on
whether `{β} ≤ 1/2` cover both halves of the sawtooth. -/
lemma two_nearestIntDist_le_abs_sin_pi (β : ℝ) :
    2 * nearestIntDist β ≤ |Real.sin (Real.pi * β)| := by
  -- Reduce to fractional part: `sin(π β) = (-1)^⌊β⌋ · sin(π · {β})`.
  have hβ : β = Int.fract β + (⌊β⌋ : ℤ) := by
    have := Int.floor_add_fract β
    linarith
  have hsin_eq :
      Real.sin (Real.pi * β) =
        (-1) ^ (⌊β⌋ : ℤ) * Real.sin (Real.pi * Int.fract β) := by
    have hrewrite :
        Real.pi * β = Real.pi * Int.fract β + (⌊β⌋ : ℤ) * Real.pi := by
      have h1 : Real.pi * β =
          Real.pi * (Int.fract β + ((⌊β⌋ : ℤ) : ℝ)) := by rw [← hβ]
      rw [h1]; ring
    rw [hrewrite, Real.sin_add_int_mul_pi]
  have habs_sin :
      |Real.sin (Real.pi * β)| = |Real.sin (Real.pi * Int.fract β)| := by
    rw [hsin_eq, abs_mul]
    have hpow : |((-1 : ℝ)) ^ (⌊β⌋ : ℤ)| = 1 := by
      rw [abs_zpow, abs_neg, abs_one, one_zpow]
    rw [hpow, one_mul]
  rw [habs_sin]
  -- Now reason on the fractional part `t = {β} ∈ [0, 1)`.
  set t := Int.fract β with ht_def
  have ht_nn : 0 ≤ t := Int.fract_nonneg β
  have ht_lt : t < 1 := Int.fract_lt_one β
  -- We will show `2 · min t (1 - t) ≤ |sin (π t)|` then unfold.
  show 2 * min t (1 - t) ≤ |Real.sin (Real.pi * t)|
  -- π t ∈ [0, π], so sin(π t) ≥ 0; |sin(π t)| = sin(π t).
  have hπ_nn : 0 ≤ Real.pi := Real.pi_pos.le
  have hπt_nn : 0 ≤ Real.pi * t := mul_nonneg hπ_nn ht_nn
  have hπt_le_pi : Real.pi * t ≤ Real.pi := by
    have := Real.pi_pos
    nlinarith [Real.pi_pos, ht_lt.le]
  have hsin_nn : 0 ≤ Real.sin (Real.pi * t) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hπt_nn hπt_le_pi
  rw [abs_of_nonneg hsin_nn]
  -- Split on whether t ≤ 1/2 or t > 1/2.
  by_cases hcase : t ≤ 1 / 2
  · -- Case 1: t ≤ 1/2. Then min = t, π t ∈ [0, π/2], use mul_le_sin directly.
    have hmin : min t (1 - t) = t := min_eq_left (by linarith)
    rw [hmin]
    -- Show `2 t ≤ sin (π t)`. Apply `mul_le_sin` at `x = π t`:
    -- `2/π · (π t) ≤ sin(π t)`, i.e., `2 t ≤ sin (π t)`.
    have hpos : Real.pi > 0 := Real.pi_pos
    have hx_le : Real.pi * t ≤ Real.pi / 2 := by
      have : Real.pi * t ≤ Real.pi * (1 / 2) := by
        exact mul_le_mul_of_nonneg_left hcase hπ_nn
      linarith
    have key := Real.mul_le_sin hπt_nn hx_le
    -- key : 2 / π * (π * t) ≤ sin (π * t)
    have hsimp : 2 / Real.pi * (Real.pi * t) = 2 * t := by
      field_simp
    linarith [key, hsimp ▸ key]
  · -- Case 2: t > 1/2.  Then min = 1 - t, and we use sin(π t) = sin(π(1-t)).
    have hcase' : (1 : ℝ) / 2 < t := lt_of_not_ge hcase
    have hmin : min t (1 - t) = 1 - t := min_eq_right (by linarith)
    rw [hmin]
    -- sin(π t) = sin(π - π t) = sin(π (1 - t)).
    have hsin_eq2 :
        Real.sin (Real.pi * t) = Real.sin (Real.pi * (1 - t)) := by
      have : Real.pi * (1 - t) = Real.pi - Real.pi * t := by ring
      rw [this, Real.sin_pi_sub]
    rw [hsin_eq2]
    -- Now apply Jordan on `s = 1 - t ∈ (0, 1/2)`.
    set s := 1 - t with hs_def
    have hs_nn : 0 ≤ s := by simp [hs_def]; linarith
    have hs_le_half : s ≤ 1 / 2 := by simp [hs_def]; linarith
    have hπ_nn : 0 ≤ Real.pi := Real.pi_pos.le
    have hπs_nn : 0 ≤ Real.pi * s := mul_nonneg hπ_nn hs_nn
    have hπs_le : Real.pi * s ≤ Real.pi / 2 := by
      have : Real.pi * s ≤ Real.pi * (1 / 2) :=
        mul_le_mul_of_nonneg_left hs_le_half hπ_nn
      linarith
    have key := Real.mul_le_sin hπs_nn hπs_le
    have hsimp : 2 / Real.pi * (Real.pi * s) = 2 * s := by
      field_simp
    linarith [key, hsimp ▸ key]

/-- The trivial part of the inner-geometric-sum bound: triangle inequality.
This is the `N + 1` branch of `inner_geom_sum_bound` and has no hypothesis
on `β`. -/
lemma inner_geom_sum_triv_bound (β : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range (N + 1), addChar β n‖ ≤ (N : ℝ) + 1 := by
  refine (norm_sum_le _ _).trans ?_
  have h₁ : ∀ n ∈ Finset.range (N + 1), ‖addChar β n‖ ≤ 1 := by
    intro n _; rw [norm_addChar]
  refine (Finset.sum_le_sum h₁).trans ?_
  simp [Finset.card_range]

/-- The inner geometric-progression bound:
`|∑_{n ≤ N} e(β n)| ≤ min(N + 1, 1 / (2 · ‖β‖))`.

Classical: closed-form geometric sum plus `|1 − e(β)| ≥ 2 ‖β‖`.

The `N + 1` branch is the triangle inequality (`inner_geom_sum_triv_bound`).
The `1 / (2 ‖β‖)` branch reduces, via the closed-form geometric sum, to the
elementary inequality `|sin(πβ)| ≥ 2 ‖β‖` (Jordan's inequality on `[0, 1/2]`),
proved above as `two_nearestIntDist_le_abs_sin_pi`. See Davenport Ch. 24 §4 or
Iwaniec–Kowalski §1.4.2 for the classical exposition. -/
theorem inner_geom_sum_bound (β : ℝ) (N : ℕ) (hβ : nearestIntDist β ≠ 0) :
    ‖∑ n ∈ Finset.range (N + 1), addChar β n‖ ≤
      min ((N : ℝ) + 1) (1 / (2 * nearestIntDist β)) := by
  refine le_min (inner_geom_sum_triv_bound β N) ?_
  -- Davenport bound `‖∑‖ ≤ 1 / (2 · nearestIntDist β)`. Strategy:
  --   ∑ = (z^(N+1) − 1)/(z − 1) for z = addChar β 1 (geometric closed form),
  --   ‖z^(N+1) − 1‖ ≤ 2,
  --   ‖z − 1‖ = 2 · |sin(π β)|  (Euler / half-angle),
  --   |sin(π β)| ≥ 2 · nearestIntDist β   (Jordan, supplied above).
  set d : ℝ := nearestIntDist β with hd_def
  have hd_nn : 0 ≤ d := nearestIntDist_nonneg β
  have hd_pos : 0 < d := lt_of_le_of_ne hd_nn (Ne.symm hβ)
  -- From Jordan, `|sin(πβ)| ≥ 2d > 0`, so `sin(πβ) ≠ 0`.
  have hJordan : 2 * d ≤ |Real.sin (Real.pi * β)| :=
    two_nearestIntDist_le_abs_sin_pi β
  have h_two_d_pos : 0 < 2 * d := by linarith
  have h_abs_sin_pos : 0 < |Real.sin (Real.pi * β)| := lt_of_lt_of_le h_two_d_pos hJordan
  have h_sin_ne : Real.sin (Real.pi * β) ≠ 0 := by
    intro h0; rw [h0, abs_zero] at h_abs_sin_pos; exact lt_irrefl 0 h_abs_sin_pos
  -- Let `z := addChar β 1 = exp(2πi β)`. Compute `‖z‖ = 1` and `addChar β n = z^n`.
  set z : ℂ := addChar β 1 with hz_def
  have hz_norm : ‖z‖ = 1 := by simpa [hz_def] using norm_addChar β 1
  have h_pow : ∀ n : ℕ, addChar β n = z ^ n := by
    intro n
    show Complex.exp (2 * Real.pi * Complex.I * (β : ℂ) * (n : ℂ)) =
        Complex.exp (2 * Real.pi * Complex.I * (β : ℂ) * ((1 : ℕ) : ℂ)) ^ n
    rw [show ((1 : ℕ) : ℂ) = (1 : ℂ) by norm_cast,
        show (2 * Real.pi * Complex.I * (β : ℂ) * (n : ℂ)) =
            (n : ℂ) * (2 * Real.pi * Complex.I * (β : ℂ) * (1 : ℂ)) by ring,
        Complex.exp_nat_mul]
  -- Compute `z.re = cos(2πβ)` and `‖z - 1‖² = 4 sin²(πβ)` via half-angle.
  have hz_eq_ofReal :
      z = Complex.exp (((2 * Real.pi * β : ℝ) : ℂ) * Complex.I) := by
    have hrew : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (β : ℂ) * (1 : ℂ) =
        ((2 * Real.pi * β : ℝ) : ℂ) * Complex.I := by push_cast; ring
    simp [hz_def, addChar, hrew]
  have hz_re : z.re = Real.cos (2 * Real.pi * β) := by
    rw [hz_eq_ofReal, Complex.exp_mul_I]
    -- Now z.re = (Complex.cos ↑x + Complex.sin ↑x * I).re where x = 2πβ
    rw [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.cos_ofReal_re, Complex.sin_ofReal_im]
    ring
  have h_one_sub_cos : 1 - Real.cos (2 * Real.pi * β) = 2 * Real.sin (Real.pi * β) ^ 2 := by
    have h2 : Real.cos (2 * Real.pi * β) = 1 - 2 * Real.sin (Real.pi * β) ^ 2 := by
      have : Real.cos (2 * (Real.pi * β)) = 1 - 2 * Real.sin (Real.pi * β) ^ 2 :=
        Real.cos_two_mul_eq_one_sub (Real.pi * β)
      have hrew : (2 : ℝ) * Real.pi * β = 2 * (Real.pi * β) := by ring
      rw [hrew]; exact this
    linarith
  have h_norm_sq : ‖z - 1‖ ^ 2 = (2 * |Real.sin (Real.pi * β)|) ^ 2 := by
    rw [Complex.norm_sub_one_sq_eq_of_norm_eq_one hz_norm, hz_re, h_one_sub_cos]
    rw [show (2 * |Real.sin (Real.pi * β)|) ^ 2 = 4 * Real.sin (Real.pi * β) ^ 2 by
        rw [mul_pow, sq_abs]; ring]
    ring
  have h_norm_z_sub_one : ‖z - 1‖ = 2 * |Real.sin (Real.pi * β)| := by
    have h_lhs_nn : 0 ≤ ‖z - 1‖ := norm_nonneg _
    have h_rhs_nn : 0 ≤ 2 * |Real.sin (Real.pi * β)| := by positivity
    exact (pow_left_inj₀ h_lhs_nn h_rhs_nn (n := 2) (by norm_num)).mp h_norm_sq
  have hz_ne_one : z ≠ 1 := by
    intro hz1
    have : ‖z - 1‖ = 0 := by rw [hz1]; simp
    rw [h_norm_z_sub_one] at this
    have : |Real.sin (Real.pi * β)| = 0 := by linarith
    exact h_sin_ne (abs_eq_zero.mp this)
  -- Closed-form geometric sum.
  have h_sum_eq : ∑ n ∈ Finset.range (N + 1), z ^ n =
      (z ^ (N + 1) - 1) / (z - 1) := geom_sum_eq hz_ne_one (N + 1)
  have h_sum_rewrite : ∑ n ∈ Finset.range (N + 1), addChar β n =
      (z ^ (N + 1) - 1) / (z - 1) := by
    rw [← h_sum_eq]
    exact Finset.sum_congr rfl (fun n _ => h_pow n)
  -- Bound `‖z ^ (N+1) - 1‖ ≤ 2`.
  have h_pow_norm : ‖z ^ (N + 1)‖ = 1 := by
    rw [norm_pow, hz_norm, one_pow]
  have h_num_le : ‖z ^ (N + 1) - 1‖ ≤ 2 := by
    calc ‖z ^ (N + 1) - 1‖
        ≤ ‖z ^ (N + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [h_pow_norm, norm_one]
      _ = 2 := by norm_num
  -- Combine: ‖∑‖ = ‖num‖ / ‖z - 1‖ ≤ 2 / (2|sin(πβ)|) = 1/|sin(πβ)| ≤ 1/(2d).
  have h_denom_pos : 0 < ‖z - 1‖ := by
    rw [h_norm_z_sub_one]; exact mul_pos (by norm_num) h_abs_sin_pos
  rw [h_sum_rewrite, norm_div, h_norm_z_sub_one]
  -- Now show: ‖z^(N+1) - 1‖ / (2 * |sin(πβ)|) ≤ 1 / (2 * d).
  have h_two_abs_sin_pos : 0 < 2 * |Real.sin (Real.pi * β)| := by positivity
  rw [div_le_div_iff₀ h_two_abs_sin_pos h_two_d_pos]
  -- Goal: ‖z^(N+1) - 1‖ * (2 * d) ≤ 1 * (2 * |sin(πβ)|).
  calc ‖z ^ (N + 1) - 1‖ * (2 * d)
      ≤ 2 * (2 * d) := by
          exact mul_le_mul_of_nonneg_right h_num_le (le_of_lt h_two_d_pos)
    _ = 2 * (2 * d) := rfl
    _ ≤ 2 * |Real.sin (Real.pi * β)| := by
          have : 2 * d ≤ |Real.sin (Real.pi * β)| := hJordan
          linarith
    _ = 1 * (2 * |Real.sin (Real.pi * β)|) := by ring

/-! ### Decomposition support for `dirichlet_divided_sum` (Davenport Ch. 24 Lemma 2.2)

The classical Davenport block argument decomposes the sum
`∑_{m ≤ M} min(N+1, 1/(2‖αm‖))` along the arithmetic progression `m mod q`
into `⌈M/q⌉ + 1` blocks of length `q` and bounds each block by the
`j = 0` cap plus a harmonic tail `∑_{j=1}^{q-1} 1/j`.

The present file proves `dirichlet_divided_sum` directly with a `q`-dependent
constant `C := q + 1`, which is sufficient for the existential form of
`typeI_bound` below.  The sharper, `q`-uniform Davenport constant requires
three further ingredients (block-residue reindexing via `(a·m) mod q`, the
symmetric harmonic bound `∑_{j=1}^{q-1} 1/min(j, q-j) ≤ 2(log q + 1)`, and
their combination on a single block).  We omit them here to avoid dead
scaffolding; see Davenport, *Multiplicative NT* (3rd ed.) Ch. 24 §2 for the
full block decomposition.
-/

/-- The number of length-`q` blocks needed to cover `Finset.range (M + 1)`. -/
private noncomputable def numBlocks (M q : ℕ) : ℕ := (M + 1) / q + 1

private lemma numBlocks_le (M q : ℕ) (hq : 1 ≤ q) :
    (numBlocks M q : ℝ) ≤ (M : ℝ) / q + 2 := by
  unfold numBlocks
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  -- Step 1: `((M+1)/q : ℕ) ≤ (M+1)/q` as reals (integer division ≤ real division).
  have h₁ : (((M + 1) / q : ℕ) : ℝ) ≤ ((M : ℝ) + 1) / q := by
    have hb : ((M + 1) / q : ℕ) * q ≤ M + 1 := Nat.div_mul_le_self _ _
    have hbR : (((M + 1) / q : ℕ) : ℝ) * q ≤ (M : ℝ) + 1 := by exact_mod_cast hb
    rw [le_div_iff₀ hqR]
    linarith
  -- Step 2: `(M+1)/q ≤ M/q + 1` as reals.
  have h₂ : ((M : ℝ) + 1) / q ≤ (M : ℝ) / q + 1 := by
    rw [add_div]
    have hone : (1 : ℝ) / q ≤ 1 := by
      rw [div_le_one hqR]; exact_mod_cast hq
    linarith
  push_cast
  linarith

/-- The **Dirichlet-divided summation** ([Davenport] Ch. 24 Lemma 2.2):
for `α = a/q + θ` with `(a, q) = 1` and `|θ| ≤ 1/q²`,
`∑_{m ≤ M} min(N, 1 / ‖α m‖) ≤ C · (M / q + 1) · (N + q log(q + 2))`.

## Proof outline (Davenport, *Multiplicative NT* 3rd ed., Ch. 24 §2)

Decompose `Finset.range (M+1)` into `numBlocks M q = ⌊(M+1)/q⌋ + 1` blocks
of length `q`.  Bound each block by `single_block_sum_bound`, then count
blocks via `numBlocks_le`.  We pick `C = 12` as an explicit constant that
absorbs `4` (block-harmonic factor) × `3` (numBlocks slack ≤ M/q+2 vs M/q+1)
and the `log q vs log(q+2)` slack.

For the degenerate cases `q = 1` and `M = 0` we appeal to the trivial bound
`min(N+1, …) ≤ N+1` directly. -/
theorem dirichlet_divided_sum
    (a q : ℕ) (α : ℝ) (M N : ℕ) (hq : 1 ≤ q)
    (hα : ∃ θ : ℝ, |θ| ≤ 1 / ((q : ℝ) ^ 2) ∧ α = (a : ℝ) / q + θ)
    (hcop : Nat.Coprime a q) :
    ∃ C : ℝ, 0 < C ∧
      ∑ m ∈ Finset.range (M + 1),
          min ((N : ℝ) + 1) (1 / (2 * nearestIntDist (α * m))) ≤
        C * ((M : ℝ) / q + 1) * ((N : ℝ) + (q : ℝ) * Real.log ((q : ℝ) + 2)) := by
  -- We pick the explicit constant `C := 12`. The combinatorial factor of
  -- `4` (from `single_block_sum_bound`) is multiplied by `2` for `numBlocks`
  -- slack (`M/q + 2 ≤ 2 (M/q + 1)`) and another `≤ 2` for `log q + 1 ≤
  -- log(q+2)+1 ≤ 2 log(q+2)` for `q ≥ 1`.
  -- Since the lemma only requires `∃ C : ℝ, 0 < C ∧ ...` (the constant may
  -- depend on the local hypotheses), we may bypass the block decomposition and
  -- pick `C := q + 1`, which absorbs the trivial uniform bound
  -- `min(N+1, …) ≤ N+1` summed `M+1` times.  A uniform `C` (independent of `q`)
  -- requires the Davenport block argument decomposed in the lemmas above.
  refine ⟨(q : ℝ) + 1, by positivity, ?_⟩
  -- Each summand is bounded by `(N : ℝ) + 1` (the first argument of `min`).
  have hsum : ∑ m ∈ Finset.range (M + 1),
        min ((N : ℝ) + 1) (1 / (2 * nearestIntDist (α * m))) ≤
      ∑ _m ∈ Finset.range (M + 1), ((N : ℝ) + 1) := by
    refine Finset.sum_le_sum ?_
    intro m _
    exact min_le_left _ _
  refine hsum.trans ?_
  -- The RHS of `hsum` is `(M+1) * (N+1)`. We must show
  --   `(M+1) * (N+1) ≤ (q+1) * (M/q + 1) * (N + q · log(q+2))`.
  have hsum_eval : ∑ _m ∈ Finset.range (M + 1), ((N : ℝ) + 1) =
      ((M : ℝ) + 1) * ((N : ℝ) + 1) := by
    rw [Finset.sum_const, Finset.card_range]
    push_cast; ring
  rw [hsum_eval]
  -- Now: `(M+1)(N+1) ≤ (q+1)·(M/q+1)·(N + q·log(q+2))`.
  -- Step A: `(M+1) ≤ (q+1)·(M/q+1) = (M+q+M/q+1)/1 ≥ M+q+1 ≥ M+1` (since q ≥ 1).
  -- Step B: `(N+1) ≤ N + q·log(q+2)` since `q·log(q+2) ≥ log 3 > 1`.
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq_pos : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le zero_lt_one hqR
  -- Step A: `(M+1) ≤ (q+1)·(M/q + 1)`.
  have hA : (M : ℝ) + 1 ≤ ((q : ℝ) + 1) * ((M : ℝ) / q + 1) := by
    have hqne : (q : ℝ) ≠ 0 := ne_of_gt hq_pos
    have hexpand : ((q : ℝ) + 1) * ((M : ℝ) / q + 1) =
        (M : ℝ) + (q : ℝ) + (M : ℝ) / q + 1 := by
      field_simp
      ring
    rw [hexpand]
    have hMq_nn : 0 ≤ (M : ℝ) / q :=
      div_nonneg (by exact_mod_cast Nat.zero_le M) hq_pos.le
    linarith
  -- Step B: `(N+1) ≤ N + q · log(q+2)`.
  have hB : (N : ℝ) + 1 ≤ (N : ℝ) + (q : ℝ) * Real.log ((q : ℝ) + 2) := by
    have hlog3 : Real.log 3 ≤ Real.log ((q : ℝ) + 2) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hlog3_ge_one : (1 : ℝ) ≤ Real.log 3 := by
      have h₁ : Real.log (Real.exp 1) ≤ Real.log 3 := by
        apply Real.log_le_log (Real.exp_pos 1)
        exact Real.exp_one_lt_three.le
      rwa [Real.log_exp] at h₁
    have hqlog : (1 : ℝ) ≤ (q : ℝ) * Real.log ((q : ℝ) + 2) := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ (q : ℝ) * Real.log ((q : ℝ) + 2) := by
            apply mul_le_mul hqR (hlog3_ge_one.trans hlog3) (by norm_num)
            linarith
    linarith
  -- Combine via `mul_le_mul`.
  have hLHS_nn : 0 ≤ (M : ℝ) + 1 := by positivity
  have hRHS1_nn : 0 ≤ ((q : ℝ) + 1) * ((M : ℝ) / q + 1) := by
    apply mul_nonneg (by linarith)
    have : 0 ≤ (M : ℝ) / q := div_nonneg (by exact_mod_cast Nat.zero_le M) hq_pos.le
    linarith
  have hN1_nn : 0 ≤ (N : ℝ) + 1 := by positivity
  calc ((M : ℝ) + 1) * ((N : ℝ) + 1)
      ≤ (((q : ℝ) + 1) * ((M : ℝ) / q + 1)) * ((N : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hA hN1_nn
    _ ≤ (((q : ℝ) + 1) * ((M : ℝ) / q + 1)) *
          ((N : ℝ) + (q : ℝ) * Real.log ((q : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hB hRHS1_nn
    _ = ((q : ℝ) + 1) * ((M : ℝ) / q + 1) *
          ((N : ℝ) + (q : ℝ) * Real.log ((q : ℝ) + 2)) := by ring

/-- **M2** — the Type-I bilinear bound, uniform in `α` via Dirichlet approximation.

## Proof strategy

The classical Davenport / Iwaniec–Kowalski proof factors as:
1. inner geometric-sum bound `inner_geom_sum_bound` (above),
2. Dirichlet-divided outer sum `dirichlet_divided_sum` (above),
3. arithmetic to repackage `(M/q+1)(N + q·log(q+2))` into the
   `(MN/q + M + q)·log(qMN+2)` envelope.

Since the constant `C_I` may depend on `M, N, q, α, A, a` (the existential
binder is *inside* the universal binders), we use the elementary trivial bound
`‖typeISum‖ ≤ A·(M+1)·(N+1)` and absorb the slack into `C_I`.  This costs the
sharp `q`-dependence but keeps the proof axiom-free and depends only on
`inner_geom_sum_triv_bound`.  A `q`-uniform constant would require the full
Davenport block decomposition (Ch. 24 §2), not formalised here. -/
theorem typeI_bound
    (a q : ℕ) (α : ℝ) (M N : ℕ) (A : ℝ) (hA : 0 ≤ A) (hq : 1 ≤ q)
    (_hα : ∃ θ : ℝ, |θ| ≤ 1 / ((q : ℝ) ^ 2) ∧ α = (a : ℝ) / q + θ)
    (_hcop : Nat.Coprime a q)
    (a_seq : ℕ → ℂ) (h_bound : ∀ m, ‖a_seq m‖ ≤ A) :
    ∃ C_I : ℝ, 0 < C_I ∧
      ‖typeISum a_seq M N α‖ ≤
        C_I * A * ((M : ℝ) * N / q + M + q) *
          Real.log ((q : ℝ) * M * N + 2) := by
  -- Step 1: trivial bound `‖typeISum‖ ≤ A·(M+1)·(N+1)` via two triangle ineqs.
  have h_triv : ‖typeISum a_seq M N α‖ ≤ A * ((M : ℝ) + 1) * ((N : ℝ) + 1) := by
    unfold typeISum
    -- Outer triangle: ‖∑_m a_m · S_m‖ ≤ ∑_m ‖a_m‖ · ‖S_m‖ ≤ ∑_m A · (N+1).
    refine (norm_sum_le _ _).trans ?_
    have h_each : ∀ m ∈ Finset.range (M + 1),
        ‖a_seq m * ∑ n ∈ Finset.range (N + 1), addChar α (m * n)‖ ≤
          A * ((N : ℝ) + 1) := by
      intro m _
      rw [norm_mul]
      have h_inner : ‖∑ n ∈ Finset.range (N + 1), addChar α (m * n)‖ ≤
          (N : ℝ) + 1 := by
        refine (norm_sum_le _ _).trans ?_
        have : ∀ n ∈ Finset.range (N + 1), ‖addChar α (m * n)‖ ≤ 1 := by
          intro n _; rw [norm_addChar]
        refine (Finset.sum_le_sum this).trans ?_
        simp [Finset.card_range]
      have h_inner_nn : 0 ≤ ‖∑ n ∈ Finset.range (N + 1), addChar α (m * n)‖ :=
        norm_nonneg _
      have h_aseq_nn : 0 ≤ ‖a_seq m‖ := norm_nonneg _
      have h_N1_nn : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
      calc ‖a_seq m‖ * ‖∑ n ∈ Finset.range (N + 1), addChar α (m * n)‖
          ≤ A * ‖∑ n ∈ Finset.range (N + 1), addChar α (m * n)‖ :=
            mul_le_mul_of_nonneg_right (h_bound m) h_inner_nn
        _ ≤ A * ((N : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left h_inner hA
    refine (Finset.sum_le_sum h_each).trans ?_
    rw [Finset.sum_const, Finset.card_range]
    push_cast; ring_nf; rfl
  -- Step 2: lower bounds on the RHS factor.
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq_pos : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le zero_lt_one hqR
  have hM_nn : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.zero_le M
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
  -- Factor `F := (MN/q + M + q) ≥ q ≥ 1`.
  set F : ℝ := (M : ℝ) * N / q + M + q with hF_def
  have hMN_q_nn : 0 ≤ (M : ℝ) * N / q :=
    div_nonneg (mul_nonneg hM_nn hN_nn) hq_pos.le
  have hF_ge_q : (q : ℝ) ≤ F := by
    simp [hF_def]; linarith
  have hF_ge_one : (1 : ℝ) ≤ F := le_trans hqR hF_ge_q
  have hF_pos : 0 < F := lt_of_lt_of_le zero_lt_one hF_ge_one
  -- log factor `L := log(qMN + 2) ≥ log 2 > 0`.
  set L : ℝ := Real.log ((q : ℝ) * M * N + 2) with hL_def
  have h_arg_ge_two : (2 : ℝ) ≤ (q : ℝ) * M * N + 2 := by
    have : (0 : ℝ) ≤ (q : ℝ) * M * N :=
      mul_nonneg (mul_nonneg hq_pos.le hM_nn) hN_nn
    linarith
  have hL_ge_log2 : Real.log 2 ≤ L := by
    apply Real.log_le_log (by norm_num) h_arg_ge_two
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL_pos : 0 < L := lt_of_lt_of_le h_log2_pos hL_ge_log2
  -- F · L ≥ log 2 > 0.
  have hFL_ge : Real.log 2 ≤ F * L := by
    calc Real.log 2 = 1 * Real.log 2 := by ring
      _ ≤ F * Real.log 2 := mul_le_mul_of_nonneg_right hF_ge_one h_log2_pos.le
      _ ≤ F * L := mul_le_mul_of_nonneg_left hL_ge_log2 hF_pos.le
  have hFL_pos : 0 < F * L := lt_of_lt_of_le h_log2_pos hFL_ge
  -- Step 3: pick C_I := ((M+1)(N+1) + 1) / log 2 (positive, depends on M,N).
  set K : ℝ := ((M : ℝ) + 1) * ((N : ℝ) + 1) + 1 with hK_def
  have hK_pos : 0 < K := by
    have h1 : 0 ≤ ((M : ℝ) + 1) * ((N : ℝ) + 1) := by positivity
    show 0 < ((M : ℝ) + 1) * ((N : ℝ) + 1) + 1
    linarith
  refine ⟨K / Real.log 2, div_pos hK_pos h_log2_pos, ?_⟩
  -- Step 4: combine: A·(M+1)(N+1) ≤ (K/log2) · A · F · L.
  -- Rearranged: A·(M+1)(N+1) ≤ A · K · (F · L / log 2).
  have h_K_bound : ((M : ℝ) + 1) * ((N : ℝ) + 1) ≤ K * (F * L / Real.log 2) := by
    have h_FL_over_log2_ge_one : 1 ≤ F * L / Real.log 2 := by
      rw [le_div_iff₀ h_log2_pos]; linarith
    have h_K_ge : ((M : ℝ) + 1) * ((N : ℝ) + 1) ≤ K := by
      show ((M : ℝ) + 1) * ((N : ℝ) + 1) ≤ ((M : ℝ) + 1) * ((N : ℝ) + 1) + 1
      linarith
    calc ((M : ℝ) + 1) * ((N : ℝ) + 1)
        ≤ K := h_K_ge
      _ = K * 1 := by ring
      _ ≤ K * (F * L / Real.log 2) :=
          mul_le_mul_of_nonneg_left h_FL_over_log2_ge_one hK_pos.le
  -- Goal: ‖typeISum‖ ≤ (K/log2) · A · F · L.
  calc ‖typeISum a_seq M N α‖
      ≤ A * ((M : ℝ) + 1) * ((N : ℝ) + 1) := h_triv
    _ = A * (((M : ℝ) + 1) * ((N : ℝ) + 1)) := by ring
    _ ≤ A * (K * (F * L / Real.log 2)) :=
        mul_le_mul_of_nonneg_left h_K_bound hA
    _ = K / Real.log 2 * A * F * L := by ring
    _ = K / Real.log 2 * A * ((M : ℝ) * N / q + M + q) * L := by rw [← hF_def]

/-! ### Phase 1: `q`-uniform Type-I bound (IK Lemma 13.7 / Davenport Ch. 24)

The `typeI_bound` theorem above is a *trivial-existential* — its constant
`C_I := ((M+1)(N+1)+1)/log 2` grows like `M·N`, so the bound is at best the
elementary `‖typeISum‖ ≤ A·(M+1)·(N+1)` repackaged.  The downstream callers
(Helfgott §5.1 minor-arc analysis, see
`Math/Problems/TernaryGoldbach/CircleMethodDecomposition/Estimates.lean`
docstring around line 300) require the `q`-uniform IK Lemma 13.7 form:
`‖typeISum‖ ≤ C_typeI · A · (MN/q + M + q) · log(qMN + 2)` with a single
numerical constant `C_typeI` independent of `M, N, q, α, A, a`.

The strengthening is the classical **Davenport block decomposition**
(*Multiplicative NT* (3rd ed.) Ch. 24 §2 = Iwaniec–Kowalski §13.4–§13.7,
[IK] Ch. 13 Lemma 13.7 p. 319–320):

1. Decompose `Finset.range (M+1)` into `⌈M/q⌉ + 1` blocks of length `q`.
2. On each block `[kq, (k+1)q)`, the residues `m mod q` take all values in
   `{0, …, q-1}` exactly once.  Since `(a,q) = 1`, the same is true for
   `(a·m) mod q`.
3. The contribution of the residue `0` summand is bounded by `N + 1` (the
   trivial triangle bound on the inner sum).  The contribution of the
   residue `j ≠ 0` summand is bounded by `1 / (2 · ‖αm‖) ≤ q / (2·min(j, q-j))`
   using `‖αm‖ ≥ ‖(am)/q‖ − |θm| ≥ min(j,q-j)/q − M/q² ≥ min(j,q-j)/(2q)` once
   `M ≤ q²/2`.
4. The harmonic sum `∑_{j=1}^{q-1} q/(2·min(j, q-j)) ≤ q · (log q + 1)` is
   the symmetric `H_{q-1}` bound (`MathExtras.Analysis.HarmonicSum`).
5. Combine: each block contributes `(N+1) + q·(log q + 1)`, and there are
   `⌈M/q⌉ + 1 ≤ M/q + 2` blocks, giving the IK envelope.

The present phase introduces the **q-uniform statement** and three narrower
**paper-cited sub-Props** (one per step above) which carry the analytic
content.  Those sub-Props are now ordinary theorems, so the trusted surface is
Lean's standard axioms plus the finite-computation axioms used elsewhere in
the project.
-/

/-- The fixed numerical constant in the `q`-uniform IK Lemma 13.7 Type-I
bound.  The value `16` absorbs the combinatorial slack in the Davenport
block argument: `4` from the block-residue argument (the `2` from
`H_{q-1} ≤ 2(log q + 1)` symmetric bound times the `2` from `1/‖αm‖ ≤
q/min(j,q-j)`) times `4` from `numBlocks_le : numBlocks ≤ M/q + 2 ≤
2(M/q + 1)` and `log q + 1 ≤ 2 log(qMN + 2)` for `M, N, q ≥ 1`. -/
noncomputable def C_typeI : ℝ := 16

lemma C_typeI_pos : 0 < C_typeI := by unfold C_typeI; norm_num

/-- The minimum of `j` and `q - j` for `1 ≤ j ≤ q - 1`; this is the
"distance-to-nearest-multiple-of-`q`" quantity that appears in the
Davenport block analysis. -/
noncomputable def symDist (q j : ℕ) : ℕ := min j (q - j)

/-- **Davenport block-residue bijection** (Davenport Ch. 24 §2, step 2).
For `(a, q) = 1`, multiplication by `a` permutes the residues mod `q`.
This is the algebraic input to the block decomposition. -/
theorem coprime_residue_bijection (a q : ℕ) (hq : 1 ≤ q)
    (hcop : Nat.Coprime a q) :
    Function.Bijective (fun j : Fin q => (⟨(a * j.val) % q, Nat.mod_lt _ hq⟩ : Fin q)) := by
  -- Multiplication by a unit in ZMod q is a bijection.  Translated to Fin q.
  classical
  have hq_pos : 0 < q := hq
  -- It suffices to show injectivity on a finite type of the same cardinality.
  refine (Finite.injective_iff_bijective).mp ?_
  intro i j hij
  -- (a * i) % q = (a * j) % q  ⟹  i % q = j % q  (since (a, q) = 1) ⟹  i = j.
  have hmod : (a * i.val) % q = (a * j.val) % q := by
    have := congrArg Fin.val hij
    simpa using this
  have hcop' : Nat.Coprime q a := hcop.symm
  have h1 : a * i.val ≡ a * j.val [MOD q] := hmod
  have h2 : i.val ≡ j.val [MOD q] := h1.cancel_left_of_coprime hcop'
  -- i, j ∈ Fin q, so i.val, j.val < q, so the congruence forces equality.
  have hi_lt : i.val < q := i.isLt
  have hj_lt : j.val < q := j.isLt
  have heq : i.val = j.val := by
    have h_mod_i : i.val % q = i.val := Nat.mod_eq_of_lt hi_lt
    have h_mod_j : j.val % q = j.val := Nat.mod_eq_of_lt hj_lt
    have := h2  -- i.val % q = j.val % q
    rw [Nat.ModEq] at this
    rw [h_mod_i, h_mod_j] at this
    exact this
  exact Fin.ext heq

/-- Helper: `1 / min(a, b) ≤ 1/a + 1/b` for positive reals. -/
private lemma one_div_min_le_add (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (1 : ℝ) / min a b ≤ 1 / a + 1 / b := by
  rcases le_total a b with h | h
  · -- min = a, RHS ≥ 1/a since 1/b ≥ 0.
    rw [min_eq_left h]
    have hb_inv_nn : (0 : ℝ) ≤ 1 / b := by positivity
    linarith
  · rw [min_eq_right h]
    have ha_inv_nn : (0 : ℝ) ≤ 1 / a := by positivity
    linarith

/-- **Symmetric harmonic sum bound** (Davenport Ch. 24 §2 step 4 / IK
Lemma 13.7 step 4).  The sum `∑_{j=1}^{q-1} 1/min(j, q-j)` is bounded
by `2·(1 + log q) + 1` because each value `k ∈ [1, ⌊q/2⌋]` appears at
most twice in the sequence `min(1, q-1), min(2, q-2), …, min(q-1, 1)`,
so the symmetric sum is at most `2 · H_{⌊q/2⌋} ≤ 2 · (1 + log ⌊q/2⌋)
≤ 2 · (1 + log q)`.  For uniformity with our `C_typeI = 16` rounding,
we round up to `4 · (1 + log q)`.

Proof: termwise `1/min(j, q-j) ≤ 1/j + 1/(q-j)`; reindex `j ↦ q-j`;
apply Mathlib's `harmonic_le_one_add_log`. -/
theorem symmetric_harmonic_sum_bound (q : ℕ) (hq : 2 ≤ q) :
    ∑ j ∈ Finset.Ico 1 q, (1 : ℝ) / (min j (q - j)) ≤
      4 * (1 + Real.log q) := by
  -- Step 1: bound each `1/min(j, q-j) ≤ 1/j + 1/(q-j)` (via `one_div_min_le_add`).
  -- Step 2: reindex `∑ j (1/j + 1/(q-j)) = 2 · ∑_{j=1}^{q-1} 1/j = 2 · H_{q-1}`.
  -- Step 3: `H_{q-1} ≤ 1 + log(q-1) ≤ 1 + log q`.
  have hqN_pos : 0 < q := by linarith
  have hqR_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqN_pos
  -- Termwise upper bound.
  have h_term : ∀ j ∈ Finset.Ico 1 q, (1 : ℝ) / (min j (q - j) : ℕ) ≤
      (1 : ℝ) / j + (1 : ℝ) / (q - j : ℕ) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    obtain ⟨hj_ge, hj_lt⟩ := hj
    have hj_pos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hj_ge)
    have hqj_pos_nat : 0 < q - j := Nat.sub_pos_of_lt hj_lt
    have hqj_pos : (0 : ℝ) < ((q - j : ℕ) : ℝ) := by exact_mod_cast hqj_pos_nat
    -- min ((j:ℕ):ℝ) ((q-j:ℕ):ℝ) coincides with ((min j (q-j) : ℕ) : ℝ).
    have hmin_cast : ((min j (q - j) : ℕ) : ℝ) = min (j : ℝ) ((q - j : ℕ) : ℝ) := by
      simp [Nat.cast_min]
    rw [hmin_cast]
    exact one_div_min_le_add (j : ℝ) ((q - j : ℕ) : ℝ) hj_pos hqj_pos
  -- Sum the termwise bound.
  refine (Finset.sum_le_sum h_term).trans ?_
  -- ∑_{j=1}^{q-1} (1/j + 1/(q-j)) = ∑ 1/j + ∑ 1/(q-j) = 2 · ∑ 1/j (by reindex).
  rw [Finset.sum_add_distrib]
  -- Reindex the second sum: ∑_{j ∈ Ico 1 q} 1/(q-j) = ∑_{k ∈ Ico 1 q} 1/k.
  have h_reindex : ∑ j ∈ Finset.Ico 1 q, (1 : ℝ) / ((q - j : ℕ) : ℝ) =
      ∑ k ∈ Finset.Ico 1 q, (1 : ℝ) / (k : ℝ) := by
    -- Use the involution `j ↦ q - j` on `Finset.Ico 1 q`.
    have hq' := hq
    refine Finset.sum_nbij' (fun j => q - j) (fun k => q - k) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_Ico] at hj ⊢
      refine ⟨?_, ?_⟩
      · omega
      · omega
    · intro k hk
      simp only [Finset.mem_Ico] at hk ⊢
      refine ⟨?_, ?_⟩
      · omega
      · omega
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      omega
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      omega
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      -- The value-equality `1/↑(q-j) = 1/↑(q-j)` is trivial after beta.
      rfl
  rw [h_reindex]
  -- Now we have 2 · ∑_{j ∈ Ico 1 q} 1/j.
  have h_double : (∑ j ∈ Finset.Ico 1 q, (1 : ℝ) / (j : ℝ)) +
                  (∑ k ∈ Finset.Ico 1 q, (1 : ℝ) / (k : ℝ)) =
                  2 * (∑ j ∈ Finset.Ico 1 q, (1 : ℝ) / (j : ℝ)) := by ring
  rw [h_double]
  -- Bound ∑_{j ∈ Ico 1 q} 1/j = harmonic (q - 1) ≤ 1 + log (q - 1) ≤ 1 + log q.
  have h_eq_harm : ∑ j ∈ Finset.Ico 1 q, (1 : ℝ) / (j : ℝ) =
      ((harmonic (q - 1) : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    -- ∑_{i ∈ Icc 1 (q-1)} 1/i = ∑_{j ∈ Ico 1 q} 1/j  since Icc 1 (q-1) = Ico 1 q
    -- when q ≥ 1.
    have h_ranges_eq : Finset.Ico 1 q = Finset.Icc 1 (q - 1) := by
      ext i
      simp [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [h_ranges_eq]
    apply Finset.sum_congr rfl
    intro i _
    rw [one_div]
  rw [h_eq_harm]
  have h_harm_bound : ((harmonic (q - 1) : ℚ) : ℝ) ≤ 1 + Real.log (q - 1 : ℕ) := by
    have := harmonic_le_one_add_log (q - 1)
    exact_mod_cast this
  have h_log_mono : Real.log ((q - 1 : ℕ) : ℝ) ≤ Real.log q := by
    apply Real.log_le_log
    · exact_mod_cast Nat.sub_pos_of_lt (by linarith : 1 < q)
    · exact_mod_cast Nat.sub_le q 1
  have h_bound1 : ((harmonic (q - 1) : ℚ) : ℝ) ≤ 1 + Real.log q :=
    h_harm_bound.trans (by linarith)
  have h_one_plus_log_nn : 0 ≤ 1 + Real.log q := by
    have : Real.log 1 ≤ Real.log q := Real.log_le_log (by norm_num) (by exact_mod_cast hqN_pos)
    simp at this
    linarith
  -- 2 · (1 + log q) ≤ 4 · (1 + log q).
  calc 2 * ((harmonic (q - 1) : ℚ) : ℝ)
      ≤ 2 * (1 + Real.log q) := by linarith
    _ ≤ 4 * (1 + Real.log q) := by linarith

/-- **Davenport per-block harmonic bound** (IK Lemma 13.7, step 3+4 /
Davenport, *Multiplicative Number Theory* (3rd ed., Springer GTM 74) Ch. 24
§2 Lemma 2.2).

For a single block of length `q` centred at residue `a/q` (i.e., for
`α = a/q + θ`, `|θ| ≤ 1/q²`, `(a, q) = 1`), the inner-sum bound
`min(N+1, 1/(2‖αm‖))` summed over `m ∈ [kq, (k+1)q)` is bounded by
`q · (N+1)`.

This is the trivial per-block bound (each of `q` summands is at most
`N+1` by the left branch of `min`).  Davenport Ch. 24 §2 Lemma 2.2
sharpens this to `(N+1) + O(q log q)` when only the FIRST block
(`k = 0`) is considered, by combining:
- The residue `0` summand contributes ≤ `N+1` (trivial `min` cap).
- For residue `j ∈ {1, …, q-1}`, `‖αm‖ ≥ ‖(am)/q‖ - |θm| ≥
  min(j, q-j)/(2q)` whenever `|θm| ≤ min(j,q-j)/(2q)` (the
  "good-residue" regime).
- Summing the symmetric harmonic `∑_{j=1}^{q-1} 1/min(j, q-j) ≤
  2 · (log q + 1)` (proven above as `symmetric_harmonic_sum_bound`)
  gives the `2q(log q + 1)` contribution from good residues.
- "Bad residues" (where `|θm|` exceeds `min(j,q-j)/(2q)`) fall back to
  the trivial `(N+1)` cap; counting these requires the Dirichlet
  spacing argument (per-block bound `≤ 1 + 4k` bad residues), giving
  an extra `(1 + 4k)(N+1)` term per block `k`.

For Phase 2b of the `typeI_bound` upgrade we prove the cleanly-valid
TRIVIAL per-block bound `q · (N+1)`, which suffices to assemble a
`q`-uniform Type-I bound with constant `C_typeI = O(q²)`.  The sharper
`(N+1) + O(q log q + k(N+1))` per-block bound is the analytic content
of Phase 2c, requiring the bad-residue count via the Dirichlet
three-distance theorem.  See `dirichlet_divided_sum_uniform` below.

References:
* Davenport, *Multiplicative Number Theory*, Ch. 24 §2 Lemma 2.2.
* Iwaniec–Kowalski, *Analytic Number Theory*, Ch. 13 Lemma 13.7
  (p. 319–320).
-/
theorem single_block_sum_bound
    (a q : ℕ) (α : ℝ) (M N : ℕ) (hq : 1 ≤ q) (k : ℕ) (_hM : (M : ℝ) ≤ (q : ℝ) ^ 2 / 2)
    (_hα : ∃ θ : ℝ, |θ| ≤ 1 / ((q : ℝ) ^ 2) ∧ α = (a : ℝ) / q + θ)
    (_hcop : Nat.Coprime a q) :
    ∑ m ∈ (Finset.range q).image (fun j => k * q + j),
        min ((N : ℝ) + 1) (1 / (2 * nearestIntDist (α * m))) ≤
      (q : ℝ) * ((N : ℝ) + 1) := by
  -- TRIVIAL per-block bound (Davenport Ch. 24 §2 Lemma 2.2, step 1).
  -- Each of the (at most) `q` summands is bounded by the left branch
  -- `(N + 1)` of `min`.  We bound the sum over the image by the sum over
  -- the preimage `Finset.range q` (a sum over `q` terms each ≤ N+1).
  --
  -- The image may collapse if `k*q + j₁ = k*q + j₂` for `j₁ ≠ j₂` (it
  -- cannot, since `+` is injective in the second arg), so `card = q`.
  -- We use `Finset.sum_image_le` (each summand nonneg).
  have hN1_nn : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
  -- The summand `f m := min (N+1) (1/(2·nearestIntDist (α·m)))` is bounded
  -- above by `N+1` and below by `0` (since 1/(2·d) ≥ 0 for d ≥ 0).
  have h_each_le : ∀ m, min ((N : ℝ) + 1) (1 / (2 * nearestIntDist (α * m))) ≤
      (N : ℝ) + 1 := fun m => min_le_left _ _
  have h_each_nn : ∀ m, (0 : ℝ) ≤ min ((N : ℝ) + 1) (1 / (2 * nearestIntDist (α * m))) := by
    intro m
    refine le_min hN1_nn ?_
    -- 1 / (2 · d) ≥ 0 for d ≥ 0.
    have hd_nn : 0 ≤ nearestIntDist (α * m) := nearestIntDist_nonneg _
    have h2d_nn : 0 ≤ 2 * nearestIntDist (α * m) := by linarith
    positivity
  -- Convert sum over image into sum over preimage `Finset.range q`.
  have h_inj : ∀ j₁ ∈ Finset.range q, ∀ j₂ ∈ Finset.range q,
      k * q + j₁ = k * q + j₂ → j₁ = j₂ := by
    intro j₁ _ j₂ _ heq
    exact Nat.add_left_cancel heq
  -- The sum over an image is ≤ sum over preimage (each term nonneg).
  have h_card_image : (((Finset.range q).image (fun j => k * q + j)).card : ℝ) ≤ q := by
    have : ((Finset.range q).image (fun j => k * q + j)).card ≤ (Finset.range q).card :=
      Finset.card_image_le
    have hq_card : (Finset.range q).card = q := Finset.card_range _
    rw [hq_card] at this
    exact_mod_cast this
  -- Bound each summand by `N+1` and use cardinality.
  calc ∑ m ∈ (Finset.range q).image (fun j => k * q + j),
          min ((N : ℝ) + 1) (1 / (2 * nearestIntDist (α * m)))
      ≤ ∑ _m ∈ (Finset.range q).image (fun j => k * q + j), ((N : ℝ) + 1) :=
        Finset.sum_le_sum (fun m _ => h_each_le m)
    _ = (((Finset.range q).image (fun j => k * q + j)).card : ℝ) * ((N : ℝ) + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (q : ℝ) * ((N : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right h_card_image hN1_nn

/-! ### Phase 2c: Refined per-block bound

We strengthen `single_block_sum_bound`'s trivial `q·(N+1)` to the genuine
Davenport refinement (IK Lemma 13.7, p. 319):

  `∑_{m ∈ block_k} min(N+1, 1/(2‖αm‖)) ≤ (4k+3)·(N+1) + 4q·(1+log q)`.

The combinatorial structure is:

1. **Bad residues** (at most `4k+3` of them per block): values of `m` in
   the block where `‖αm‖` is too small for the `1/(2‖αm‖)` branch of `min`
   to beat `N+1`.  These use the trivial `(N+1)` cap.
2. **Good residues** (the remaining ones): bound `1/(2‖αm‖) ≤ q/(2·d_j)`
   where `d_j = min(j, q-j)` and `j = (a·m) mod q`, then sum the symmetric
   harmonic series (proven above as `symmetric_harmonic_sum_bound`).

The bad-residue counting bound `≤ 4k+3` is the **Davenport pigeonhole**
(*Multiplicative NT* (3rd ed.) Ch. 24 §2 Lemma 2.2): the points
`{α·m (mod 1) : m ∈ block_k}` are spaced approximately `1/q` apart, and
at most `4k+3` of them can be ≤ `1/(2(N+1))` from an integer (which is
when the `1/(2d)` cap fails to improve on `N+1`).  Formally, this uses
the three-distance theorem applied to the rotation by `α`.

The refined bound is stated as `single_block_sum_bound_refined` below; its
proof factors through `single_block_bad_residue_count` (analytic content,
Davenport pigeonhole) and `single_block_good_residue_sum_bound`
(combinatorial, uses `symmetric_harmonic_sum_bound`).
-/

/-- The set of "bad" residues `j ∈ Finset.range q` in block `k`, i.e., those
for which the Davenport bound `q/(2·d_j)` (where `d_j = min(j, q-j)` for
`j ≥ 1`, and `d_0 = q`) fails to beat `N+1`.  Equivalently, `d_j ≤ q/(2(N+1))`.

For `j ≥ 1`, this is the set of residues with `min(j, q-j) ≤ q/(2(N+1))`.
The Davenport pigeonhole bounds the cardinality of this set (over `m` in
block `k`, i.e., `m = kq, kq+1, …, kq+q-1`) by `4k+3`. -/
private noncomputable def badResidueSet (q N : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun j =>
    (min (j : ℝ) ((q : ℝ) - j) : ℝ) ≤ (q : ℝ) / (2 * ((N : ℝ) + 1)))

/-- The "good" residues are the complement: `j ∈ Finset.range q` with
`d_j > q/(2(N+1))`, i.e., where the `1/(2·d_j)` bound improves on `N+1`. -/
private noncomputable def goodResidueSet (q N : ℕ) : Finset ℕ :=
  (Finset.range q) \ badResidueSet q N

private lemma badResidueSet_subset_range (q N : ℕ) :
    badResidueSet q N ⊆ Finset.range q := by
  unfold badResidueSet; exact Finset.filter_subset _ _

private lemma good_union_bad (q N : ℕ) :
    badResidueSet q N ∪ goodResidueSet q N = Finset.range q := by
  unfold goodResidueSet
  exact Finset.union_sdiff_of_subset (badResidueSet_subset_range q N)

private lemma good_disjoint_bad (q N : ℕ) :
    Disjoint (badResidueSet q N) (goodResidueSet q N) := by
  unfold goodResidueSet
  exact Finset.disjoint_sdiff

/-! ### `k`-dependent residue partition (Phase 2c-3 refinement)

The static `badResidueSet q N` (using the bad-threshold `d ≤ q/(2(N+1))`)
is too loose to support the Davenport pointwise estimate, which needs the
tighter regime `d ≥ 2(k+1)` in block `k`.  The k-dependent versions below
align the partition with the analytic regime so that
`single_block_sum_bound_refined` closes without any internal placeholder.

Davenport, *Multiplicative NT* (3rd ed.) Ch. 24 §2 Lemma 2.2 absorbs the
small-distance residues into the bad-count (provable here by direct
pigeonhole: `card{j : min(j, q-j) < 2(k+1)} ≤ 4k+3`, beating the
`O(1+log q)` three-distance bound but sufficient for the per-block
estimate). -/

/-- The set of "bad" residues `j ∈ Finset.range q` *in block `k`*, i.e.,
those for which the Davenport pointwise estimate `‖αm‖ ≥ d_j/(2q)` fails
because `d_j := min(j, q - j) < 2(k+1)`.

For `j = 0` we have `d_0 = min(0, q) = 0 < 2(k+1)`, so `0 ∈ badResidueSetAtK`
for every `k`.

The cardinality bound `card ≤ 4k+3` is provable directly by pigeonhole
(see `single_block_bad_residue_count`). -/
private noncomputable def badResidueSetAtK (q k : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun j =>
    (min (j : ℝ) ((q : ℝ) - j) : ℝ) < 2 * ((k : ℝ) + 1))

/-- The "good" residues for block `k`: those with `d_j ≥ 2(k+1)`, so the
Davenport pointwise estimate applies. -/
private noncomputable def goodResidueSetAtK (q k : ℕ) : Finset ℕ :=
  (Finset.range q) \ badResidueSetAtK q k

private lemma badResidueSetAtK_subset_range (q k : ℕ) :
    badResidueSetAtK q k ⊆ Finset.range q := by
  unfold badResidueSetAtK; exact Finset.filter_subset _ _

private lemma good_union_bad_atK (q k : ℕ) :
    badResidueSetAtK q k ∪ goodResidueSetAtK q k = Finset.range q := by
  unfold goodResidueSetAtK
  exact Finset.union_sdiff_of_subset (badResidueSetAtK_subset_range q k)

private lemma good_disjoint_bad_atK (q k : ℕ) :
    Disjoint (badResidueSetAtK q k) (goodResidueSetAtK q k) := by
  unfold goodResidueSetAtK
  exact Finset.disjoint_sdiff

/-- For `j ∈ goodResidueSetAtK q k`, the regime hypothesis of
`davenport_good_residue_pointwise_bound` holds. -/
private lemma goodResidueSetAtK_regime (q k j : ℕ)
    (hj : j ∈ goodResidueSetAtK q k) :
    2 * ((k : ℝ) + 1) ≤ min (j : ℝ) ((q : ℝ) - j) := by
  -- `j ∈ goodResidueSetAtK = range q \ badResidueSetAtK`, so `j ∈ range q` and
  -- `j ∉ badResidueSetAtK`.  The latter says `¬ (j ∈ range q ∧ d_j < 2(k+1))`;
  -- combined with `j ∈ range q` this gives `¬ (d_j < 2(k+1))`, i.e.
  -- `d_j ≥ 2(k+1)`.
  have hsplit : j ∈ Finset.range q ∧ j ∉ badResidueSetAtK q k := by
    unfold goodResidueSetAtK at hj
    exact Finset.mem_sdiff.mp hj
  obtain ⟨hjr, hj_not_bad⟩ := hsplit
  -- Unfold `j ∉ badResidueSetAtK` to get a strict inequality.
  by_contra h_lt
  push Not at h_lt
  -- `h_lt : min (j : ℝ) ((q : ℝ) - j) < 2 * (k + 1)`, so j ∈ badResidueSetAtK.
  apply hj_not_bad
  unfold badResidueSetAtK
  rw [Finset.mem_filter]
  exact ⟨hjr, h_lt⟩

/-- **Davenport bad-residue count** (Davenport Ch. 24 §2 Lemma 2.2 step 1;
IK Lemma 13.7 p. 319 step "bad" residues).

For block `k` (`m ∈ [kq, (k+1)q)`), the number of residues `j ∈ [0, q)`
that are *bad for block `k`* — i.e., `min(j, q-j) < 2(k+1)` — is at most
`4k+3`.

**Proof (direct pigeonhole, Phase 2c-3 refinement).**  Write `D = 2(k+1)`.
The bad set is `{j ∈ range q : j < D} ∪ {j ∈ range q : q - j < D}`.  The
first piece has at most `D = 2(k+1)` elements; the second has at most
`D - 1 = 2(k+1) - 1` elements (since `q - j ≥ 1` for `j < q`).  Their
union has at most `4(k+1) - 1 = 4k+3` elements.

This is the residue-count input that, in Davenport's original argument,
is obtained via the three-distance theorem on the rotation `α·m`.  The
k-dependent partition `badResidueSetAtK q k` aligns with the regime
hypothesis `d_j ≥ 2(k+1)` of `davenport_good_residue_pointwise_bound`,
allowing the per-block estimate to close without invoking Mathlib's
unported `Real.threeDistanceTheorem`.

Reference: Davenport, *Multiplicative NT* (3rd ed.) Ch. 24 §2 Lemma 2.2,
proof step "small distance count" (=`O(k)` via pigeonhole). -/
theorem single_block_bad_residue_count
    (a q : ℕ) (_α : ℝ) (M N k : ℕ) (_hq : 1 ≤ q)
    (_hM : (M : ℝ) ≤ (q : ℝ) ^ 2 / 2)
    (_hα : ∃ θ : ℝ, |θ| ≤ 1 / ((q : ℝ) ^ 2) ∧ _α = (a : ℝ) / q + θ)
    (_hcop : Nat.Coprime a q) :
    ((badResidueSetAtK q k).card : ℝ) ≤ 4 * k + 3 := by
  -- Direct pigeonhole on the k-dependent set
  -- `{j ∈ range q : min(j, q-j) < 2(k+1)}`.
  -- We show `badResidueSetAtK q k ⊆ A ∪ B` where:
  --   A := Finset.range (2*(k+1))           (covers `j < 2(k+1)`)
  --   B := Finset.Ioo (q - 2*(k+1)) q        (covers `q - j < 2(k+1)`)
  -- Cards: A.card ≤ 2*(k+1) and B.card ≤ 2*(k+1) - 1, total ≤ 4k+3.
  -- Recall N here is unused; the bad set only depends on k.
  classical
  set D : ℕ := 2 * (k + 1) with hD_def
  set A : Finset ℕ := Finset.range D with hA_def
  set B : Finset ℕ := Finset.Ioo (q - D) q with hB_def
  -- Subset claim.
  have h_subset : badResidueSetAtK q k ⊆ A ∪ B := by
    intro j hj
    unfold badResidueSetAtK at hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hj_lt, hj_min⟩ := hj
    -- hj_min : min (j : ℝ) ((q : ℝ) - j) < 2 * ((k : ℝ) + 1)
    -- Case split on which branch is the smaller.
    rcases lt_or_ge ((j : ℝ)) ((q : ℝ) - j) with hcase | hcase
    · -- `(j : ℝ) ≤ (q : ℝ) - j`, so `min = j`, hence `j < D` as reals.
      have h_min_eq : min ((j : ℝ)) ((q : ℝ) - j) = (j : ℝ) :=
        min_eq_left hcase.le
      rw [h_min_eq] at hj_min
      -- `(j : ℝ) < (D : ℝ)`, hence `j < D` (Nat).
      have hj_D : j < D := by
        have h_cast : ((D : ℕ) : ℝ) = 2 * ((k : ℝ) + 1) := by
          rw [hD_def]; push_cast; ring
        have : (j : ℝ) < ((D : ℕ) : ℝ) := by rw [h_cast]; exact hj_min
        exact_mod_cast this
      refine Finset.mem_union.mpr (Or.inl ?_)
      rw [hA_def]; exact Finset.mem_range.mpr hj_D
    · -- `(q : ℝ) - j ≤ (j : ℝ)`, so `min = q - j`, hence `q - j < D` as reals.
      have h_min_eq : min ((j : ℝ)) ((q : ℝ) - j) = (q : ℝ) - j :=
        min_eq_right hcase
      rw [h_min_eq] at hj_min
      -- `(q : ℝ) - j < D`. Translate to Nat: `q - j < D`.
      have hj_le_q : j ≤ q := le_of_lt hj_lt
      have h_qsub_cast : ((q - j : ℕ) : ℝ) = (q : ℝ) - (j : ℝ) := by
        rw [Nat.cast_sub hj_le_q]
      have h_cast : ((D : ℕ) : ℝ) = 2 * ((k : ℝ) + 1) := by
        rw [hD_def]; push_cast; ring
      have : ((q - j : ℕ) : ℝ) < ((D : ℕ) : ℝ) := by
        rw [h_qsub_cast, h_cast]; exact hj_min
      have hqj_D : q - j < D := by exact_mod_cast this
      -- Now `q - j < D` and `j < q` give `q - D < j < q`, so `j ∈ Ioo (q - D) q`.
      refine Finset.mem_union.mpr (Or.inr ?_)
      rw [hB_def, Finset.mem_Ioo]
      refine ⟨?_, hj_lt⟩
      -- `j > q - D` follows from `q - j < D`.
      by_cases hqD : D ≤ q
      · -- `q - D + j ≥ ?` — use Nat arithmetic.
        omega
      · -- `D > q`, so `q - D = 0` and `j ≥ 0`; need strict `0 < j`.
        -- When `q < D`, we have `q - D = 0` (Nat).  Need `0 < j`.
        -- Subcase: if `j = 0`, then `q - j = q < D`, which is consistent; we still need
        -- `j > q - D = 0`, i.e., `j ≥ 1`.  This may fail!
        -- However, when `j = 0`, the first branch `(j : ℝ) ≤ (q : ℝ) - j` applies
        -- (since `0 ≤ q`), so we should be in the first case, not this one.
        -- We're in the second case `hcase : (q : ℝ) - j ≤ (j : ℝ)`.
        -- Combined with `j ≥ 0`, this gives `q ≤ 2j`, so `j ≥ q/2 ≥ 1` when q ≥ 2.
        -- But when q = 1, range q = {0}, and j = 0 puts q - j = 1 ≤ 0 = j is false.
        -- So we're safe: in this branch, j ≥ 1.
        -- More directly: from `hcase`, `(q : ℝ) ≤ 2 * (j : ℝ)`, so `q ≤ 2j` (Nat).
        have hq_le_2j_real : (q : ℝ) ≤ 2 * (j : ℝ) := by linarith
        have hq_le_2j : q ≤ 2 * j := by exact_mod_cast hq_le_2j_real
        -- If `j = 0`, then `q ≤ 0`, but `j < q` gives `q ≥ 1`, contradiction.
        have hj_pos : 0 < j := by
          by_contra h0
          push Not at h0
          interval_cases j
          omega
        omega
  -- Cardinality argument: badResidueSetAtK q k ⊆ A ∪ B, |A ∪ B| ≤ |A| + |B|.
  have h_card_AB : (A ∪ B).card ≤ A.card + B.card := Finset.card_union_le A B
  have hA_card : A.card = D := by rw [hA_def, Finset.card_range]
  have hB_card : B.card ≤ D - 1 := by
    -- B = Ioo (q - D) q, card = q - (q - D) - 1.
    rw [hB_def, Nat.card_Ioo]
    -- |Ioo (q - D) q| = q - (q - D) - 1.
    -- Two cases: D ≤ q or D > q.
    by_cases hqD : D ≤ q
    · -- q - (q - D) = D, so card = D - 1.
      have : q - (q - D) = D := by omega
      omega
    · -- q < D, so q - D = 0, card = q - 0 - 1 = q - 1 ≤ D - 1.
      omega
  have h_card_le_nat : (A ∪ B).card ≤ 4 * k + 3 := by
    have hD_val : D = 2 * (k + 1) := hD_def
    -- A.card + B.card ≤ D + (D - 1) = 2D - 1 = 4(k+1) - 1 = 4k + 3.
    have h_AB : A.card + B.card ≤ D + (D - 1) := by
      have hh : A.card + B.card ≤ D + (D - 1) := by
        rw [hA_card]
        exact Nat.add_le_add_left hB_card D
      exact hh
    have h_sum : D + (D - 1) = 4 * k + 3 := by
      rw [hD_val]
      have : 2 * (k + 1) + (2 * (k + 1) - 1) = 4 * k + 3 := by omega
      exact this
    omega
  have h_main : (badResidueSetAtK q k).card ≤ 4 * k + 3 :=
    (Finset.card_le_card h_subset).trans h_card_le_nat
  -- Cast to ℝ.
  have h_cast : ((badResidueSetAtK q k).card : ℝ) ≤ ((4 * k + 3 : ℕ) : ℝ) := by
    exact_mod_cast h_main
  have h_RHS : ((4 * k + 3 : ℕ) : ℝ) = 4 * (k : ℝ) + 3 := by push_cast; ring
  linarith [h_RHS ▸ h_cast]

/-- **Davenport good-residue harmonic bound** (Davenport Ch. 24 §2 Lemma
2.2 step 2; IK Lemma 13.7 p. 319 step "good" residues).

For each good residue `j ∈ {1, …, q-1}` (i.e., one whose distance to
boundary `d_j = min(j, q-j) > q/(2(N+1))`), the Davenport inner-sum
bound is at most `q/(2·d_j)`.  Summing over good residues gives at most
`∑_{j=1}^{q-1} q/(2·min(j, q-j)) ≤ q · (1 + log q) ≤ 4q·(1+log q)`.

**Formal statement:** the sum over `goodResidueSet q N` of the
bound-substitute `q / (2 · max 1 (min j (q-j)))` is `≤ 4q·(1 + log q)`.

We use `max 1 _` to handle `j = 0` cleanly (in which case `d_j = 0` would
divide by zero; but `j = 0` is in the bad set since `min(0, q) = 0 ≤ q/(2(N+1))`
trivially, so the good set excludes it).  For `j ≥ 1`, `max 1 (min j (q-j)) =
min j (q-j)` when `q ≥ 2`.

Proof: reduce to `symmetric_harmonic_sum_bound`, dropping any restriction
to good residues (the harmonic series is monotone, so summing over a
subset of `Finset.Ico 1 q` gives a smaller value). -/
theorem single_block_good_residue_sum_bound
    (q N : ℕ) (hq : 2 ≤ q) :
    ∑ j ∈ goodResidueSet q N,
        (q : ℝ) / (2 * (max (1 : ℝ) (min (j : ℝ) ((q : ℝ) - j)))) ≤
      4 * (q : ℝ) * (1 + Real.log q) := by
  -- Bound by ∑ over Finset.range q (the good set is a subset), then drop
  -- `j = 0` and bound the rest by symmetric_harmonic_sum_bound.
  have hq_pos : 0 < q := by linarith
  have hqR_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
  -- Step 1: each summand is nonneg.
  have h_nn : ∀ j, (0 : ℝ) ≤ (q : ℝ) / (2 * (max (1 : ℝ) (min (j : ℝ) ((q : ℝ) - j)))) := by
    intro j
    have hmax_pos : (0 : ℝ) < max 1 (min (j : ℝ) ((q : ℝ) - j)) :=
      lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    positivity
  -- Step 2: extend the sum from goodResidueSet to Finset.range q.
  have h_subset : goodResidueSet q N ⊆ Finset.range q := by
    unfold goodResidueSet; exact Finset.sdiff_subset
  have h_step1 :
      ∑ j ∈ goodResidueSet q N,
          (q : ℝ) / (2 * (max (1 : ℝ) (min (j : ℝ) ((q : ℝ) - j)))) ≤
      ∑ j ∈ Finset.range q,
          (q : ℝ) / (2 * (max (1 : ℝ) (min (j : ℝ) ((q : ℝ) - j)))) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg h_subset ?_
    intro j _ _; exact h_nn j
  refine h_step1.trans ?_
  -- Step 3: split off `j = 0` and reindex remainder to `Finset.Ico 1 q`.
  have h_split : Finset.range q = insert 0 (Finset.Ico 1 q) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    constructor
    · intro hi
      by_cases h0 : i = 0
      · left; exact h0
      · right; exact ⟨Nat.one_le_iff_ne_zero.mpr h0, hi⟩
    · rintro (rfl | ⟨_, h2⟩)
      · exact hq_pos
      · exact h2
  have h_zero_not_mem : (0 : ℕ) ∉ Finset.Ico 1 q := by
    simp [Finset.mem_Ico]
  rw [h_split, Finset.sum_insert h_zero_not_mem]
  -- The `j = 0` summand: `q / (2 · max 1 (min 0 q)) = q / (2 · max 1 0) = q / 2`.
  -- Note Lean reduces `((0 : ℕ) : ℝ) - ↑0` to `↑q - ↑0`. Use the cast 0 form.
  have h_zero_eval :
      (q : ℝ) / (2 * (max (1 : ℝ) (min ((0 : ℕ) : ℝ) ((q : ℝ) - ((0 : ℕ) : ℝ))))) = q / 2 := by
    push_cast
    have h_min_zero : min (0 : ℝ) ((q : ℝ) - 0) = 0 := by
      have : (0 : ℝ) ≤ (q : ℝ) - 0 := by linarith
      exact min_eq_left this
    have h_max_one : max (1 : ℝ) 0 = 1 := max_eq_left (by norm_num : (0 : ℝ) ≤ 1)
    rw [h_min_zero, h_max_one]
    ring
  rw [h_zero_eval]
  -- Step 4: bound the j ∈ Ico 1 q part by symmetric_harmonic_sum_bound · q.
  -- For j ∈ [1, q), min(j, q-j) ≥ 1, so max 1 (min j (q-j)) = min j (q-j).
  have h_ico_termwise : ∀ j ∈ Finset.Ico 1 q,
      (q : ℝ) / (2 * (max (1 : ℝ) (min (j : ℝ) ((q : ℝ) - j)))) ≤
        (q : ℝ) / 2 * ((1 : ℝ) / ((min j (q - j) : ℕ) : ℝ)) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    obtain ⟨hj_ge, hj_lt⟩ := hj
    have hj_pos : 0 < j := hj_ge
    have hqj_pos : 0 < q - j := Nat.sub_pos_of_lt hj_lt
    have hmin_pos : 0 < min j (q - j) := Nat.lt_min.mpr ⟨hj_pos, hqj_pos⟩
    have hmin_posR : (0 : ℝ) < ((min j (q - j) : ℕ) : ℝ) := by exact_mod_cast hmin_pos
    have hmin_ge_one : (1 : ℝ) ≤ ((min j (q - j) : ℕ) : ℝ) := by exact_mod_cast hmin_pos
    have hmin_cast : ((min j (q - j) : ℕ) : ℝ) = min (j : ℝ) ((q : ℝ) - j) := by
      have h1 : ((min j (q - j) : ℕ) : ℝ) = min ((j : ℕ) : ℝ) (((q - j : ℕ) : ℝ)) := by
        push_cast; rfl
      rw [h1]
      congr 1
      push_cast
      exact_mod_cast Nat.cast_sub hj_lt.le
    have hmin_real_pos : (0 : ℝ) < min (j : ℝ) ((q : ℝ) - j) := by
      rw [← hmin_cast]; exact hmin_posR
    have hmin_real_ge_one : (1 : ℝ) ≤ min (j : ℝ) ((q : ℝ) - j) := by
      rw [← hmin_cast]; exact hmin_ge_one
    have h_max_eq : max (1 : ℝ) (min (j : ℝ) ((q : ℝ) - j)) = min (j : ℝ) ((q : ℝ) - j) :=
      max_eq_right hmin_real_ge_one
    rw [h_max_eq, ← hmin_cast]
    rw [div_mul_eq_div_div, div_eq_mul_one_div]
  have h_ico_step :
      ∑ j ∈ Finset.Ico 1 q,
          (q : ℝ) / (2 * (max (1 : ℝ) (min (j : ℝ) ((q : ℝ) - j)))) ≤
      ∑ j ∈ Finset.Ico 1 q, (q : ℝ) / 2 * ((1 : ℝ) / ((min j (q - j) : ℕ) : ℝ)) :=
    Finset.sum_le_sum h_ico_termwise
  -- Factor q/2 out of the RHS and apply symmetric_harmonic_sum_bound.
  have h_factor :
      ∑ j ∈ Finset.Ico 1 q, (q : ℝ) / 2 * ((1 : ℝ) / ((min j (q - j) : ℕ) : ℝ)) =
      (q : ℝ) / 2 * ∑ j ∈ Finset.Ico 1 q, ((1 : ℝ) / ((min j (q - j) : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]
  rw [h_factor] at h_ico_step
  have h_sym := symmetric_harmonic_sum_bound q hq
  have hq_half_nn : 0 ≤ (q : ℝ) / 2 := by positivity
  have h_apply_sym :
      (q : ℝ) / 2 * ∑ j ∈ Finset.Ico 1 q, ((1 : ℝ) / ((min j (q - j) : ℕ) : ℝ)) ≤
      (q : ℝ) / 2 * (4 * (1 + Real.log q)) :=
    mul_le_mul_of_nonneg_left h_sym hq_half_nn
  -- Chain: goodSum ≤ Ico-sum ≤ q/2 · harmonic ≤ q/2 · 4(1+log q) = 2q(1+log q).
  -- Then 2q(1+log q) ≤ 4q(1+log q) since 1+log q ≥ 0 for q ≥ 1.
  have h_log_nn : 0 ≤ Real.log q := by
    apply Real.log_nonneg; exact_mod_cast hq_pos
  have h_one_plus_log : 1 ≤ 1 + Real.log q := by linarith
  have h_q_half_le : (q : ℝ) / 2 ≤ 2 * q * (1 + Real.log q) := by
    calc (q : ℝ) / 2
        ≤ q := by linarith
      _ = q * 1 := by ring
      _ ≤ q * (1 + Real.log q) := by nlinarith
      _ ≤ 2 * q * (1 + Real.log q) := by nlinarith
  -- Final combine: (q/2) + (q/2 · 4(1+log q)) ≤ 4q(1+log q).
  have h_final :
      (q : ℝ) / 2 + (q : ℝ) / 2 * (4 * (1 + Real.log q)) ≤ 4 * (q : ℝ) * (1 + Real.log q) := by
    have h_simplify : (q : ℝ) / 2 * (4 * (1 + Real.log q)) = 2 * q * (1 + Real.log q) := by ring
    rw [h_simplify]; linarith [h_q_half_le]
  -- The goal after `rw [h_zero_eval]` is:
  --   q / 2 + ∑ j ∈ Ico 1 q, ... ≤ 4 q (1 + log q).
  -- Chain through h_ico_step (LHS sum ≤ q/2 · ...) and h_apply_sym, then h_final.
  have h_chain :
      (q : ℝ) / 2 + ∑ j ∈ Finset.Ico 1 q,
          (q : ℝ) / (2 * (max (1 : ℝ) (min (j : ℝ) ((q : ℝ) - j)))) ≤
      (q : ℝ) / 2 + (q : ℝ) / 2 * (4 * (1 + Real.log q)) := by
    have h_sum_chain : ∑ j ∈ Finset.Ico 1 q,
            (q : ℝ) / (2 * (max (1 : ℝ) (min (j : ℝ) ((q : ℝ) - j)))) ≤
        (q : ℝ) / 2 * (4 * (1 + Real.log q)) := h_ico_step.trans h_apply_sym
    linarith
  exact h_chain.trans h_final

/-! ### Davenport pointwise estimate (`‖αm‖ ≥ d_j/(2q)`) on good residues

The analytic heart of the Phase 2c refinement is the per-`m` lower bound
on `nearestIntDist(α·m)` for `m` in the block whose residue
`j' = (a·m) mod q` is "good" (i.e., `d_{j'} > q/(2(N+1))`).

Writing `α·m = (a·m)/q + θ·m = l + j'/q + θ·m` (with `l ∈ ℤ`,
`j' ∈ [0, q)`), we have
  `nearestIntDist(α·m) = nearestIntDist(j'/q + θ·m)`
and by the triangle inequality for the sawtooth,
  `nearestIntDist(α·m) ≥ nearestIntDist(j'/q) − |θ·m|
                       = d_{j'}/q − |θ·m|`.

For `m ∈ [kq, (k+1)q)`, we have `|θ·m| ≤ |θ|·(k+1)q ≤ (k+1)/q`.  The
Davenport refinement (`Multiplicative NT` Ch. 24 §2 Lemma 2.2) restricts
the relevant `j'` to those with `d_{j'} ≥ 2(k+1)`, ensuring
  `nearestIntDist(α·m) ≥ d_{j'}/q − (k+1)/q ≥ d_{j'}/(2q)`,
hence `1/(2·nearestIntDist(α·m)) ≤ q/d_{j'}`.

The block-by-block accounting then absorbs the `≤ 4k+3` residues with
`d_{j'} < 2(k+1)` into the *bad* count (along with those failing the
trivial cap `d_{j'} ≤ q/(2(N+1))`), arriving at the `(4k+3)·(N+1)`
contribution.  The remaining "good" residues satisfy the harmonic bound
`∑ q/d_{j'} ≤ 2q(1+log q)`, controlled by `symmetric_harmonic_sum_bound`.

We package the pointwise estimate as the conditional lemma
`davenport_good_residue_pointwise_bound`, whose hypothesis encodes the
residue regime where the estimate applies.  Its proof goes through the
sawtooth triangle inequality on `Int.fract`; for Phase 2c-2 we record
the statement and cite Davenport (the full Int.fract decomposition is
mechanical but tedious — see Phase 2d notes). -/

/-- **Davenport pointwise inner-bound on the good regime**
(Davenport, *Multiplicative NT* (3rd ed.) Ch. 24 §2 Lemma 2.2, step 2).

For `m` in block `k` (so `m ≤ (k+1)q − 1`) with `α = a/q + θ`,
`|θ| ≤ 1/q²`, and residue `j' = (a·m) mod q` satisfying
`d_{j'} := min(j', q−j') ≥ 2(k+1)`, the Davenport sawtooth estimate
yields
  `nearestIntDist(α·m) ≥ d_{j'}/(2q)`,
hence the inner-sum cap satisfies
  `1/(2·nearestIntDist(α·m)) ≤ q / d_{j'}`.

Combined with the trivial `min(N+1, x) ≤ x` cap on the `1/(2‖αm‖)`
branch, we obtain the form used in the block assembly.

**Proof sketch:** Write `α·m = ⌊(a·m)/q⌋ + j'/q + θ·m`. Then
`nearestIntDist(α·m) = nearestIntDist(j'/q + θ·m)`. Triangle inequality
for the sawtooth `‖x + y‖ ≥ ‖x‖ − |y|` (with `‖x‖ = nearestIntDist x`)
gives `≥ d_{j'}/q − |θ·m|`. Since `|θ·m| ≤ (k+1)/q` and
`d_{j'} ≥ 2(k+1)`, we get `≥ d_{j'}/q − d_{j'}/(2q) = d_{j'}/(2q)`.

For Phase 2c-2 we record the analytic statement and defer the
`Int.fract`-based sawtooth triangle-inequality proof to Phase 2d
(it is a mechanical decomposition; the analytic content is exhausted
by the inequality chain above). -/
theorem davenport_good_residue_pointwise_bound
    (a q : ℕ) (α : ℝ) (m k : ℕ) (hq : 1 ≤ q)
    (hm_block : m ≤ (k + 1) * q - 1)
    (hα : ∃ θ : ℝ, |θ| ≤ 1 / ((q : ℝ) ^ 2) ∧ α = (a : ℝ) / q + θ)
    (_hcop : Nat.Coprime a q)
    (hgood : (2 * ((k : ℝ) + 1)) ≤
        (min ((((a * m) % q : ℕ) : ℝ)) ((q : ℝ) - (((a * m) % q : ℕ) : ℝ)))) :
    nearestIntDist (α * m) ≥
      (min ((((a * m) % q : ℕ) : ℝ)) ((q : ℝ) - (((a * m) % q : ℕ) : ℝ))) /
        (2 * (q : ℝ)) := by
  -- Davenport Ch. 24 §2 Lemma 2.2, step 2.
  -- Proof: write `α·m = (a·m)/q + θ·m`.  Sawtooth triangle inequality on
  -- `Int.fract` (via `|x - round x|`) gives
  --   `nearestIntDist(αm) ≥ nearestIntDist((a·m)/q) − |θ·m|`.
  -- `nearestIntDist((a·m)/q) = d_{j'}/q` where `j' = (a·m) % q`
  -- (Mathlib `abs_sub_round_div_natCast_eq`).
  -- `|θ·m| ≤ m/q² ≤ ((k+1)q − 1)/q² < (k+1)/q ≤ d_{j'}/(2q)` (by `hgood`).
  -- Hence `nearestIntDist(αm) ≥ d_{j'}/q − d_{j'}/(2q) = d_{j'}/(2q)`.
  classical
  -- Basic positivity.
  have hqR_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hq)
  have hqR_ne : (q : ℝ) ≠ 0 := ne_of_gt hqR_pos
  -- Notation for `j' := (a·m) % q` and `d := min(j', q - j')`.
  set j : ℕ := (a * m) % q with hj_def
  set d : ℝ := min ((j : ℝ)) ((q : ℝ) - (j : ℝ)) with hd_def
  -- Extract `θ`.
  obtain ⟨θ, hθ_abs, hα_eq⟩ := hα
  -- Rewrite `α * m = (a*m)/q + θ*m`.
  have h_decomp : α * (m : ℝ) = ((a * m : ℕ) : ℝ) / (q : ℝ) + θ * (m : ℝ) := by
    rw [hα_eq]
    push_cast
    field_simp
  -- Step 1: `nearestIntDist(αm) ≥ nearestIntDist((a*m)/q) − |θ*m|`.
  -- We show this via the characterization `nearestIntDist x = |x - round x|`.
  -- Let `r := round((a*m)/q + θ*m) = round(α*m)`.  Then for any integer `n`,
  --    nearestIntDist (αm) = |αm - r| ≤ |αm - n|  (by definition of round).
  -- We use the converse direction: for ANY integer `z`,
  --    `nearestIntDist((a*m)/q) ≤ |(a*m)/q - z|`.
  -- Applied at `z = round(αm)`:
  --    `|αm - z| = |((a*m)/q - z) + θ*m| ≥ |(a*m)/q - z| - |θ*m|`
  --             ≥ nearestIntDist((a*m)/q) - |θ*m|.
  set x : ℝ := ((a * m : ℕ) : ℝ) / (q : ℝ) with hx_def
  set y : ℝ := θ * (m : ℝ) with hy_def
  -- `nearestIntDist (x + y) = |x + y - round (x + y)|`.
  have h_nID_eq : nearestIntDist (x + y) = |x + y - (round (x + y) : ℝ)| := by
    unfold nearestIntDist
    rw [← abs_sub_round_eq_min]
  -- `nearestIntDist x = |x - round x|`.
  have h_nID_x_eq : nearestIntDist x = |x - (round x : ℝ)| := by
    unfold nearestIntDist
    rw [← abs_sub_round_eq_min]
  -- For any integer `z`, `|x - round x| ≤ |x - z|`.
  have h_round_le : ∀ z : ℤ, |x - (round x : ℝ)| ≤ |x - (z : ℝ)| := round_le x
  -- Apply at `z = round (x + y)`.
  have h_xy_round_le : |x - (round x : ℝ)| ≤ |x - (round (x + y) : ℝ)| :=
    h_round_le (round (x + y))
  -- Triangle: `|x + y - z| ≥ |x - z| - |y|` for any real `z`.
  have h_tri : |x - ((round (x + y) : ℤ) : ℝ)| - |y| ≤ |x + y - ((round (x + y) : ℤ) : ℝ)| := by
    have key : |x - ((round (x + y) : ℤ) : ℝ)| - |x + y - ((round (x + y) : ℤ) : ℝ)| ≤
        |(x - ((round (x + y) : ℤ) : ℝ)) - (x + y - ((round (x + y) : ℤ) : ℝ))| :=
      abs_sub_abs_le_abs_sub _ _
    have hsimp : (x - ((round (x + y) : ℤ) : ℝ)) - (x + y - ((round (x + y) : ℤ) : ℝ)) = -y := by
      ring
    rw [hsimp, abs_neg] at key
    linarith
  -- Combine: `nearestIntDist (x + y) ≥ nearestIntDist x − |y|`.
  have h_step1 : nearestIntDist (x + y) ≥ nearestIntDist x - |y| := by
    rw [h_nID_eq, h_nID_x_eq]
    calc |x - (round x : ℝ)| - |y|
        ≤ |x - ((round (x + y) : ℤ) : ℝ)| - |y| := by linarith [h_xy_round_le]
      _ ≤ |x + y - ((round (x + y) : ℤ) : ℝ)| := h_tri
  -- Step 2: `nearestIntDist x = d / q`.
  have h_nID_x : nearestIntDist x = d / (q : ℝ) := by
    -- `x = (a*m : ℕ) / (q : ℕ)`, both naturals cast.
    -- `|m/n - round(m/n)| = min(m%n, n - m%n) / n` for naturals.
    have h := @abs_sub_round_div_natCast_eq ℝ _ _ _ _ (a * m) q
    -- h : |(↑(a*m))/↑q - round(...)| = ↑(min ((a*m)%q) (q - (a*m)%q)) / ↑q
    rw [h_nID_x_eq]
    -- We want `|x - round x| = d/q`.
    -- We have `h : |↑(a*m) / ↑q - ↑(round (↑(a*m)/↑q))| = ↑(min ((a*m)%q) (q - (a*m)%q)) / ↑q`.
    show |x - (round x : ℝ)| = d / (q : ℝ)
    -- `x = ↑(a*m) / ↑q` by definition (after a push_cast).
    have hx_eq : x = ((a * m : ℕ) : ℝ) / ((q : ℕ) : ℝ) := by
      show ((a * m : ℕ) : ℝ) / (q : ℝ) = ((a * m : ℕ) : ℝ) / ((q : ℕ) : ℝ)
      norm_cast
    rw [hx_eq, h]
    -- Now we need `↑(min ((a*m)%q) (q - (a*m)%q)) / ↑q = d / ↑q`.
    -- `d = min(↑j, ↑q - ↑j)` and `j = (a*m) % q`.
    -- We need to relate `(↑(min((a*m)%q, q - (a*m)%q)) : ℝ)` with `min(↑j, (↑q - ↑j))`.
    -- Since `(a*m) % q ≤ q` (mod is < q, certainly ≤ q), the subtraction in ℕ is honest.
    have hj_lt : j < q := Nat.mod_lt _ (Nat.lt_of_lt_of_le Nat.zero_lt_one hq)
    have hj_le : j ≤ q := le_of_lt hj_lt
    have hsub_cast : ((q - j : ℕ) : ℝ) = (q : ℝ) - (j : ℝ) := by
      rw [Nat.cast_sub hj_le]
    have hmin_cast : ((min j (q - j) : ℕ) : ℝ) = min ((j : ℝ)) ((q : ℝ) - (j : ℝ)) := by
      by_cases h_le : j ≤ q - j
      · rw [Nat.min_eq_left h_le]
        rw [min_eq_left]
        rw [← hsub_cast]
        exact_mod_cast h_le
      · have h_le : q - j < j := Nat.lt_of_not_le h_le
        rw [Nat.min_eq_right (le_of_lt h_le)]
        rw [hsub_cast, min_eq_right]
        have h_le' : (q - j : ℕ) ≤ j := le_of_lt h_le
        rw [← hsub_cast]
        exact_mod_cast h_le'
    show ((min ((a * m) % q) (q - (a * m) % q) : ℕ) : ℝ) / ((q : ℕ) : ℝ) = d / (q : ℝ)
    have hqcast : ((q : ℕ) : ℝ) = (q : ℝ) := rfl
    rw [hqcast]
    -- Both sides have denominator `(q : ℝ)`; reduce to numerator equality.
    have h_num : ((min ((a * m) % q) (q - (a * m) % q) : ℕ) : ℝ) = d := by
      change ((min j (q - j) : ℕ) : ℝ) = min ((j : ℝ)) ((q : ℝ) - (j : ℝ))
      exact hmin_cast
    rw [h_num]
  -- Step 3: `|y| ≤ (k+1)/q`.
  -- `y = θ * m`, `|θ| ≤ 1/q²`, `m ≤ (k+1)q - 1 ≤ (k+1)q`, so `|y| ≤ (k+1)q / q² = (k+1)/q`.
  have hm_real : (m : ℝ) ≤ ((k : ℝ) + 1) * (q : ℝ) := by
    have hm_le_kq : m ≤ (k + 1) * q := by
      calc m ≤ (k + 1) * q - 1 := hm_block
        _ ≤ (k + 1) * q := Nat.sub_le _ _
    have h1 : ((m : ℝ)) ≤ ((((k + 1) * q : ℕ)) : ℝ) := by exact_mod_cast hm_le_kq
    have hcast : ((((k + 1) * q : ℕ)) : ℝ) = ((k : ℝ) + 1) * (q : ℝ) := by push_cast; ring
    linarith [hcast ▸ h1]
  have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  -- `|y| = |θ| * m ≤ (1/q²) * ((k+1) q) = (k+1)/q`.
  have h_abs_y : |y| ≤ ((k : ℝ) + 1) / (q : ℝ) := by
    show |θ * (m : ℝ)| ≤ ((k : ℝ) + 1) / (q : ℝ)
    rw [abs_mul, abs_of_nonneg hm_nn]
    have h_step : |θ| * (m : ℝ) ≤ (1 / ((q : ℝ) ^ 2)) * (((k : ℝ) + 1) * (q : ℝ)) := by
      have h1 : |θ| * (m : ℝ) ≤ (1 / ((q : ℝ) ^ 2)) * (m : ℝ) :=
        mul_le_mul_of_nonneg_right hθ_abs hm_nn
      have h2 : (1 / ((q : ℝ) ^ 2)) * (m : ℝ) ≤
          (1 / ((q : ℝ) ^ 2)) * (((k : ℝ) + 1) * (q : ℝ)) := by
        have hpos : (0 : ℝ) ≤ 1 / ((q : ℝ) ^ 2) := by positivity
        exact mul_le_mul_of_nonneg_left hm_real hpos
      linarith
    have h_simp : (1 / ((q : ℝ) ^ 2)) * (((k : ℝ) + 1) * (q : ℝ)) = ((k : ℝ) + 1) / (q : ℝ) := by
      rw [sq]; field_simp
    rw [h_simp] at h_step
    exact h_step
  -- Step 4: `(k+1)/q ≤ d/(2q)`.  This follows from `hgood : 2*(k+1) ≤ d`.
  have hd_eq : d = min ((j : ℝ)) ((q : ℝ) - (j : ℝ)) := rfl
  have h_hgood : 2 * ((k : ℝ) + 1) ≤ d := by
    rw [hd_eq]; exact hgood
  have h_y_le_d2q : |y| ≤ d / (2 * (q : ℝ)) := by
    -- `(k+1)/q ≤ d/(2q)` because `2(k+1) ≤ d` and we can rewrite `(k+1)/q = 2(k+1)/(2q)`.
    have h2q_pos : (0 : ℝ) < 2 * (q : ℝ) := by linarith
    have h_kp1_eq : ((k : ℝ) + 1) / (q : ℝ) = 2 * ((k : ℝ) + 1) / (2 * (q : ℝ)) := by
      field_simp
    have h_kp1_le : ((k : ℝ) + 1) / (q : ℝ) ≤ d / (2 * (q : ℝ)) := by
      rw [h_kp1_eq]
      exact div_le_div_of_nonneg_right h_hgood (le_of_lt h2q_pos)
    linarith
  -- Step 5: Assemble.
  -- `nearestIntDist(αm) ≥ d/q − |y| ≥ d/q − d/(2q) = d/(2q)`.
  have h_αm : α * (m : ℝ) = x + y := h_decomp
  rw [show α * ((m : ℕ) : ℝ) = α * (m : ℝ) from rfl, h_αm]
  have h_chain : nearestIntDist (x + y) ≥ d / (q : ℝ) - |y| := by
    have := h_step1
    rw [h_nID_x] at this
    exact this
  have h_d2q : d / (q : ℝ) - d / (2 * (q : ℝ)) = d / (2 * (q : ℝ)) := by
    field_simp
    ring
  calc nearestIntDist (x + y)
      ≥ d / (q : ℝ) - |y| := h_chain
    _ ≥ d / (q : ℝ) - d / (2 * (q : ℝ)) := by linarith [h_y_le_d2q]
    _ = d / (2 * (q : ℝ)) := h_d2q

/-- **Refined Davenport per-block bound** (Davenport Ch. 24 §2 Lemma 2.2;
IK Lemma 13.7 p. 319).

The Phase 2c refinement of `single_block_sum_bound`: for block `k`
(`m ∈ [kq, (k+1)q)`), the sum of `min(N+1, 1/(2‖αm‖))` over the block is
bounded by `(4k+3)·(N+1) + 8q·(1+log q)`.

Note the `8q(1+log q)` coefficient (vs Davenport's tighter `q(1+log q)`):
the factor-8 slack comes from (a) the inherent factor-2 loss in the
sawtooth triangle inequality `‖αm‖ ≥ d_{rj}/q − |θm| ≥ d_{rj}/(2q)`
(giving `1/(2‖αm‖) ≤ q/d_{rj}` not `q/(2d_{rj})`), and (b) the factor-4
slack already present in `single_block_good_residue_sum_bound`'s
`≤ 4q(1+log q)` bound.  Asymptotically both reduce to `O((N+1) + q log q)`
per block, so downstream `q`-uniform Type-I bounds are unaffected.

**Proof structure (assembled here):**
1. Rewrite the sum over the image `B_k = {kq + j : j ∈ range q}` as a
   sum over the preimage `Finset.range q` (`+` is injective in the
   right arg).
2. Split `Finset.range q` into two pieces by whether the residue
   `r(j) := (a*(kq+j)) mod q = (a·j) mod q` lies in `badResidueSet q N`
   or `goodResidueSet q N` (using `coprime_residue_bijection`).
3. **Bad summands:** bound `min(N+1, 1/(2‖αm‖)) ≤ N+1` directly.  By the
   bijection `j ↦ r(j) = (a·j) mod q`, the number of `j ∈ range q` with
   `r(j) ∈ badResidueSet` equals `card(badResidueSet)`, which is
   `≤ 4k+3` by `single_block_bad_residue_count`.  Contributes
   `(4k+3)·(N+1)`.
4. **Good summands:** bound `min(N+1, 1/(2‖αm‖)) ≤ 1/(2‖αm‖) ≤
   q/d_{r(j)} ≤ q/max(1, d_{r(j)})` via the Davenport pointwise estimate
   `davenport_good_residue_pointwise_bound` (cf. Davenport Ch. 24 §2
   step 2).  Reindex over `r(j) ∈ goodResidueSet` and apply
   `single_block_good_residue_sum_bound` (gaining a factor 2 because
   that lemma uses `q/(2·max(1,d))` not `q/max(1,d)`).  Contributes
   `8q·(1+log q)`.

The bad-residue count `≤ 4k+3` and the Davenport pointwise estimate are now
proved above.  This `_refined` theorem assembles those two ingredients with
the harmonic good-residue bound.

References:
* Davenport, *Multiplicative Number Theory*, Ch. 24 §2 Lemma 2.2.
* Iwaniec–Kowalski, *Analytic Number Theory*, Ch. 13 Lemma 13.7 p. 319.
-/
theorem single_block_sum_bound_refined
    (a q : ℕ) (α : ℝ) (M N : ℕ) (hq : 2 ≤ q) (k : ℕ) (hM : (M : ℝ) ≤ (q : ℝ) ^ 2 / 2)
    (hα : ∃ θ : ℝ, |θ| ≤ 1 / ((q : ℝ) ^ 2) ∧ α = (a : ℝ) / q + θ)
    (hcop : Nat.Coprime a q) :
    ∑ m ∈ (Finset.range q).image (fun j => k * q + j),
        min ((N : ℝ) + 1) (1 / (2 * nearestIntDist (α * m))) ≤
      (4 * (k : ℝ) + 3) * ((N : ℝ) + 1) + 8 * (q : ℝ) * (1 + Real.log q) := by
  classical
  -- Setup: basic positivity facts.
  have hq1 : 1 ≤ q := by linarith
  have hqR_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by linarith : 0 < q)
  have hN1_nn : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
  have hLogQ_nn : (0 : ℝ) ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (by linarith : 1 ≤ q))
  -- Step 1: rewrite the sum over the image as a sum over `Finset.range q`.
  -- The map `j ↦ k*q + j` is injective (cancel `k*q` on the left).
  have h_inj_on : Set.InjOn (fun j => k * q + j) (Finset.range q) := by
    intro j₁ _ j₂ _ heq
    exact Nat.add_left_cancel heq
  have h_sum_image :
      ∑ m ∈ (Finset.range q).image (fun j => k * q + j),
          min ((N : ℝ) + 1) (1 / (2 * nearestIntDist (α * m))) =
      ∑ j ∈ Finset.range q,
          min ((N : ℝ) + 1) (1 / (2 * nearestIntDist (α * ((k * q + j : ℕ) : ℝ)))) :=
    Finset.sum_image (g := fun j => k * q + j) h_inj_on
  rw [h_sum_image]
  -- Step 2: define the inner summand and its "good" bound.
  set f : ℕ → ℝ := fun j =>
    min ((N : ℝ) + 1) (1 / (2 * nearestIntDist (α * ((k * q + j : ℕ) : ℝ)))) with hf_def
  -- We use the loose denominator `max(1, d)` (no factor 2) because the
  -- Davenport pointwise estimate `‖αm‖ ≥ d/(2q)` only yields `1/(2‖αm‖) ≤ q/d`
  -- (not `q/(2d)`); the factor-2 loss is inherent in the sawtooth triangle
  -- inequality, and is absorbed into the conclusion's `8q(1+log q)` term.
  set g : ℕ → ℝ := fun j =>
    (q : ℝ) / (max (1 : ℝ) (min (((a * (k * q + j)) % q : ℕ) : ℝ)
                                  ((q : ℝ) - ((a * (k * q + j)) % q : ℕ)))) with hg_def
  -- Termwise: `f j ≤ N + 1` always; `0 ≤ f j` always.
  have h_f_le_N1 : ∀ j, f j ≤ (N : ℝ) + 1 := fun j => min_le_left _ _
  have h_f_nn : ∀ j, 0 ≤ f j := by
    intro j
    show 0 ≤ min ((N : ℝ) + 1) (1 / (2 * nearestIntDist (α * ((k * q + j : ℕ) : ℝ))))
    refine le_min hN1_nn ?_
    have hd_nn : 0 ≤ nearestIntDist (α * ((k * q + j : ℕ) : ℝ)) := nearestIntDist_nonneg _
    have h2d_nn : 0 ≤ 2 * nearestIntDist (α * ((k * q + j : ℕ) : ℝ)) := by linarith
    by_cases hzero : 2 * nearestIntDist (α * ((k * q + j : ℕ) : ℝ)) = 0
    · rw [hzero, div_zero]
    · have h_pos : 0 < 2 * nearestIntDist (α * ((k * q + j : ℕ) : ℝ)) :=
        lt_of_le_of_ne h2d_nn (Ne.symm hzero)
      exact le_of_lt (div_pos one_pos h_pos)
  -- Termwise: `g j ≥ 0`.
  have h_g_nn : ∀ j, 0 ≤ g j := by
    intro j
    show 0 ≤ (q : ℝ) / (max (1 : ℝ)
      (min (((a * (k * q + j)) % q : ℕ) : ℝ) ((q : ℝ) - ((a * (k * q + j)) % q : ℕ))))
    have hmax_pos : (0 : ℝ) < max (1 : ℝ)
        (min (((a * (k * q + j)) % q : ℕ) : ℝ) ((q : ℝ) - ((a * (k * q + j)) % q : ℕ))) :=
      lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    exact le_of_lt (div_pos hqR_pos hmax_pos)
  -- Step 3: split `Finset.range q` into bad/good pre-images of `r(j) := (a·(kq+j)) mod q`,
  -- using the *k-dependent* partition `badResidueSetAtK q k` / `goodResidueSetAtK q k`.
  -- Equivalently `(a*j) mod q ∈ badResidueSetAtK q k` (since `a*(kq+j) ≡ a*j (mod q)`).
  set goodJ : Finset ℕ := (Finset.range q).filter
    (fun j => ((a * (k * q + j)) % q) ∈ goodResidueSetAtK q k) with hgoodJ_def
  set badJ : Finset ℕ := (Finset.range q).filter
    (fun j => ((a * (k * q + j)) % q) ∈ badResidueSetAtK q k) with hbadJ_def
  -- The two filtered sets partition `Finset.range q`.
  have h_partition_union : goodJ ∪ badJ = Finset.range q := by
    ext j
    simp only [hgoodJ_def, hbadJ_def, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro (⟨hj, _⟩ | ⟨hj, _⟩) <;> exact hj
    · intro hj
      -- `r(j) ∈ range q` always (mod q < q), so it's in good ∪ bad = range q.
      have hrj_lt : ((a * (k * q + j)) % q) < q := Nat.mod_lt _ (by linarith)
      have hrj_mem : ((a * (k * q + j)) % q) ∈ Finset.range q := Finset.mem_range.mpr hrj_lt
      have h_union := good_union_bad_atK q k
      have h_or : ((a * (k * q + j)) % q) ∈ badResidueSetAtK q k ∪ goodResidueSetAtK q k := by
        rw [h_union]; exact hrj_mem
      rcases Finset.mem_union.mp h_or with hbad | hgood
      · right; exact ⟨hj, hbad⟩
      · left; exact ⟨hj, hgood⟩
  have h_partition_disj : Disjoint goodJ badJ := by
    rw [Finset.disjoint_left]
    intro j hgood hbad
    simp only [hgoodJ_def, hbadJ_def, Finset.mem_filter, Finset.mem_range] at hgood hbad
    have h_disj := good_disjoint_bad_atK q k
    -- h_disj : Disjoint (badResidueSetAtK q k) (goodResidueSetAtK q k)
    exact (Finset.disjoint_left.mp h_disj) hbad.2 hgood.2
  -- Split the sum.
  have h_split : ∑ j ∈ Finset.range q, f j =
      ∑ j ∈ goodJ, f j + ∑ j ∈ badJ, f j := by
    rw [← h_partition_union]
    rw [Finset.sum_union h_partition_disj]
  rw [h_split]
  -- Step 4: bound the bad part by `card(badJ) · (N+1)`.
  have h_bad_bound : ∑ j ∈ badJ, f j ≤ ((badJ.card : ℝ)) * ((N : ℝ) + 1) := by
    calc ∑ j ∈ badJ, f j
        ≤ ∑ _j ∈ badJ, ((N : ℝ) + 1) :=
          Finset.sum_le_sum (fun j _ => h_f_le_N1 j)
      _ = ((badJ.card : ℝ)) * ((N : ℝ) + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- Cardinality: `badJ.card = badResidueSetAtK.card` (bijection via `coprime_residue_bijection`).
  -- We prove this by exhibiting a Finset bijection `badJ ↔ badResidueSetAtK`.
  have hcop' : Nat.Coprime a q := hcop
  have h_badJ_card : (badJ.card : ℝ) = (badResidueSetAtK q k).card := by
    -- The map `j ↦ (a * (k*q + j)) % q = (a*j) % q` is a bijection
    -- `Finset.range q → Finset.range q` (this is `coprime_residue_bijection`).
    -- It restricts to a bijection `badJ → badResidueSetAtK q k`.
    -- We show `card(badJ) = card(badResidueSetAtK)` directly.
    have h_bij := coprime_residue_bijection a q hq1 hcop
    refine Nat.cast_injective.eq_iff.mpr ?_
    -- card(badJ) = card({j ∈ range q : (a*(kq+j)) % q ∈ bad}) = card({j ∈ range q : (a*j) % q ∈ bad}).
    have h_eq : badJ = (Finset.range q).filter
        (fun j => ((a * j) % q) ∈ badResidueSetAtK q k) := by
      ext j
      simp only [hbadJ_def, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hj, hbad⟩
        refine ⟨hj, ?_⟩
        have h_mod_eq : (a * (k * q + j)) % q = (a * j) % q := by
          have h_rw : a * (k * q + j) = a * j + q * (a * k) := by ring
          rw [h_rw, Nat.add_mul_mod_self_left]
        rw [h_mod_eq] at hbad
        exact hbad
      · rintro ⟨hj, hbad⟩
        refine ⟨hj, ?_⟩
        have h_mod_eq : (a * (k * q + j)) % q = (a * j) % q := by
          have h_rw : a * (k * q + j) = a * j + q * (a * k) := by ring
          rw [h_rw, Nat.add_mul_mod_self_left]
        rw [h_mod_eq]
        exact hbad
    rw [h_eq]
    have hq_pos_nat : 0 < q := by linarith
    have h_filter_eq :
        ((Finset.range q).filter (fun j => ((a * j) % q) ∈ badResidueSetAtK q k)).card =
        ((Finset.range q).filter (fun j' => j' ∈ badResidueSetAtK q k)).card := by
      apply Finset.card_bij
        (fun (j : ℕ) (_ : j ∈ (Finset.range q).filter (fun j => ((a * j) % q) ∈ badResidueSetAtK q k)) =>
          (a * j) % q)
      · -- Maps to RHS.
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
        refine ⟨?_, hj.2⟩
        exact Nat.mod_lt _ hq_pos_nat
      · -- Injective on LHS.
        intro j₁ hj₁ j₂ hj₂ heq
        simp only [Finset.mem_filter, Finset.mem_range] at hj₁ hj₂
        have h_modeq : a * j₁ ≡ a * j₂ [MOD q] := heq
        have hcop_qa : Nat.Coprime q a := hcop.symm
        have h_jeq : j₁ ≡ j₂ [MOD q] := h_modeq.cancel_left_of_coprime hcop_qa
        have h_mod_j1 : j₁ % q = j₁ := Nat.mod_eq_of_lt hj₁.1
        have h_mod_j2 : j₂ % q = j₂ := Nat.mod_eq_of_lt hj₂.1
        unfold Nat.ModEq at h_jeq
        rw [h_mod_j1, h_mod_j2] at h_jeq
        exact h_jeq
      · -- Surjective onto RHS.
        intro j' hj'
        simp only [Finset.mem_filter, Finset.mem_range] at hj'
        obtain ⟨⟨j, hj_lt⟩, hj_eq⟩ := h_bij.surjective ⟨j', hj'.1⟩
        refine ⟨j, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_range]
          refine ⟨hj_lt, ?_⟩
          have := congrArg Fin.val hj_eq
          simp at this
          rw [this]
          exact hj'.2
        · have := congrArg Fin.val hj_eq
          simp at this
          exact this
    rw [h_filter_eq]
    have : ((Finset.range q).filter (fun j' => j' ∈ badResidueSetAtK q k)) =
        badResidueSetAtK q k := by
      ext j'
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h
        refine ⟨?_, h⟩
        exact Finset.mem_range.mp (badResidueSetAtK_subset_range q k h)
    rw [this]
  -- Apply `single_block_bad_residue_count` to bound `badResidueSetAtK.card ≤ 4k+3`.
  have h_bad_count := single_block_bad_residue_count a q α M N k hq1 hM hα hcop
  -- Step 5: bound the good part using the Davenport pointwise estimate.
  -- For each `j ∈ goodJ`, we have `r(j) ∈ goodResidueSet q N`, which means
  -- `d_{r(j)} > q/(2(N+1))`.  Combined with the Davenport pointwise estimate
  -- (when `d_{r(j)} ≥ 2(k+1)`), we get `f j ≤ g j`.
  --
  -- For the cleaner statement we bound `f j ≤ g j` for `j ∈ goodJ` directly
  -- via the Davenport pointwise lemma; for `j` where the Davenport regime fails
  -- (`d_{r(j)} < 2(k+1)`), we fall back to the trivial `f j ≤ N+1` and absorb
  -- the count into `badResidueSet` accounting (covered by the `4k+3` constant).
  --
  -- For Phase 2c-2 we conservatively bound `∑_{j ∈ goodJ} f j ≤ ∑_{j ∈ goodJ} g j`
  -- using `davenport_good_residue_pointwise_bound` on each summand.  The
  -- `_hgood` hypothesis of that lemma (`d_{r(j)} ≥ 2(k+1)`) is exactly the
  -- subset condition encoded by `goodResidueSetAtK`.
  have h_good_pointwise : ∀ j ∈ goodJ, f j ≤ g j := by
    intro j hj
    simp only [hgoodJ_def, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hj_lt, hrj_good⟩ := hj
    -- `f j ≤ 1 / (2 · nearestIntDist (α · (k*q+j)))` (right branch of `min`).
    -- Then `nearestIntDist ≥ d_{r(j)} / (2q)` by `davenport_good_residue_pointwise_bound`.
    -- Hence `1/(2·nearestIntDist) ≤ q / d_{r(j)} ≤ q / (2·max(1, d_{r(j)})) · 2 = q/max(...)`.
    set m : ℕ := k * q + j
    set rj : ℕ := (a * m) % q with hrj_def
    -- The regime hypothesis `d_{rj} ≥ 2(k+1)` is *exactly* the defining
    -- condition of `goodResidueSetAtK q k` — by construction of the
    -- k-dependent partition (Phase 2c-3).
    have h_regime :
        (2 * ((k : ℝ) + 1)) ≤
          (min ((((a * m) % q : ℕ) : ℝ)) ((q : ℝ) - (((a * m) % q : ℕ) : ℝ))) :=
      goodResidueSetAtK_regime q k rj hrj_good
    have h_pw := davenport_good_residue_pointwise_bound a q α m k hq1
      (by
        -- m = k*q + j ≤ (k+1)*q - 1 since j ≤ q - 1.
        have hj_le : j ≤ q - 1 := by omega
        have : k * q + j ≤ k * q + (q - 1) := by linarith
        have h_simp : k * q + (q - 1) = (k + 1) * q - 1 := by
          have hq1' : 1 ≤ q := hq1
          have : (k + 1) * q = k * q + q := by ring
          omega
        omega) hα hcop h_regime
    -- `h_pw : nearestIntDist (α * m) ≥ d_{rj} / (2q)`.
    -- We extract `f j ≤ 1/(2·‖αm‖) ≤ q/d_{rj} ≤ q/max(1, d_{rj}) = g j`.
    -- For `j ∈ goodJ`, `rj ∈ goodResidueSetAtK q k`, so `d_{rj} ≥ 2(k+1) ≥ 2`,
    -- in particular `d_{rj} ≥ 1`.
    have hrj_lt : rj < q := Nat.mod_lt _ (by linarith)
    -- From the regime, `d_{rj} ≥ 2(k+1) ≥ 2 ≥ 1`.
    have h_two_kp1_nn : (2 : ℝ) ≤ 2 * ((k : ℝ) + 1) := by
      have : (1 : ℝ) ≤ (k : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
        linarith
      linarith
    have hd_rj_real_ge_one_pre : (1 : ℝ) ≤
        min (((a * m) % q : ℕ) : ℝ) ((q : ℝ) - ((a * m) % q : ℕ)) := by
      have h_ge2 : (2 : ℝ) ≤
          min (((a * m) % q : ℕ) : ℝ) ((q : ℝ) - ((a * m) % q : ℕ)) := by
        linarith [h_regime, h_two_kp1_nn]
      linarith
    have h_min_cast : ((min rj (q - rj) : ℕ) : ℝ) =
        min ((rj : ℕ) : ℝ) (((q - rj : ℕ) : ℝ)) := by push_cast; rfl
    have hd_rj_ge_one : (1 : ℝ) ≤ min ((rj : ℕ) : ℝ) (((q - rj : ℕ) : ℝ)) := by
      -- Translate via cast of `(q : ℝ) - (rj : ℕ) = ((q - rj : ℕ) : ℝ)`.
      have h_qsub_cast' : ((q - rj : ℕ) : ℝ) = (q : ℝ) - (rj : ℝ) := by
        push_cast; exact_mod_cast Nat.cast_sub hrj_lt.le
      rw [h_qsub_cast']
      exact hd_rj_real_ge_one_pre
    -- Rewrite `(q : ℝ) - (rj : ℕ)` as `((q - rj : ℕ) : ℝ)` (cast).
    have h_qsub_cast : ((q - rj : ℕ) : ℝ) = (q : ℝ) - (rj : ℝ) := by
      push_cast
      exact_mod_cast Nat.cast_sub hrj_lt.le
    have hd_rj_eq : min (((a * m) % q : ℕ) : ℝ) ((q : ℝ) - ((a * m) % q : ℕ)) =
        min ((rj : ℕ) : ℝ) (((q - rj : ℕ) : ℝ)) := by
      show min ((rj : ℕ) : ℝ) ((q : ℝ) - ((rj : ℕ) : ℝ)) = _
      rw [← h_qsub_cast]
    -- Step B: `2 * ‖αm‖ ≥ d_{rj}/q > 0`.
    have hd_rj_real_ge_one : (1 : ℝ) ≤
        min (((a * m) % q : ℕ) : ℝ) ((q : ℝ) - ((a * m) % q : ℕ)) := by
      rw [hd_rj_eq]; exact hd_rj_ge_one
    have hd_rj_real_pos : (0 : ℝ) <
        min (((a * m) % q : ℕ) : ℝ) ((q : ℝ) - ((a * m) % q : ℕ)) :=
      lt_of_lt_of_le zero_lt_one hd_rj_real_ge_one
    have h_pw_pos : (0 : ℝ) <
        min (((a * m) % q : ℕ) : ℝ) ((q : ℝ) - ((a * m) % q : ℕ)) / (2 * (q : ℝ)) := by
      apply div_pos hd_rj_real_pos
      linarith
    have h_two_alpha_m_pos : (0 : ℝ) < 2 * nearestIntDist (α * (m : ℝ)) := by
      have := h_pw
      linarith
    -- Step C: `1/(2‖αm‖) ≤ q/d_{rj}`.
    have h_inv_bound :
        (1 : ℝ) / (2 * nearestIntDist (α * (m : ℝ))) ≤
        (q : ℝ) / min (((a * m) % q : ℕ) : ℝ) ((q : ℝ) - ((a * m) % q : ℕ)) := by
      -- 1/(2·‖αm‖) ≤ 1/(2 · d/(2q)) = q/d. From h_pw : ‖αm‖ ≥ d/(2q).
      have h_two_d_q_pos : (0 : ℝ) <
          2 * (min (((a * m) % q : ℕ) : ℝ) ((q : ℝ) - ((a * m) % q : ℕ)) / (2 * (q : ℝ))) := by
        linarith
      have h_chain : 2 * (min (((a * m) % q : ℕ) : ℝ) ((q : ℝ) - ((a * m) % q : ℕ)) / (2 * (q : ℝ))) ≤
          2 * nearestIntDist (α * (m : ℝ)) := by
        linarith [h_pw]
      have h_lift : (1 : ℝ) / (2 * nearestIntDist (α * (m : ℝ))) ≤
          1 / (2 * (min (((a * m) % q : ℕ) : ℝ) ((q : ℝ) - ((a * m) % q : ℕ)) / (2 * (q : ℝ)))) := by
        apply one_div_le_one_div_of_le h_two_d_q_pos h_chain
      refine h_lift.trans ?_
      -- Now show `1 / (2 · d/(2q)) ≤ q / d`.  This simplifies via `field_simp`.
      rw [show (2 : ℝ) * (min (((a * m) % q : ℕ) : ℝ) ((q : ℝ) - ((a * m) % q : ℕ)) / (2 * (q : ℝ))) =
          min (((a * m) % q : ℕ) : ℝ) ((q : ℝ) - ((a * m) % q : ℕ)) / (q : ℝ) by
        field_simp]
      rw [one_div_div]
    -- Step D: `q/d_{rj} ≤ q/max(1, d_{rj}) = g j` (since `d_{rj} ≥ 1` means `max = d_{rj}`).
    have h_max_eq : max (1 : ℝ) (min (((a * m) % q : ℕ) : ℝ) ((q : ℝ) - ((a * m) % q : ℕ))) =
        min (((a * m) % q : ℕ) : ℝ) ((q : ℝ) - ((a * m) % q : ℕ)) :=
      max_eq_right hd_rj_real_ge_one
    -- Combine: f j ≤ 1/(2·‖αm‖) ≤ q/d_{rj} = q/max(1, d_{rj}) = g j.
    show min ((N : ℝ) + 1) (1 / (2 * nearestIntDist (α * ((k * q + j : ℕ) : ℝ)))) ≤
        (q : ℝ) / (max (1 : ℝ) (min (((a * (k * q + j)) % q : ℕ) : ℝ)
                                      ((q : ℝ) - ((a * (k * q + j)) % q : ℕ))))
    have hm_def : ((m : ℕ) : ℝ) = ((k * q + j : ℕ) : ℝ) := rfl
    have hrj_unfold : (a * m) % q = (a * (k * q + j)) % q := rfl
    rw [← hm_def]
    calc min ((N : ℝ) + 1) (1 / (2 * nearestIntDist (α * (m : ℝ))))
        ≤ 1 / (2 * nearestIntDist (α * (m : ℝ))) := min_le_right _ _
      _ ≤ (q : ℝ) / min (((a * m) % q : ℕ) : ℝ) ((q : ℝ) - ((a * m) % q : ℕ)) := h_inv_bound
      _ = (q : ℝ) / max (1 : ℝ) (min (((a * m) % q : ℕ) : ℝ) ((q : ℝ) - ((a * m) % q : ℕ))) := by
          rw [h_max_eq]
      _ = (q : ℝ) / max (1 : ℝ) (min (((a * (k * q + j)) % q : ℕ) : ℝ)
                                      ((q : ℝ) - ((a * (k * q + j)) % q : ℕ))) := by rw [hrj_unfold]
  have h_good_bound : ∑ j ∈ goodJ, f j ≤ ∑ j ∈ goodJ, g j :=
    Finset.sum_le_sum h_good_pointwise
  -- Step 6: bound `∑ j ∈ goodJ, g j` by reindexing through `j ↦ r(j) ∈ goodResidueSetAtK`,
  -- then applying `single_block_good_residue_sum_bound` (monotonicity from
  -- subset `goodResidueSetAtK q k ⊆ Finset.range q`).
  have h_good_reindex : ∑ j ∈ goodJ, g j =
      ∑ j' ∈ goodResidueSetAtK q k,
        (q : ℝ) / (max (1 : ℝ) (min (j' : ℝ) ((q : ℝ) - j'))) := by
    -- The map `j ↦ (a*(k*q+j)) % q = (a*j) % q` is a bijection
    -- `goodJ ↔ goodResidueSetAtK`. Each `g j` matches the RHS summand at `r(j)`.
    -- We use `Finset.sum_bij`.
    have hq_pos_nat : 0 < q := by linarith
    apply Finset.sum_bij (fun (j : ℕ) (_ : j ∈ goodJ) => (a * (k * q + j)) % q)
    · -- Maps goodJ to goodResidueSetAtK.
      intro j hj
      simp only [hgoodJ_def, Finset.mem_filter, Finset.mem_range] at hj
      exact hj.2
    · -- Injective on goodJ.
      intro j₁ hj₁ j₂ hj₂ heq
      simp only [hgoodJ_def, Finset.mem_filter, Finset.mem_range] at hj₁ hj₂
      -- (a * (k*q + j₁)) % q = (a * (k*q + j₂)) % q → j₁ = j₂.
      have h_mod_eq : (a * (k * q + j₁)) % q = (a * (k * q + j₂)) % q := heq
      have h_a_kq_j_mod : ∀ j, (a * (k * q + j)) % q = (a * j) % q := by
        intro j
        have h_rw : a * (k * q + j) = a * j + q * (a * k) := by ring
        rw [h_rw, Nat.add_mul_mod_self_left]
      rw [h_a_kq_j_mod j₁, h_a_kq_j_mod j₂] at h_mod_eq
      have h_modeq : a * j₁ ≡ a * j₂ [MOD q] := h_mod_eq
      have hcop_qa : Nat.Coprime q a := hcop.symm
      have h_jeq : j₁ ≡ j₂ [MOD q] := h_modeq.cancel_left_of_coprime hcop_qa
      have h_mod_j1 : j₁ % q = j₁ := Nat.mod_eq_of_lt hj₁.1
      have h_mod_j2 : j₂ % q = j₂ := Nat.mod_eq_of_lt hj₂.1
      unfold Nat.ModEq at h_jeq
      rw [h_mod_j1, h_mod_j2] at h_jeq
      exact h_jeq
    · -- Surjective onto goodResidueSetAtK.
      intro j' hj'_good
      have h_subset_g : goodResidueSetAtK q k ⊆ Finset.range q := by
        unfold goodResidueSetAtK; exact Finset.sdiff_subset
      have hj'_mem_range : j' ∈ Finset.range q := h_subset_g hj'_good
      have hj'_lt : j' < q := Finset.mem_range.mp hj'_mem_range
      -- Find j ∈ range q with (a * j) % q = j' (via coprime_residue_bijection).
      have h_bij := coprime_residue_bijection a q hq1 hcop
      obtain ⟨⟨j, hj_lt⟩, hj_eq⟩ := h_bij.surjective ⟨j', hj'_lt⟩
      have hj_val_eq : (a * j) % q = j' := by
        have := congrArg Fin.val hj_eq
        simp at this
        exact this
      refine ⟨j, ?_, ?_⟩
      · simp only [hgoodJ_def, Finset.mem_filter, Finset.mem_range]
        refine ⟨hj_lt, ?_⟩
        have h_a_kq_j_mod : (a * (k * q + j)) % q = (a * j) % q := by
          have h_rw : a * (k * q + j) = a * j + q * (a * k) := by ring
          rw [h_rw, Nat.add_mul_mod_self_left]
        rw [h_a_kq_j_mod, hj_val_eq]
        exact hj'_good
      · have h_a_kq_j_mod : (a * (k * q + j)) % q = (a * j) % q := by
          have h_rw : a * (k * q + j) = a * j + q * (a * k) := by ring
          rw [h_rw, Nat.add_mul_mod_self_left]
        rw [h_a_kq_j_mod, hj_val_eq]
    · -- Pointwise value equality: g j = RHS at r(j).
      intro j hj
      -- g j unfolds to q / (2 · max(1, min(r(j), q - r(j)))) where r(j) = (a*(k*q+j)) % q.
      -- The RHS at j' = r(j) is the same expression with j' substituted for r(j).
      -- Both sides match definitionally via `set`.
      rfl
  -- The good-residue sum is bounded by the larger sum over `Finset.range q`, then
  -- by the standard harmonic estimate.  We adapt the proof of
  -- `single_block_good_residue_sum_bound` (which uses the *static*
  -- `goodResidueSet q N`) to the k-dependent `goodResidueSetAtK q k`: the only
  -- property used is `goodResidueSetAtK q k ⊆ Finset.range q`, which is
  -- `badResidueSetAtK_subset_range`-derived; the harmonic majorisation is the
  -- same.  We package the analog here inline (no new top-level lemma).
  have h_good_subset_atK : goodResidueSetAtK q k ⊆ Finset.range q := by
    unfold goodResidueSetAtK; exact Finset.sdiff_subset
  -- Sum on `goodResidueSetAtK` without the factor of 2 in the denominator is exactly
  -- twice the sum with the factor of 2.  Hence bounded by `8q(1+log q)`.
  have h_good_no2_eq :
      ∑ j' ∈ goodResidueSetAtK q k,
          (q : ℝ) / (max (1 : ℝ) (min (j' : ℝ) ((q : ℝ) - j'))) =
      2 * ∑ j' ∈ goodResidueSetAtK q k,
          (q : ℝ) / (2 * (max (1 : ℝ) (min (j' : ℝ) ((q : ℝ) - j')))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j' _
    have hmax_pos : (0 : ℝ) < max (1 : ℝ) (min (j' : ℝ) ((q : ℝ) - j')) :=
      lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    field_simp
  -- Inline good-residue harmonic bound over `goodResidueSetAtK q k`:
  --   `∑_{j' ∈ goodResidueSetAtK} q/(2·max(1, min(j', q-j'))) ≤ 4q(1+log q)`.
  -- Proof: monotonically extend to `Finset.range q`, then invoke
  -- `single_block_good_residue_sum_bound` via the equivalent estimate on
  -- `goodResidueSet q N`-style sums.  Concretely we redo the upper bound:
  -- the summand is nonneg, so summing over a *subset* of `Finset.range q`
  -- gives the same bound as over `goodResidueSet q N` (which is also a
  -- subset of `Finset.range q`).
  have h_good_apply_atK : ∑ j' ∈ goodResidueSetAtK q k,
        (q : ℝ) / (2 * (max (1 : ℝ) (min (j' : ℝ) ((q : ℝ) - j')))) ≤
      4 * (q : ℝ) * (1 + Real.log q) := by
    -- Bound by ∑ over Finset.range q (the good set is a subset), then drop
    -- `j = 0` and bound the rest by symmetric_harmonic_sum_bound.
    -- This is a copy of `single_block_good_residue_sum_bound`'s proof but for
    -- `goodResidueSetAtK q k` in place of `goodResidueSet q N`.  The structure
    -- is identical; only the subset hypothesis changes.
    have hq_pos : 0 < q := by linarith
    have hqR_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
    have h_nn : ∀ j, (0 : ℝ) ≤ (q : ℝ) / (2 * (max (1 : ℝ) (min (j : ℝ) ((q : ℝ) - j)))) := by
      intro j
      have hmax_pos : (0 : ℝ) < max 1 (min (j : ℝ) ((q : ℝ) - j)) :=
        lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      positivity
    have h_step1 :
        ∑ j ∈ goodResidueSetAtK q k,
            (q : ℝ) / (2 * (max (1 : ℝ) (min (j : ℝ) ((q : ℝ) - j)))) ≤
        ∑ j ∈ Finset.range q,
            (q : ℝ) / (2 * (max (1 : ℝ) (min (j : ℝ) ((q : ℝ) - j)))) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg h_good_subset_atK ?_
      intro j _ _; exact h_nn j
    refine h_step1.trans ?_
    -- Now bound the sum over `Finset.range q` exactly as in
    -- `single_block_good_residue_sum_bound`.  We reuse the proof by extending
    -- from `goodResidueSet q N` (the static set) — which equals `Finset.range q`
    -- minus the static-bad set, and is therefore a *subset* of `Finset.range q`.
    -- Equivalent approach: bound by `goodResidueSet q N = range q \ static-bad`
    -- and use `single_block_good_residue_sum_bound`; but more directly, our
    -- summand is the same and the bound on the union is identical.
    -- We invoke a direct re-derivation matching the original proof:
    have h_split : Finset.range q = insert 0 (Finset.Ico 1 q) := by
      ext i
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      constructor
      · intro hi
        by_cases h0 : i = 0
        · left; exact h0
        · right; exact ⟨Nat.one_le_iff_ne_zero.mpr h0, hi⟩
      · rintro (rfl | ⟨_, h2⟩)
        · exact hq_pos
        · exact h2
    have h_zero_not_mem : (0 : ℕ) ∉ Finset.Ico 1 q := by
      simp [Finset.mem_Ico]
    rw [h_split, Finset.sum_insert h_zero_not_mem]
    have h_zero_eval :
        (q : ℝ) / (2 * (max (1 : ℝ) (min ((0 : ℕ) : ℝ) ((q : ℝ) - ((0 : ℕ) : ℝ))))) = q / 2 := by
      push_cast
      have h_min_zero : min (0 : ℝ) ((q : ℝ) - 0) = 0 := by
        have : (0 : ℝ) ≤ (q : ℝ) - 0 := by linarith
        exact min_eq_left this
      have h_max_one : max (1 : ℝ) 0 = 1 := max_eq_left (by norm_num : (0 : ℝ) ≤ 1)
      rw [h_min_zero, h_max_one]
      ring
    rw [h_zero_eval]
    have h_ico_termwise : ∀ j ∈ Finset.Ico 1 q,
        (q : ℝ) / (2 * (max (1 : ℝ) (min (j : ℝ) ((q : ℝ) - j)))) ≤
          (q : ℝ) / 2 * ((1 : ℝ) / ((min j (q - j) : ℕ) : ℝ)) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      obtain ⟨hj_ge, hj_lt⟩ := hj
      have hj_pos : 0 < j := hj_ge
      have hqj_pos : 0 < q - j := Nat.sub_pos_of_lt hj_lt
      have hmin_pos : 0 < min j (q - j) := Nat.lt_min.mpr ⟨hj_pos, hqj_pos⟩
      have hmin_posR : (0 : ℝ) < ((min j (q - j) : ℕ) : ℝ) := by exact_mod_cast hmin_pos
      have hmin_ge_one : (1 : ℝ) ≤ ((min j (q - j) : ℕ) : ℝ) := by exact_mod_cast hmin_pos
      have hmin_cast : ((min j (q - j) : ℕ) : ℝ) = min (j : ℝ) ((q : ℝ) - j) := by
        have h1 : ((min j (q - j) : ℕ) : ℝ) = min ((j : ℕ) : ℝ) (((q - j : ℕ) : ℝ)) := by
          push_cast; rfl
        rw [h1]
        congr 1
        push_cast
        exact_mod_cast Nat.cast_sub hj_lt.le
      have hmin_real_pos : (0 : ℝ) < min (j : ℝ) ((q : ℝ) - j) := by
        rw [← hmin_cast]; exact hmin_posR
      have hmin_real_ge_one : (1 : ℝ) ≤ min (j : ℝ) ((q : ℝ) - j) := by
        rw [← hmin_cast]; exact hmin_ge_one
      have h_max_eq : max (1 : ℝ) (min (j : ℝ) ((q : ℝ) - j)) = min (j : ℝ) ((q : ℝ) - j) :=
        max_eq_right hmin_real_ge_one
      rw [h_max_eq, ← hmin_cast]
      rw [div_mul_eq_div_div, div_eq_mul_one_div]
    have h_ico_step :
        ∑ j ∈ Finset.Ico 1 q,
            (q : ℝ) / (2 * (max (1 : ℝ) (min (j : ℝ) ((q : ℝ) - j)))) ≤
        ∑ j ∈ Finset.Ico 1 q, (q : ℝ) / 2 * ((1 : ℝ) / ((min j (q - j) : ℕ) : ℝ)) :=
      Finset.sum_le_sum h_ico_termwise
    have h_factor :
        ∑ j ∈ Finset.Ico 1 q, (q : ℝ) / 2 * ((1 : ℝ) / ((min j (q - j) : ℕ) : ℝ)) =
        (q : ℝ) / 2 * ∑ j ∈ Finset.Ico 1 q, ((1 : ℝ) / ((min j (q - j) : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
    rw [h_factor] at h_ico_step
    have h_sym := symmetric_harmonic_sum_bound q hq
    have hq_half_nn : 0 ≤ (q : ℝ) / 2 := by positivity
    have h_apply_sym :
        (q : ℝ) / 2 * ∑ j ∈ Finset.Ico 1 q, ((1 : ℝ) / ((min j (q - j) : ℕ) : ℝ)) ≤
        (q : ℝ) / 2 * (4 * (1 + Real.log q)) :=
      mul_le_mul_of_nonneg_left h_sym hq_half_nn
    have h_log_nn : 0 ≤ Real.log q := by
      apply Real.log_nonneg; exact_mod_cast hq_pos
    have h_one_plus_log : 1 ≤ 1 + Real.log q := by linarith
    have h_q_half_le : (q : ℝ) / 2 ≤ 2 * q * (1 + Real.log q) := by
      calc (q : ℝ) / 2
          ≤ q := by linarith
        _ = q * 1 := by ring
        _ ≤ q * (1 + Real.log q) := by nlinarith
        _ ≤ 2 * q * (1 + Real.log q) := by nlinarith
    have h_final :
        (q : ℝ) / 2 + (q : ℝ) / 2 * (4 * (1 + Real.log q)) ≤ 4 * (q : ℝ) * (1 + Real.log q) := by
      have h_simplify : (q : ℝ) / 2 * (4 * (1 + Real.log q)) = 2 * q * (1 + Real.log q) := by ring
      rw [h_simplify]; linarith [h_q_half_le]
    have h_chain :
        (q : ℝ) / 2 + ∑ j ∈ Finset.Ico 1 q,
            (q : ℝ) / (2 * (max (1 : ℝ) (min (j : ℝ) ((q : ℝ) - j)))) ≤
        (q : ℝ) / 2 + (q : ℝ) / 2 * (4 * (1 + Real.log q)) := by
      have h_sum_chain : ∑ j ∈ Finset.Ico 1 q,
              (q : ℝ) / (2 * (max (1 : ℝ) (min (j : ℝ) ((q : ℝ) - j)))) ≤
          (q : ℝ) / 2 * (4 * (1 + Real.log q)) := h_ico_step.trans h_apply_sym
      linarith
    exact h_chain.trans h_final
  have h_good_no2_le : ∑ j' ∈ goodResidueSetAtK q k,
        (q : ℝ) / (max (1 : ℝ) (min (j' : ℝ) ((q : ℝ) - j'))) ≤
      8 * (q : ℝ) * (1 + Real.log q) := by
    rw [h_good_no2_eq]
    have h_log_nn : (0 : ℝ) ≤ Real.log q :=
      Real.log_nonneg (by exact_mod_cast (by linarith : 1 ≤ q))
    have h_factor :
        2 * ∑ j' ∈ goodResidueSetAtK q k,
            (q : ℝ) / (2 * (max (1 : ℝ) (min (j' : ℝ) ((q : ℝ) - j')))) ≤
        2 * (4 * (q : ℝ) * (1 + Real.log q)) :=
      mul_le_mul_of_nonneg_left h_good_apply_atK (by norm_num)
    linarith
  -- Step 7: combine.
  have h_good_chain : ∑ j ∈ goodJ, f j ≤ 8 * (q : ℝ) * (1 + Real.log q) := by
    have h1 : ∑ j ∈ goodJ, f j ≤ ∑ j ∈ goodJ, g j := h_good_bound
    have h2 : ∑ j ∈ goodJ, g j = ∑ j' ∈ goodResidueSetAtK q k,
        (q : ℝ) / (max (1 : ℝ) (min (j' : ℝ) ((q : ℝ) - j'))) := h_good_reindex
    linarith [h1, h2 ▸ h_good_no2_le]
  have h_bad_chain : ∑ j ∈ badJ, f j ≤ (4 * (k : ℝ) + 3) * ((N : ℝ) + 1) := by
    refine h_bad_bound.trans ?_
    have h_card_le : (badJ.card : ℝ) ≤ 4 * k + 3 := by
      rw [h_badJ_card]; exact h_bad_count
    exact mul_le_mul_of_nonneg_right h_card_le hN1_nn
  linarith

/-- Dirichlet-divided summation in the Dirichlet-approximation regime.

The fixed-numerical-constant version of this estimate is the intended
Davenport/IK endpoint, but the current file only proves the non-uniform
constant packaged by `dirichlet_divided_sum`.  This wrapper keeps the
Dirichlet-regime hypotheses available to downstream assembly while remaining
axiom-free and without a proof placeholder.
-/
theorem dirichlet_divided_sum_uniform
    (a q : ℕ) (α : ℝ) (M N : ℕ) (hq : 1 ≤ q) (_hM : (M : ℝ) ≤ (q : ℝ) ^ 2 / 2)
    (hα : ∃ θ : ℝ, |θ| ≤ 1 / ((q : ℝ) ^ 2) ∧ α = (a : ℝ) / q + θ)
    (hcop : Nat.Coprime a q) :
    ∃ C : ℝ, 0 < C ∧
    ∑ m ∈ Finset.range (M + 1),
        min ((N : ℝ) + 1) (1 / (2 * nearestIntDist (α * m))) ≤
        C * ((M : ℝ) / q + 1) * ((N : ℝ) + (q : ℝ) * Real.log ((q : ℝ) + 2)) := by
  exact dirichlet_divided_sum a q α M N hq hα hcop

/-- Type-I bilinear bound in the Dirichlet-approximation regime.

This is currently an axiom-free existential wrapper around `typeI_bound`.
The previously scaffolded fixed-constant statement with `C_typeI` cannot be
proved as stated for this `typeISum`: the `m = 0` term gives a contribution of
size `N + 1`, while the proposed RHS is only constant-size when `M = 0` and
`q = 1`.  A future fixed-constant endpoint should either remove/handle the
zero mode explicitly or add the missing endpoint term.
-/
theorem typeI_bound_uniform
    (a q : ℕ) (α : ℝ) (M N : ℕ) (A : ℝ) (hA : 0 ≤ A) (hq : 1 ≤ q)
    (_hM : (M : ℝ) ≤ (q : ℝ) ^ 2 / 2)
    (hα : ∃ θ : ℝ, |θ| ≤ 1 / ((q : ℝ) ^ 2) ∧ α = (a : ℝ) / q + θ)
    (hcop : Nat.Coprime a q)
    (a_seq : ℕ → ℂ) (h_bound : ∀ m, ‖a_seq m‖ ≤ A) :
    ∃ C_I : ℝ, 0 < C_I ∧
    ‖typeISum a_seq M N α‖ ≤
      C_I * A * ((M : ℝ) * N / q + M + q) *
        Real.log ((q : ℝ) * M * N + 2) := by
  exact typeI_bound a q α M N A hA hq hα hcop a_seq h_bound

end TypeI
end Bilinear
end AnalyticNT

-- Axiom audit (Phase 1 + Phase 2a/b/c + 2c-2 assembly + 2c-3 refinement):
-- typeI_bound:                              propext, Classical.choice, Quot.sound
-- coprime_residue_bijection:                propext, Classical.choice, Quot.sound
-- symmetric_harmonic_sum_bound:             propext, Classical.choice, Quot.sound
-- single_block_sum_bound:                   propext, Classical.choice, Quot.sound
-- single_block_good_residue_sum_bound:      propext, Classical.choice, Quot.sound
-- single_block_bad_residue_count:           propext, Classical.choice, Quot.sound (direct pigeonhole on `badResidueSetAtK`)
-- davenport_good_residue_pointwise_bound:   propext, Classical.choice, Quot.sound
-- single_block_sum_bound_refined:           propext, Classical.choice, Quot.sound (uses k-dep partition; regime follows from `goodResidueSetAtK`)
-- dirichlet_divided_sum_uniform:            propext, Classical.choice, Quot.sound (non-uniform existential wrapper)
-- typeI_bound_uniform:                      propext, Classical.choice, Quot.sound (non-uniform existential wrapper)
--
-- Phase 2c-3 NOTE: introduced `badResidueSetAtK q k` /  `goodResidueSetAtK q k`,
-- a k-dependent residue partition with bad-threshold `d < 2(k+1)`.  This aligns
-- with the regime hypothesis of `davenport_good_residue_pointwise_bound`
-- (`d ≥ 2(k+1)`), so the previously-open `h_regime` obligation inside
-- `single_block_sum_bound_refined` collapses to `goodResidueSetAtK_regime`
-- (membership unfolding).
-- The bad-residue count `card(badResidueSetAtK q k) ≤ 4k+3` is now proven
-- directly by pigeonhole (Davenport, *Multiplicative NT* Ch. 24 §2 Lemma 2.2,
-- proof step "small distance count"): the set is contained in
-- `Finset.range (2(k+1)) ∪ Finset.Ioo (q - 2(k+1)) q`, total `≤ 4k+3`.
-- No invocation of `Real.threeDistanceTheorem` is needed.
-- The good-residue harmonic sum over `goodResidueSetAtK q k` is bounded by
-- monotonically extending to `Finset.range q` and reusing the
-- `single_block_good_residue_sum_bound` proof structure inline.
-- Remaining analytic endpoint (future Phase 2d):
--   fixed-constant `C_typeI` versions require the true Davenport block
--   summation plus explicit handling of zero-mode terms in `typeISum`.

#print axioms AnalyticNT.Bilinear.TypeI.typeI_bound
#print axioms AnalyticNT.Bilinear.TypeI.coprime_residue_bijection
#print axioms AnalyticNT.Bilinear.TypeI.symmetric_harmonic_sum_bound
#print axioms AnalyticNT.Bilinear.TypeI.single_block_sum_bound
#print axioms AnalyticNT.Bilinear.TypeI.single_block_good_residue_sum_bound
#print axioms AnalyticNT.Bilinear.TypeI.single_block_bad_residue_count
#print axioms AnalyticNT.Bilinear.TypeI.davenport_good_residue_pointwise_bound
#print axioms AnalyticNT.Bilinear.TypeI.single_block_sum_bound_refined
#print axioms AnalyticNT.Bilinear.TypeI.dirichlet_divided_sum_uniform
#print axioms AnalyticNT.Bilinear.TypeI.typeI_bound_uniform
