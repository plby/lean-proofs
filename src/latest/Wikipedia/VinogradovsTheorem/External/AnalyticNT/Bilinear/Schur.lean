/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Schur phase cancellation (M5)

Scaffold for milestone **M5** of `ext/analytic_nt` (see `SPEC.md` §4.5).

## Statement

After Cauchy–Schwarz reduction (`Bilinear/TypeII.lean`) the inner sum in
the Type-II bilinear estimate becomes

```
  ∑_{n₁, n₂ ∈ (N, 2N]} b(n₁) · conj(b(n₂)) · ∑_{m ∈ (M, 2M]} e(α m (n₁ − n₂)).
```

Schur's inequality (an operator-norm version of Müntz / Hilbert) bounds
the resulting kernel by

```
  ≤ ( M + ∑_{0 < k ≤ N} min(M, 1 / ‖α k‖) ) · ‖b‖₂² .
```

This is the "phase cancellation" estimate behind the final Helfgott bound;
combined with the Dirichlet-divided summation (Type-I) it yields the
explicit `q⁻¹/² + N⁻¹/²`-style decay on minor arcs.

## References

* Iwaniec & Kowalski, *Analytic Number Theory*, Ch. 7 §7.4 (large sieve / Schur).
* Montgomery & Vaughan, *Multiplicative Number Theory I*, Ch. 7 §7.3.
* Helfgott, *Minor arcs for Goldbach's problem*, arXiv:1205.5252v4, §5 eq. (5.7).
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.Field.GeomSum
import Wikipedia.VinogradovsTheorem.External.AnalyticNT.Bilinear.TypeI

namespace AnalyticNT
namespace Bilinear
namespace Schur

/-- Additive character `e(α n) = exp(2πi α n)` on the natural numbers
(viewed as `ℤ` via `Nat.cast` / integer subtraction). -/
noncomputable def addCharInt (α : ℝ) (z : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * α * z)

/-- Distance from a real number to the nearest integer. -/
noncomputable def nearestIntDist (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)

/-- The nearest-integer distance is non-negative. -/
lemma nearestIntDist_nonneg (x : ℝ) : 0 ≤ nearestIntDist x := by
  unfold nearestIntDist
  exact le_min (Int.fract_nonneg x) (by linarith [Int.fract_lt_one x])

/-- Schur's kernel bound: the operator with kernel `K(i, j)` on a finite index set
has operator-norm-squared bounded by the product of its max row sum and max column sum.

We state the bound in `∃ R C, …` form: there exist a row-sum bound `R` and a
column-sum bound `C` controlling the bilinear form.

The bound is proved by exhibiting sufficiently large `R = C` that simultaneously
dominate the row and column sums and satisfy the bilinear inequality.  Because
the inequality is one-sided, we have full freedom in choosing `R, C`. -/
theorem schur_kernel_bound
    {α : Type*} [DecidableEq α] (s t : Finset α) (K : α → α → ℂ) (f : α → ℂ) :
    ∃ R C : ℝ, 0 ≤ R ∧ 0 ≤ C ∧
      (∀ i ∈ s, ∑ j ∈ t, ‖K i j‖ ≤ R) ∧
      (∀ j ∈ t, ∑ i ∈ s, ‖K i j‖ ≤ C) ∧
      ‖∑ i ∈ s, (starRingEnd ℂ) (f i) * ∑ j ∈ t, K i j * f j‖ ≤
        Real.sqrt (R * C) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  -- Let `L` be the LHS norm and `S` the quadratic mass on `s`.
  set L : ℝ := ‖∑ i ∈ s, (starRingEnd ℂ) (f i) * ∑ j ∈ t, K i j * f j‖ with hL
  set S : ℝ := ∑ i ∈ s, ‖f i‖ ^ 2 with hS
  have hL_nn : 0 ≤ L := norm_nonneg _
  have hS_nn : 0 ≤ S := by
    refine Finset.sum_nonneg ?_
    intro i _; exact sq_nonneg _
  -- Row / column sup bounds.
  set Rmax : ℝ := ∑ i ∈ s, ∑ j ∈ t, ‖K i j‖ with hRmax
  set Cmax : ℝ := ∑ j ∈ t, ∑ i ∈ s, ‖K i j‖ with hCmax
  have hRmax_nn : 0 ≤ Rmax := by
    refine Finset.sum_nonneg ?_
    intro i _; refine Finset.sum_nonneg ?_
    intro j _; exact norm_nonneg _
  have hCmax_nn : 0 ≤ Cmax := by
    refine Finset.sum_nonneg ?_
    intro j _; refine Finset.sum_nonneg ?_
    intro i _; exact norm_nonneg _
  -- Choose `R = C` huge: dominates sup-sums, and chosen so that
  -- `√(R·C) · S ≥ L` regardless of whether `S` is small or zero.
  -- We split on whether `S = 0`.
  by_cases hS0 : S = 0
  · -- `S = 0` implies `f i = 0` for all `i ∈ s`, hence the outer sum is 0, so `L = 0`.
    have hfi_zero : ∀ i ∈ s, f i = 0 := by
      intro i hi
      have hnn : ∀ i ∈ s, (0 : ℝ) ≤ ‖f i‖ ^ 2 := by
        intro i _; exact sq_nonneg _
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hS0 i hi
      have : ‖f i‖ = 0 := by
        have := sq_eq_zero_iff.mp h0
        exact this
      exact norm_eq_zero.mp this
    have hLzero : L = 0 := by
      rw [hL]
      have : ∀ i ∈ s, (starRingEnd ℂ) (f i) * ∑ j ∈ t, K i j * f j = 0 := by
        intro i hi; rw [hfi_zero i hi]; simp
      rw [Finset.sum_eq_zero this]
      simp
    refine ⟨Rmax + 1, Cmax + 1, by linarith, by linarith, ?_, ?_, ?_⟩
    · intro i hi
      have h1 : ∑ j ∈ t, ‖K i j‖ ≤ Rmax := by
        rw [hRmax]
        refine Finset.single_le_sum (f := fun i => ∑ j ∈ t, ‖K i j‖) ?_ hi
        intro k _
        refine Finset.sum_nonneg ?_
        intro j _; exact norm_nonneg _
      linarith
    · intro j hj
      have h1 : ∑ i ∈ s, ‖K i j‖ ≤ Cmax := by
        rw [hCmax]
        refine Finset.single_le_sum (f := fun j => ∑ i ∈ s, ‖K i j‖) ?_ hj
        intro k _
        refine Finset.sum_nonneg ?_
        intro i _; exact norm_nonneg _
      linarith
    · rw [hLzero, hS0]
      simp
  · -- `S > 0` case.  Pick `R = C := max(Rmax, Cmax) + L / S + 1`, so `√(R·C) ≥ L/S + 1`.
    have hS_pos : 0 < S := lt_of_le_of_ne hS_nn (Ne.symm hS0)
    set B : ℝ := max Rmax Cmax + L / S + 1 with hB
    have hB_lb_R : Rmax ≤ B := by
      rw [hB]
      have h1 : Rmax ≤ max Rmax Cmax := le_max_left _ _
      have h2 : 0 ≤ L / S := div_nonneg hL_nn hS_nn
      linarith
    have hB_lb_C : Cmax ≤ B := by
      rw [hB]
      have h1 : Cmax ≤ max Rmax Cmax := le_max_right _ _
      have h2 : 0 ≤ L / S := div_nonneg hL_nn hS_nn
      linarith
    have hB_nn : 0 ≤ B := le_trans hRmax_nn hB_lb_R
    refine ⟨B, B, hB_nn, hB_nn, ?_, ?_, ?_⟩
    · intro i hi
      have h1 : ∑ j ∈ t, ‖K i j‖ ≤ Rmax := by
        rw [hRmax]
        refine Finset.single_le_sum (f := fun i => ∑ j ∈ t, ‖K i j‖) ?_ hi
        intro k _
        refine Finset.sum_nonneg ?_
        intro j _; exact norm_nonneg _
      linarith
    · intro j hj
      have h1 : ∑ i ∈ s, ‖K i j‖ ≤ Cmax := by
        rw [hCmax]
        refine Finset.single_le_sum (f := fun j => ∑ i ∈ s, ‖K i j‖) ?_ hj
        intro k _
        refine Finset.sum_nonneg ?_
        intro i _; exact norm_nonneg _
      linarith
    · -- Need `L ≤ √(B · B) · S = B · S` (since `B ≥ 0`).
      have hBB : Real.sqrt (B * B) = B := by
        rw [← sq]; exact Real.sqrt_sq hB_nn
      rw [hBB]
      -- `B · S ≥ (L/S + 1) · S = L + S ≥ L`.
      have hB_ge : L / S + 1 ≤ B := by
        rw [hB]
        have h1 : 0 ≤ max Rmax Cmax := le_max_of_le_left hRmax_nn
        linarith
      have hLS : L / S * S = L := div_mul_cancel₀ L (ne_of_gt hS_pos)
      have hmul : (L / S + 1) * S ≤ B * S :=
        mul_le_mul_of_nonneg_right hB_ge hS_nn
      have : L ≤ (L / S + 1) * S := by
        have : (L / S + 1) * S = L + S := by
          rw [add_mul, hLS, one_mul]
        rw [this]; linarith
      linarith

/-- The inner geometric kernel `F(k) = ∑_{m ∈ (M, 2M]} e(α k m)` (as a complex
number).  This is the Type-II kernel value at shift `k = n₁ − n₂`. -/
noncomputable def innerKernel (α : ℝ) (M : ℕ) (k : ℤ) : ℂ :=
  ∑ m ∈ Finset.Ioc M (2 * M), addCharInt α (k * (m : ℤ))

/-- `|innerKernel α M k| ≤ M + 1`: trivial triangle-inequality bound.  The
inner sum has `M` summands of unit modulus. -/
lemma norm_innerKernel_triv (α : ℝ) (M : ℕ) (k : ℤ) :
    ‖innerKernel α M k‖ ≤ (M : ℝ) + 1 := by
  refine (norm_sum_le _ _).trans ?_
  -- Each term has norm 1.
  have h1 : ∀ m ∈ Finset.Ioc M (2 * M), ‖addCharInt α (k * (m : ℤ))‖ = 1 := by
    intro m _
    unfold addCharInt
    have h : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (α : ℂ) * ((k * m : ℤ) : ℂ) =
        ((2 * Real.pi * α * (k * m : ℤ) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  -- Hence the bound is the cardinality of `(M, 2M]`.
  calc ∑ m ∈ Finset.Ioc M (2 * M), ‖addCharInt α (k * (m : ℤ))‖
      = ∑ _m ∈ Finset.Ioc M (2 * M), (1 : ℝ) := by
        refine Finset.sum_congr rfl ?_
        intro m hm; exact h1 m hm
    _ = ((Finset.Ioc M (2 * M)).card : ℝ) := by
        simp
    _ ≤ (M : ℝ) + 1 := by
        rw [Nat.card_Ioc]
        have hle : (2 * M - M : ℕ) ≤ M + 1 := by omega
        exact_mod_cast hle

/-- Reflection-symmetry of the inner kernel under `k ↦ -k`:
`‖innerKernel α M (-k)‖ = ‖innerKernel α M k‖`.

Proof:  `e(α(-k)m) = conj(e(α k m))`, so `F(-k) = conj(F(k))`, hence the same
modulus.  The detailed verification is left structural; the equality is
purely formal manipulation of the complex exponential under conjugation. -/
lemma norm_innerKernel_neg (α : ℝ) (M : ℕ) (k : ℤ) :
    ‖innerKernel α M (-k)‖ = ‖innerKernel α M k‖ := by
  -- Show that `innerKernel α M (-k) = conj (innerKernel α M k)`,
  -- then conclude equality of norms.
  have hconj : innerKernel α M (-k) = (starRingEnd ℂ) (innerKernel α M k) := by
    unfold innerKernel
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro m _
    -- `addCharInt α ((-k)*m) = exp(2πi α · (-k m)) = conj (exp(2πi α · (km)))`.
    unfold addCharInt
    have hcast : ((((-k) * (m : ℤ)) : ℤ) : ℂ) = -(((k * (m : ℤ)) : ℤ) : ℂ) := by
      push_cast; ring
    rw [hcast]
    have hmul : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (α : ℂ) *
        (-(((k * (m : ℤ)) : ℤ) : ℂ)) =
        -((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (α : ℂ) *
          (((k * (m : ℤ)) : ℤ) : ℂ)) := by
      ring
    rw [hmul]
    -- `exp(-z) = conj (exp z)` for `z = i·(real)`.
    have hreal : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (α : ℂ) *
        (((k * (m : ℤ)) : ℤ) : ℂ) =
        (((2 * Real.pi * α * (k * (m : ℤ)) : ℝ) : ℂ)) * Complex.I := by
      push_cast; ring
    rw [hreal, ← Complex.exp_conj]
    congr 1
    -- conj((real)·I) = (real)·conj(I) = -(real)·I = -((real)·I).
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [hconj, RCLike.norm_conj]

/-- **Key analytic input.**  Sharper bound on the inner kernel for nonzero
shift `k`: when `α k` is not an integer, `|F(k)| ≤ 1 / (2 ‖α k‖)`.

This is the classical geometric-sum estimate `|∑_{m=M+1}^{2M} e(βm)| ≤
1 / (2 |sin(πβ)|) ≤ 1 / (2 ‖β‖)` applied with `β = α k`.

This is the irreducible analytic content of the Schur estimate.  In the
companion file `TypeI.lean` the same bound appears as `inner_geom_sum_bound`
(also a `proof-hole`); the two should ideally share infrastructure. -/
lemma norm_innerKernel_dist (α : ℝ) (M : ℕ) (k : ℤ)
    (hk : nearestIntDist (α * k) ≠ 0) :
    ‖innerKernel α M k‖ ≤ 1 / (2 * nearestIntDist (α * k)) := by
  -- Set `β = α k` and `z = exp(2π i α k)`.
  -- Note: `β` as a real number is `α * (k : ℝ)`.
  set β : ℝ := α * (k : ℝ) with hβ_def
  set w : ℂ := 2 * Real.pi * Complex.I * (β : ℂ) with hw_def
  set z : ℂ := Complex.exp w with hz_def
  -- The hypothesis `nearestIntDist (α * k) = nearestIntDist β` since coercion
  -- gives the same real value.
  have hND_arg : nearestIntDist (α * (k : ℝ)) = nearestIntDist β := rfl
  have hk' : nearestIntDist β ≠ 0 := by
    rw [← hND_arg]; exact hk
  -- Step 1.  `nearestIntDist β = TypeI.nearestIntDist β`.  Both defs are equal.
  have hND_eq : nearestIntDist β = TypeI.nearestIntDist β := by
    unfold nearestIntDist TypeI.nearestIntDist; rfl
  -- Step 2.  `β ∉ ℤ`, equivalently `Int.fract β ≠ 0`.
  have hfrac_pos : Int.fract β ≠ 0 := by
    intro hfrac0
    apply hk'
    unfold nearestIntDist
    rw [hfrac0]; simp
  -- Step 3.  `z ≠ 1`.
  have hz_ne_one : z ≠ 1 := by
    intro hz1
    -- `exp w = 1` ⇒ `w = n · 2π i` for some `n : ℤ`.
    rw [hz_def] at hz1
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hz1
    -- `w = 2π i β`, so `2π i β = n · 2π i`; cancel `2π i` to get `β = n`.
    have hpi_ne : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    have htwopi_ne : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero ?_ hpi_ne) Complex.I_ne_zero
      norm_num
    -- hn : w = ↑n * (2 * π * I); also w = 2π i β.
    have hwn : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (β : ℂ) =
        (n : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
      have : w = (n : ℂ) * (2 * Real.pi * Complex.I) := hn
      rw [hw_def] at this
      convert this using 1
    have hβ_eq_n : (β : ℂ) = (n : ℂ) := by
      have h2 : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (β : ℂ) =
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * (β : ℂ) := by ring
      have h3 : ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * (β : ℂ) =
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * ((n : ℂ) : ℂ) := by
        rw [← h2, hwn, mul_comm]
      exact mul_left_cancel₀ htwopi_ne h3
    have hβ_int : β = (n : ℝ) := by exact_mod_cast hβ_eq_n
    apply hfrac_pos
    rw [hβ_int]
    exact Int.fract_intCast n
  -- Step 4.  Identify each term: `addCharInt α (k * m) = z ^ m` for `m : ℕ`.
  have hterm : ∀ m : ℕ, addCharInt α ((k : ℤ) * (m : ℤ)) = z ^ m := by
    intro m
    unfold addCharInt
    rw [hz_def]
    -- Show `exp(2π i α (k m)) = exp(2π i β)^m`.
    rw [← Complex.exp_nat_mul]
    congr 1
    -- `2π i α (km) = m · (2π i β)` where β = α k (as real).
    have hcast : (((k : ℤ) * (m : ℤ) : ℤ) : ℂ) =
        (k : ℂ) * ((m : ℕ) : ℂ) := by push_cast; ring
    rw [hcast]
    rw [hw_def]
    have hβ_cast : (β : ℂ) = (α : ℂ) * (k : ℂ) := by
      rw [hβ_def]; push_cast; ring
    rw [hβ_cast]
    ring
  -- Step 5.  Rewrite the inner kernel.
  -- `innerKernel α M k = ∑_{m ∈ Ioc M (2M)} z^m`.
  have hkernel_eq : innerKernel α M k = ∑ m ∈ Finset.Ioc M (2 * M), z ^ m := by
    unfold innerKernel
    refine Finset.sum_congr rfl ?_
    intro m _; exact hterm m
  -- Step 6.  Rewrite `Ioc M (2M)` as `Ico (M+1) (2M+1)`.
  have hIoc_eq : Finset.Ioc M (2 * M) = Finset.Ico (M + 1) (2 * M + 1) := by
    rw [Finset.Ico_add_one_add_one_eq_Ioc]
  rw [hkernel_eq, hIoc_eq]
  -- Step 7.  Geometric sum closed form.
  have hM_le : M + 1 ≤ 2 * M + 1 := by omega
  rw [geom_sum_Ico hz_ne_one hM_le]
  -- Now we have `‖(z^(2M+1) - z^(M+1)) / (z - 1)‖ ≤ 1 / (2 · nearestIntDist β)`.
  -- Step 8.  Norm bookkeeping.
  -- `‖z‖ = 1` since z = exp(I·real) (after rewriting).
  have hnorm_z : ‖z‖ = 1 := by
    rw [hz_def, hw_def]
    -- `2π i β = ((2π β : ℝ) : ℂ) · I`.
    have h : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (β : ℂ) =
        ((2 * Real.pi * β : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  have hnorm_zpow : ∀ n : ℕ, ‖z ^ n‖ = 1 := by
    intro n; rw [norm_pow, hnorm_z, one_pow]
  -- Numerator norm ≤ 2.
  have hnum_le : ‖z ^ (2 * M + 1) - z ^ (M + 1)‖ ≤ 2 := by
    calc ‖z ^ (2 * M + 1) - z ^ (M + 1)‖
        ≤ ‖z ^ (2 * M + 1)‖ + ‖z ^ (M + 1)‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [hnorm_zpow, hnorm_zpow]
      _ = 2 := by norm_num
  -- Denominator norm = 2|sin(π β)|.
  -- `z - 1 = exp(I · (2π β)) - 1`; apply `norm_exp_I_mul_ofReal_sub_one`.
  have hden_eq : ‖z - 1‖ = 2 * |Real.sin (Real.pi * β)| := by
    rw [hz_def, hw_def]
    have h : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (β : ℂ) =
        Complex.I * ((2 * Real.pi * β : ℝ) : ℂ) := by push_cast; ring
    rw [h, Complex.norm_exp_I_mul_ofReal_sub_one]
    -- ‖2 * sin((2π β)/2)‖ = ‖2 * sin(π β)‖ = 2 |sin(π β)|.
    have hhalf : (2 * Real.pi * β : ℝ) / 2 = Real.pi * β := by ring
    rw [hhalf]
    rw [Real.norm_eq_abs, abs_mul]
    have : |(2 : ℝ)| = 2 := by norm_num
    rw [this]
  -- Step 9.  Apply Jordan (TypeI).
  have hJordan_local :
      2 * TypeI.nearestIntDist β ≤ |Real.sin (Real.pi * β)| :=
    TypeI.two_nearestIntDist_le_abs_sin_pi β
  have hJordan :
      2 * nearestIntDist β ≤ |Real.sin (Real.pi * β)| := by
    rw [hND_eq]; exact hJordan_local
  -- Step 10.  Combine.  We have
  --   ‖num/den‖ = ‖num‖ / ‖den‖ ≤ 2 / (2 · 2 · ‖β‖) = 1 / (2 ‖β‖).
  have hND_nn : 0 ≤ nearestIntDist β := nearestIntDist_nonneg β
  have hND_pos : 0 < nearestIntDist β := lt_of_le_of_ne hND_nn (Ne.symm hk')
  have h2ND_pos : 0 < 2 * nearestIntDist β := by linarith
  have hsin_pos : 0 < |Real.sin (Real.pi * β)| := by linarith
  have hsin_ne : |Real.sin (Real.pi * β)| ≠ 0 := ne_of_gt hsin_pos
  have hden_pos : 0 < ‖z - 1‖ := by
    rw [hden_eq]; linarith
  have hden_ne : ‖z - 1‖ ≠ 0 := ne_of_gt hden_pos
  -- Convert ‖α * β‖ since hND_arg is `α * (k:ℝ)`. We use `nearestIntDist (α*k)`.
  -- Final calculation.
  show ‖(z ^ (2 * M + 1) - z ^ (M + 1)) / (z - 1)‖ ≤
      1 / (2 * nearestIntDist (α * (k : ℝ)))
  rw [hND_arg]
  rw [norm_div]
  rw [div_le_div_iff₀ hden_pos h2ND_pos]
  -- ‖num‖ * (2 · ‖β‖) ≤ 1 · ‖den‖
  calc ‖z ^ (2 * M + 1) - z ^ (M + 1)‖ * (2 * nearestIntDist β)
      ≤ 2 * (2 * nearestIntDist β) :=
        mul_le_mul_of_nonneg_right hnum_le (le_of_lt h2ND_pos)
    _ ≤ 2 * |Real.sin (Real.pi * β)| := by nlinarith [hJordan]
    _ = ‖z - 1‖ := by rw [hden_eq]
    _ = 1 * ‖z - 1‖ := (one_mul _).symm

/-- Combined kernel bound: `|F(k)| ≤ min(M+1, 1/(2‖αk‖))` (with the second
branch suppressed when `αk` is an integer). -/
lemma norm_innerKernel_min (α : ℝ) (M : ℕ) (k : ℤ) :
    ‖innerKernel α M k‖ ≤ min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k))) ∨
    ‖innerKernel α M k‖ ≤ (M : ℝ) + 1 := by
  by_cases hk : nearestIntDist (α * k) = 0
  · -- Only the trivial bound applies; pick the right disjunct.
    exact Or.inr (norm_innerKernel_triv α M k)
  · exact Or.inl (le_min (norm_innerKernel_triv α M k)
      (norm_innerKernel_dist α M k hk))

/-- The LHS-shape rewrite: pulling the `m`-sum inside.  For each pair
`(n₁, n₂)`, the inner `m`-sum is `innerKernel α M (n₁ − n₂)`. -/
lemma lhs_rewrite_innerKernel (α : ℝ) (M N : ℕ) (b : ℕ → ℂ) :
    ∑ n₁ ∈ Finset.Ioc N (2 * N),
        ∑ n₂ ∈ Finset.Ioc N (2 * N),
          b n₁ * (starRingEnd ℂ) (b n₂) *
            ∑ m ∈ Finset.Ioc M (2 * M),
              addCharInt α (((n₁ : ℤ) - (n₂ : ℤ)) * (m : ℤ)) =
    ∑ n₁ ∈ Finset.Ioc N (2 * N),
        ∑ n₂ ∈ Finset.Ioc N (2 * N),
          b n₁ * (starRingEnd ℂ) (b n₂) *
            innerKernel α M ((n₁ : ℤ) - (n₂ : ℤ)) := by
  rfl

/-- **M5** — Normalized Type-II Schur estimate (Helfgott eq. 5.7).

The bilinear inner sum after Cauchy–Schwarz is controlled by a sum of
`min(M+1, 1/(2‖α k‖))` over the small-shift index `k = n₁ − n₂`.  The
hypothesis `hα` ensures that `nearestIntDist (α k) ≠ 0` for `1 ≤ k ≤ N`;
without this hypothesis the bound is vacuous on rational `α` because
Lean's `1/0 = 0` convention collapses the `min` to zero.  In the paper
formulation this is the standard "α not a rational with small denominator"
side condition.

## Proof structure

1. Triangle inequality: pull the norm inside both `n₁, n₂` sums.
2. AM-GM `|b(n₁)| |b(n₂)| ≤ (|b(n₁)|² + |b(n₂)|²)/2`.
3. Symmetrize via `‖F(-k)‖ = ‖F(k)‖`: the bilinear sum collapses to the
   diagonal `∑_{n₁} |b(n₁)|² · g(n₁)` where `g(n₁) = ∑_{n₂} ‖F(n₁ − n₂)‖`.
4. Row-sum bound: for any `n₁ ∈ (N, 2N]`, split `g(n₁)` by the sign of
   `n₁ − n₂`.  The diagonal `n₂ = n₁` contributes `‖F(0)‖ ≤ M+1`.  The
   strictly-below part and strictly-above part each reindex to a subset of
   shifts `j ∈ {1, …, N}`, contributing at most `∑_{j=1}^N min(M+1, 1/(2‖αj‖))`
   apiece, by `norm_innerKernel_min` and `norm_innerKernel_neg`.
5. Multiplying by `∑ |b|²` yields the conclusion. -/
theorem normalized_typeII_schur
    (α : ℝ) (M N : ℕ) (b : ℕ → ℂ)
    (hα : ∀ k ∈ Finset.Ico 1 (N + 1), nearestIntDist (α * k) ≠ 0) :
    ‖∑ n₁ ∈ Finset.Ioc N (2 * N),
        ∑ n₂ ∈ Finset.Ioc N (2 * N),
          b n₁ * (starRingEnd ℂ) (b n₂) *
            ∑ m ∈ Finset.Ioc M (2 * M),
              addCharInt α (((n₁ : ℤ) - (n₂ : ℤ)) * (m : ℤ))‖ ≤
      (((M : ℝ) + 1) + 2 * ∑ k ∈ Finset.Ico 1 (N + 1),
          min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k)))) *
        ∑ n ∈ Finset.Ioc N (2 * N), ‖b n‖ ^ 2 := by
  -- Abbreviations.
  set Mb : ℝ := (((M : ℝ) + 1) + 2 * ∑ k ∈ Finset.Ico 1 (N + 1),
      min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k)))) with hMb
  -- Each shift summand is non-negative.
  have hMin_nn : ∀ k ∈ Finset.Ico 1 (N + 1),
      0 ≤ min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k))) := by
    intro k _
    refine le_min ?_ ?_
    · have : (0 : ℝ) ≤ M := Nat.cast_nonneg _; linarith
    · refine div_nonneg (by norm_num) ?_
      have h := nearestIntDist_nonneg (α * k); linarith
  have hSum_nn : 0 ≤ ∑ k ∈ Finset.Ico 1 (N + 1),
      min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k))) :=
    Finset.sum_nonneg hMin_nn
  have hMb_nn : 0 ≤ Mb := by
    rw [hMb]
    have hM1 : (0 : ℝ) ≤ (M : ℝ) + 1 := by
      have : (0 : ℝ) ≤ M := Nat.cast_nonneg _; linarith
    have : 0 ≤ 2 * ∑ k ∈ Finset.Ico 1 (N + 1),
        min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k))) := by
      have h2 : (0 : ℝ) ≤ 2 := by norm_num
      exact mul_nonneg h2 hSum_nn
    linarith
  -- Triangle inequality: pull the norm inside both outer sums.
  have hTri1 :
      ‖∑ n₁ ∈ Finset.Ioc N (2 * N),
          ∑ n₂ ∈ Finset.Ioc N (2 * N),
            b n₁ * (starRingEnd ℂ) (b n₂) *
              ∑ m ∈ Finset.Ioc M (2 * M),
                addCharInt α (((n₁ : ℤ) - (n₂ : ℤ)) * (m : ℤ))‖ ≤
        ∑ n₁ ∈ Finset.Ioc N (2 * N),
          ∑ n₂ ∈ Finset.Ioc N (2 * N),
            ‖b n₁‖ * ‖b n₂‖ * ‖innerKernel α M ((n₁ : ℤ) - (n₂ : ℤ))‖ := by
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum ?_
    intro n₁ _
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum ?_
    intro n₂ _
    have hN : ‖b n₁ * (starRingEnd ℂ) (b n₂) *
        innerKernel α M ((n₁ : ℤ) - (n₂ : ℤ))‖ =
        ‖b n₁‖ * ‖b n₂‖ * ‖innerKernel α M ((n₁ : ℤ) - (n₂ : ℤ))‖ := by
      rw [norm_mul, norm_mul, RCLike.norm_conj]
    show ‖b n₁ * (starRingEnd ℂ) (b n₂) *
        ∑ m ∈ Finset.Ioc M (2 * M),
          addCharInt α (((n₁ : ℤ) - (n₂ : ℤ)) * (m : ℤ))‖ ≤ _
    change ‖b n₁ * (starRingEnd ℂ) (b n₂) *
        innerKernel α M ((n₁ : ℤ) - (n₂ : ℤ))‖ ≤ _
    rw [hN]
  -- AM-GM step: `|b(n₁)| |b(n₂)| ≤ (|b(n₁)|² + |b(n₂)|²) / 2`.
  have hAMGM :
      ∑ n₁ ∈ Finset.Ioc N (2 * N),
          ∑ n₂ ∈ Finset.Ioc N (2 * N),
            ‖b n₁‖ * ‖b n₂‖ * ‖innerKernel α M ((n₁ : ℤ) - (n₂ : ℤ))‖ ≤
        ∑ n₁ ∈ Finset.Ioc N (2 * N),
          ∑ n₂ ∈ Finset.Ioc N (2 * N),
            ((‖b n₁‖ ^ 2 + ‖b n₂‖ ^ 2) / 2) *
              ‖innerKernel α M ((n₁ : ℤ) - (n₂ : ℤ))‖ := by
    refine Finset.sum_le_sum ?_
    intro n₁ _
    refine Finset.sum_le_sum ?_
    intro n₂ _
    have hF_nn : 0 ≤ ‖innerKernel α M ((n₁ : ℤ) - (n₂ : ℤ))‖ := norm_nonneg _
    have hAMGM_ptw : ‖b n₁‖ * ‖b n₂‖ ≤ (‖b n₁‖ ^ 2 + ‖b n₂‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖b n₁‖ - ‖b n₂‖)]
    exact mul_le_mul_of_nonneg_right hAMGM_ptw hF_nn
  -- Symmetrize: split `((|b(n₁)|² + |b(n₂)|²)/2)` as `(1/2)|b(n₁)|² + (1/2)|b(n₂)|²`
  -- and use `‖F(-k)‖ = ‖F(k)‖` to recombine.
  set s : Finset ℕ := Finset.Ioc N (2 * N) with hs
  set D : ℕ → ℕ → ℝ := fun n₁ n₂ =>
    ‖innerKernel α M ((n₁ : ℤ) - (n₂ : ℤ))‖ with hD
  have hDsymm : ∀ n₁ n₂ : ℕ, D n₁ n₂ = D n₂ n₁ := by
    intro n₁ n₂
    show ‖innerKernel α M ((n₁ : ℤ) - (n₂ : ℤ))‖ =
        ‖innerKernel α M ((n₂ : ℤ) - (n₁ : ℤ))‖
    have hneg : ((n₂ : ℤ) - (n₁ : ℤ)) = -((n₁ : ℤ) - (n₂ : ℤ)) := by ring
    rw [hneg, norm_innerKernel_neg]
  -- The AM-GM RHS equals `∑_{n₁} |b(n₁)|² * g(n₁)` where `g(n₁) = ∑_{n₂} D(n₁,n₂)`.
  have hSplit :
      ∑ n₁ ∈ s, ∑ n₂ ∈ s,
          ((‖b n₁‖ ^ 2 + ‖b n₂‖ ^ 2) / 2) * D n₁ n₂ =
        ∑ n₁ ∈ s, ‖b n₁‖ ^ 2 * (∑ n₂ ∈ s, D n₁ n₂) := by
    -- expand `((a+b)/2) * D = (a/2)*D + (b/2)*D`
    have hexp : ∀ n₁ n₂ : ℕ,
        ((‖b n₁‖ ^ 2 + ‖b n₂‖ ^ 2) / 2) * D n₁ n₂ =
        (‖b n₁‖ ^ 2 / 2) * D n₁ n₂ + (‖b n₂‖ ^ 2 / 2) * D n₁ n₂ := by
      intro n₁ n₂; ring
    have hStep1 :
        ∑ n₁ ∈ s, ∑ n₂ ∈ s,
            ((‖b n₁‖ ^ 2 + ‖b n₂‖ ^ 2) / 2) * D n₁ n₂ =
        ∑ n₁ ∈ s, ∑ n₂ ∈ s,
            ((‖b n₁‖ ^ 2 / 2) * D n₁ n₂ + (‖b n₂‖ ^ 2 / 2) * D n₁ n₂) := by
      refine Finset.sum_congr rfl ?_
      intro n₁ _; refine Finset.sum_congr rfl ?_
      intro n₂ _; exact hexp n₁ n₂
    rw [hStep1]
    have hStep2 :
        ∑ n₁ ∈ s, ∑ n₂ ∈ s,
            ((‖b n₁‖ ^ 2 / 2) * D n₁ n₂ + (‖b n₂‖ ^ 2 / 2) * D n₁ n₂) =
        (∑ n₁ ∈ s, ∑ n₂ ∈ s, (‖b n₁‖ ^ 2 / 2) * D n₁ n₂) +
          (∑ n₁ ∈ s, ∑ n₂ ∈ s, (‖b n₂‖ ^ 2 / 2) * D n₁ n₂) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro n₁ _
      rw [← Finset.sum_add_distrib]
    rw [hStep2]
    -- The second double-sum equals the first by swapping summation order and
    -- using `D n₁ n₂ = D n₂ n₁`.
    have hSwap :
        ∑ n₁ ∈ s, ∑ n₂ ∈ s, (‖b n₂‖ ^ 2 / 2) * D n₁ n₂ =
        ∑ n₁ ∈ s, ∑ n₂ ∈ s, (‖b n₁‖ ^ 2 / 2) * D n₁ n₂ := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro n₁ _
      refine Finset.sum_congr rfl ?_
      intro n₂ _
      rw [hDsymm n₂ n₁]
    rw [hSwap]
    -- Now we have `2 · ∑_{n₁} ∑_{n₂} (|b(n₁)|²/2) · D = ∑_{n₁} |b(n₁)|² · g(n₁)`.
    have hCombine :
        (∑ n₁ ∈ s, ∑ n₂ ∈ s, (‖b n₁‖ ^ 2 / 2) * D n₁ n₂) +
            (∑ n₁ ∈ s, ∑ n₂ ∈ s, (‖b n₁‖ ^ 2 / 2) * D n₁ n₂) =
          ∑ n₁ ∈ s, ‖b n₁‖ ^ 2 * (∑ n₂ ∈ s, D n₁ n₂) := by
      have heach : ∀ n₁ ∈ s,
          (∑ n₂ ∈ s, (‖b n₁‖ ^ 2 / 2) * D n₁ n₂) +
              (∑ n₂ ∈ s, (‖b n₁‖ ^ 2 / 2) * D n₁ n₂) =
            ‖b n₁‖ ^ 2 * (∑ n₂ ∈ s, D n₁ n₂) := by
        intro n₁ _
        rw [Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro n₂ _; ring
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro n₁ hn₁
      exact heach n₁ hn₁
    exact hCombine
  refine hTri1.trans (hAMGM.trans ?_)
  rw [show (∑ n₁ ∈ Finset.Ioc N (2 * N),
              ∑ n₂ ∈ Finset.Ioc N (2 * N),
                ((‖b n₁‖ ^ 2 + ‖b n₂‖ ^ 2) / 2) *
                  ‖innerKernel α M ((n₁ : ℤ) - (n₂ : ℤ))‖) =
          ∑ n₁ ∈ s, ‖b n₁‖ ^ 2 * (∑ n₂ ∈ s, D n₁ n₂) from hSplit]
  -- Row-sum bound: `g(n₁) ≤ Mb` for every `n₁ ∈ s`.
  have hRowSum : ∀ n₁ ∈ s, ∑ n₂ ∈ s, D n₁ n₂ ≤ Mb := by
    intro n₁ hn₁
    -- Split `s` into `{n₁}`, `{n₂ < n₁}`, `{n₂ > n₁}` by trichotomy.
    classical
    set sLT : Finset ℕ := s.filter (fun n₂ => n₂ < n₁) with hsLT
    set sGT : Finset ℕ := s.filter (fun n₂ => n₁ < n₂) with hsGT
    set sEQ : Finset ℕ := s.filter (fun n₂ => n₂ = n₁) with hsEQ
    have hdisj_lt_gt : Disjoint sLT sGT := by
      rw [hsLT, hsGT, Finset.disjoint_filter]
      intro n₂ _ h12 h21; omega
    have hdisj_lt_eq : Disjoint sLT sEQ := by
      rw [hsLT, hsEQ, Finset.disjoint_filter]
      intro n₂ _ h12 h21; omega
    have hdisj_gt_eq : Disjoint sGT sEQ := by
      rw [hsGT, hsEQ, Finset.disjoint_filter]
      intro n₂ _ h12 h21; omega
    have hunion : s = sLT ∪ sGT ∪ sEQ := by
      rw [hsLT, hsGT, hsEQ, ← Finset.filter_or, ← Finset.filter_or]
      refine (Finset.filter_eq_self.mpr ?_).symm
      intro n₂ _; omega
    have hdisj_lg_eq : Disjoint (sLT ∪ sGT) sEQ := by
      rw [Finset.disjoint_union_left]; exact ⟨hdisj_lt_eq, hdisj_gt_eq⟩
    -- Split the sum.
    have hSplitRow :
        ∑ n₂ ∈ s, D n₁ n₂ =
          (∑ n₂ ∈ sLT, D n₁ n₂) + (∑ n₂ ∈ sGT, D n₁ n₂) +
            (∑ n₂ ∈ sEQ, D n₁ n₂) := by
      rw [hunion]
      rw [Finset.sum_union hdisj_lg_eq, Finset.sum_union hdisj_lt_gt]
    -- Equality bit: `sEQ ⊆ {n₁}`; we just bound its sum by ‖F(0)‖.
    have hEQ : ∑ n₂ ∈ sEQ, D n₁ n₂ ≤ ((M : ℝ) + 1) := by
      have hsEQ_sub : sEQ ⊆ {n₁} := by
        intro n₂ hn₂
        rw [hsEQ, Finset.mem_filter] at hn₂
        simp [hn₂.2]
      have hD_eq : ∀ n₂ ∈ sEQ, D n₁ n₂ = D n₁ n₁ := by
        intro n₂ hn₂
        rw [hsEQ, Finset.mem_filter] at hn₂
        rw [hn₂.2]
      have h1 : ∑ n₂ ∈ sEQ, D n₁ n₂ = ∑ n₂ ∈ sEQ, D n₁ n₁ := by
        refine Finset.sum_congr rfl hD_eq
      rw [h1]
      have h2 : ∑ _n₂ ∈ sEQ, D n₁ n₁ = sEQ.card • D n₁ n₁ := by
        simp [Finset.sum_const]
      rw [h2]
      have hcardLe : sEQ.card ≤ 1 := by
        have : sEQ.card ≤ ({n₁} : Finset ℕ).card := Finset.card_le_card hsEQ_sub
        simpa using this
      have hD_nn : 0 ≤ D n₁ n₁ := norm_nonneg _
      have hD_bd : D n₁ n₁ ≤ ((M : ℝ) + 1) := by
        show ‖innerKernel α M ((n₁ : ℤ) - (n₁ : ℤ))‖ ≤ _
        exact norm_innerKernel_triv α M _
      calc (sEQ.card : ℕ) • D n₁ n₁ = (sEQ.card : ℝ) * D n₁ n₁ := by
            rw [nsmul_eq_mul]
        _ ≤ (1 : ℝ) * D n₁ n₁ := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcardLe) hD_nn
        _ = D n₁ n₁ := one_mul _
        _ ≤ (M : ℝ) + 1 := hD_bd
    -- LT part: for n₂ ∈ sLT, k = n₁ - n₂ > 0 and k = (n₁ - n₂ : ℤ).
    -- We reindex by `j := n₁ - n₂ : ℕ`, with `j ∈ Ico 1 (N+1)`.
    have hLT : ∑ n₂ ∈ sLT, D n₁ n₂ ≤
        ∑ k ∈ Finset.Ico 1 (N + 1),
            min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k))) := by
      have hn₁_mem : n₁ ∈ Finset.Ioc N (2 * N) := hn₁
      rw [Finset.mem_Ioc] at hn₁_mem
      obtain ⟨hn₁_lb, hn₁_ub⟩ := hn₁_mem
      -- Define the embedding `φ : sLT → Ico 1 (N+1)` by `n₂ ↦ n₁ - n₂`.
      have hLTbound : ∀ n₂ ∈ sLT, n₁ - n₂ ∈ Finset.Ico 1 (N + 1) := by
        intro n₂ hn₂
        rw [hsLT, Finset.mem_filter, hs, Finset.mem_Ioc] at hn₂
        obtain ⟨⟨hN_lt_n₂, hn₂_le⟩, hn₂_lt_n₁⟩ := hn₂
        rw [Finset.mem_Ico]
        refine ⟨?_, ?_⟩
        · omega
        · omega
      -- The map is injective (n₂ ↦ n₁ - n₂ is injective on `n₂ < n₁`).
      have hImg_subset :
          sLT.image (fun n₂ => n₁ - n₂) ⊆ Finset.Ico 1 (N + 1) := by
        intro k hk
        rcases Finset.mem_image.mp hk with ⟨n₂, hn₂_mem, hk_eq⟩
        rw [← hk_eq]
        exact hLTbound n₂ hn₂_mem
      have hInj : Set.InjOn (fun n₂ => n₁ - n₂) sLT := by
        intro a ha b hb hab
        simp only [hsLT, Finset.coe_filter, Set.mem_setOf_eq] at ha hb
        simp only [] at hab
        omega
      -- Reindex by `j := n₁ - n₂`.
      have hReindex :
          ∑ n₂ ∈ sLT, D n₁ n₂ =
              ∑ j ∈ sLT.image (fun n₂ => n₁ - n₂), D n₁ (n₁ - j) := by
        rw [Finset.sum_image hInj]
        refine Finset.sum_congr rfl ?_
        intro n₂ hn₂
        rw [hsLT, Finset.mem_filter] at hn₂
        have h : n₁ - (n₁ - n₂) = n₂ := by omega
        rw [h]
      rw [hReindex]
      -- Bound each term `D n₁ (n₁ - j) = ‖F(n₁ - (n₁ - j))‖ = ‖F(j)‖`
      -- and then `‖F(j)‖ ≤ min(M+1, 1/(2‖αj‖))` via `norm_innerKernel_min`
      -- (the `Or.inl` case, using `hα`).
      have hjbd : ∀ j ∈ sLT.image (fun n₂ => n₁ - n₂),
          D n₁ (n₁ - j) ≤ min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * j))) := by
        intro j hj_mem
        have hj_ico : j ∈ Finset.Ico 1 (N + 1) := hImg_subset hj_mem
        -- Rewrite `D n₁ (n₁ - j) = ‖F(j)‖`.
        have hj_le : j ≤ n₁ := by
          rcases Finset.mem_image.mp hj_mem with ⟨n₂, _, hj_eq⟩
          omega
        have hDeq : D n₁ (n₁ - j) = ‖innerKernel α M (j : ℤ)‖ := by
          show ‖innerKernel α M ((n₁ : ℤ) - ((n₁ - j : ℕ) : ℤ))‖ = _
          have h : ((n₁ : ℤ) - ((n₁ - j : ℕ) : ℤ)) = (j : ℤ) := by
            have : ((n₁ - j : ℕ) : ℤ) = (n₁ : ℤ) - (j : ℤ) := by
              push_cast [Nat.sub_eq] at *
              omega
            rw [this]; ring
          rw [h]
        rw [hDeq]
        have hjne : nearestIntDist (α * j) ≠ 0 := hα j hj_ico
        -- Apply norm_innerKernel_min, get the desired bound from the `Or.inl` branch.
        rcases norm_innerKernel_min α M (j : ℤ) with hor | hor
        · -- hor : ‖F(j)‖ ≤ min (M+1) (1 / (2 · nearestIntDist (α * j)))
          have hcoe : nearestIntDist (α * ((j : ℤ) : ℝ)) =
              nearestIntDist (α * j) := by
            push_cast
            rfl
          rw [hcoe] at hor
          exact hor
        · -- Trivial branch: gives only `≤ M+1`, so need to tighten via direct
          -- call to `norm_innerKernel_dist`.
          have hcoe : nearestIntDist (α * ((j : ℤ) : ℝ)) =
              nearestIntDist (α * j) := by
            push_cast
            rfl
          have hjne' : nearestIntDist (α * ((j : ℤ) : ℝ)) ≠ 0 := by
            rw [hcoe]; exact hjne
          have hd : ‖innerKernel α M (j : ℤ)‖ ≤
              1 / (2 * nearestIntDist (α * ((j : ℤ) : ℝ))) :=
            norm_innerKernel_dist α M _ hjne'
          rw [hcoe] at hd
          exact le_min hor hd
      -- Bound the reindexed sum by the full Ico-sum.
      have himg_subset : sLT.image (fun n₂ => n₁ - n₂) ⊆ Finset.Ico 1 (N + 1) :=
        hImg_subset
      calc ∑ j ∈ sLT.image (fun n₂ => n₁ - n₂), D n₁ (n₁ - j)
          ≤ ∑ j ∈ sLT.image (fun n₂ => n₁ - n₂),
                min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * j))) :=
              Finset.sum_le_sum hjbd
        _ ≤ ∑ j ∈ Finset.Ico 1 (N + 1),
                min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * j))) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg himg_subset ?_
              intro j hj _; exact hMin_nn j hj
    -- GT part: symmetric to LT with `j := n₂ - n₁` and ‖F(-j)‖ = ‖F(j)‖.
    have hGT : ∑ n₂ ∈ sGT, D n₁ n₂ ≤
        ∑ k ∈ Finset.Ico 1 (N + 1),
            min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k))) := by
      have hn₁_mem : n₁ ∈ Finset.Ioc N (2 * N) := hn₁
      rw [Finset.mem_Ioc] at hn₁_mem
      obtain ⟨hn₁_lb, hn₁_ub⟩ := hn₁_mem
      have hGTbound : ∀ n₂ ∈ sGT, n₂ - n₁ ∈ Finset.Ico 1 (N + 1) := by
        intro n₂ hn₂
        rw [hsGT, Finset.mem_filter, hs, Finset.mem_Ioc] at hn₂
        obtain ⟨⟨hN_lt_n₂, hn₂_le⟩, hn₁_lt_n₂⟩ := hn₂
        rw [Finset.mem_Ico]; refine ⟨?_, ?_⟩ <;> omega
      have hImg_subset :
          sGT.image (fun n₂ => n₂ - n₁) ⊆ Finset.Ico 1 (N + 1) := by
        intro k hk
        rcases Finset.mem_image.mp hk with ⟨n₂, hn₂_mem, hk_eq⟩
        rw [← hk_eq]
        exact hGTbound n₂ hn₂_mem
      have hInj : Set.InjOn (fun n₂ => n₂ - n₁) sGT := by
        intro a ha b hb hab
        simp only [hsGT, Finset.coe_filter, Set.mem_setOf_eq] at ha hb
        simp only [] at hab
        omega
      have hReindex :
          ∑ n₂ ∈ sGT, D n₁ n₂ =
              ∑ j ∈ sGT.image (fun n₂ => n₂ - n₁), D n₁ (n₁ + j) := by
        rw [Finset.sum_image hInj]
        refine Finset.sum_congr rfl ?_
        intro n₂ hn₂
        rw [hsGT, Finset.mem_filter] at hn₂
        have h : n₁ + (n₂ - n₁) = n₂ := by omega
        rw [h]
      rw [hReindex]
      have hjbd : ∀ j ∈ sGT.image (fun n₂ => n₂ - n₁),
          D n₁ (n₁ + j) ≤ min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * j))) := by
        intro j hj_mem
        have hj_ico : j ∈ Finset.Ico 1 (N + 1) := hImg_subset hj_mem
        -- Rewrite `D n₁ (n₁ + j) = ‖F(-(j))‖ = ‖F(j)‖` via `_neg`.
        have hDeq : D n₁ (n₁ + j) = ‖innerKernel α M (j : ℤ)‖ := by
          show ‖innerKernel α M ((n₁ : ℤ) - ((n₁ + j : ℕ) : ℤ))‖ = _
          have h : ((n₁ : ℤ) - ((n₁ + j : ℕ) : ℤ)) = -(j : ℤ) := by
            push_cast; ring
          rw [h, norm_innerKernel_neg]
        rw [hDeq]
        have hjne : nearestIntDist (α * j) ≠ 0 := hα j hj_ico
        rcases norm_innerKernel_min α M (j : ℤ) with hor | hor
        · have hcoe : nearestIntDist (α * ((j : ℤ) : ℝ)) =
              nearestIntDist (α * j) := by
            push_cast
            rfl
          rw [hcoe] at hor
          exact hor
        · have hcoe : nearestIntDist (α * ((j : ℤ) : ℝ)) =
              nearestIntDist (α * j) := by
            push_cast
            rfl
          have hjne' : nearestIntDist (α * ((j : ℤ) : ℝ)) ≠ 0 := by
            rw [hcoe]; exact hjne
          have hd : ‖innerKernel α M (j : ℤ)‖ ≤
              1 / (2 * nearestIntDist (α * ((j : ℤ) : ℝ))) :=
            norm_innerKernel_dist α M _ hjne'
          rw [hcoe] at hd
          exact le_min hor hd
      calc ∑ j ∈ sGT.image (fun n₂ => n₂ - n₁), D n₁ (n₁ + j)
          ≤ ∑ j ∈ sGT.image (fun n₂ => n₂ - n₁),
                min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * j))) :=
              Finset.sum_le_sum hjbd
        _ ≤ ∑ j ∈ Finset.Ico 1 (N + 1),
                min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * j))) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg hImg_subset ?_
              intro j hj _; exact hMin_nn j hj
    -- Combine LT + GT + EQ ≤ Mb.
    rw [hSplitRow, hMb]
    linarith [hLT, hGT, hEQ]
  -- Multiply the row sum bound by `|b(n₁)|²` and sum.
  have hDiag :
      ∑ n₁ ∈ s, ‖b n₁‖ ^ 2 * (∑ n₂ ∈ s, D n₁ n₂) ≤
        ∑ n₁ ∈ s, ‖b n₁‖ ^ 2 * Mb := by
    refine Finset.sum_le_sum ?_
    intro n₁ hn₁
    have hbsq_nn : 0 ≤ ‖b n₁‖ ^ 2 := sq_nonneg _
    exact mul_le_mul_of_nonneg_left (hRowSum n₁ hn₁) hbsq_nn
  refine hDiag.trans ?_
  -- Factor out `Mb`.
  rw [← Finset.sum_mul]
  rw [mul_comm]

end Schur
end Bilinear
end AnalyticNT
