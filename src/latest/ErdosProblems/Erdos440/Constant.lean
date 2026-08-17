import Mathlib

/-!
# The analytic constant in Erdős Problem 440

This file isolates the convergent series

`c = ∑ d ≥ 1, 1 / (√d (d + 1))`.

The indexing below is shifted by one, so that the `n`-th term has `d = n + 1`.
-/

open scoped BigOperators Topology
open Filter Finset

namespace Erdos440Constant

/-- The `d = n + 1` term of the sharp Erdős--Szemerédi constant. -/
noncomputable def sharpTerm (n : ℕ) : ℝ :=
  1 / (Real.sqrt (n + 1 : ℝ) * (n + 2 : ℝ))

/-- The same kernel with the mathematical (unshifted) positive index `d`.
Its value at `d = 0` is zero. -/
noncomputable def unshiftedSharpTerm (d : ℕ) : ℝ :=
  1 / (Real.sqrt d * (d + 1 : ℝ))

/-- The sharp universal coefficient, indexed over positive integers. -/
noncomputable def sharpConstant : ℝ :=
  ∑' n : ℕ, sharpTerm n

/-- The first `N` positive-index terms of the sharp series. -/
noncomputable def sharpPartialSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, sharpTerm n

/-- The first `N` terms in the difference-of-square-roots form used by
partial summation in the sharp estimate. -/
noncomputable def incrementPartialSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N,
    (Real.sqrt (n + 1 : ℝ) - Real.sqrt n) / (n + 1 : ℝ)

@[simp] theorem unshiftedSharpTerm_zero : unshiftedSharpTerm 0 = 0 := by
  simp [unshiftedSharpTerm]

@[simp] theorem unshiftedSharpTerm_succ (n : ℕ) :
    unshiftedSharpTerm (n + 1) = sharpTerm n := by
  unfold unshiftedSharpTerm sharpTerm
  norm_num only [Nat.cast_add, Nat.cast_one]
  ring

private lemma three_halves_rpow (n : ℕ) :
    |(n : ℝ) + 1| ^ (3 / 2 : ℝ) =
      Real.sqrt (n + 1 : ℝ) * (n + 1 : ℝ) := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [abs_of_pos hpos, show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
    Real.rpow_add hpos]
  simp only [Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem sharpTerm_nonneg (n : ℕ) : 0 ≤ sharpTerm n := by
  unfold sharpTerm
  positivity

theorem summable_sharpTerm : Summable sharpTerm := by
  have hp : Summable (fun n : ℕ ↦ 1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow 1 (3 / 2)).2 (by norm_num)
  apply Summable.of_nonneg_of_le (f := fun n : ℕ ↦
      1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ))
  · intro n
    unfold sharpTerm
    positivity
  · intro n
    unfold sharpTerm
    rw [three_halves_rpow]
    apply one_div_le_one_div_of_le
    · positivity
    · gcongr
      norm_num
  · exact hp

theorem summable_unshiftedSharpTerm : Summable unshiftedSharpTerm := by
  apply (summable_nat_add_iff 1).mp
  simpa only [unshiftedSharpTerm_succ] using summable_sharpTerm

/-- This makes explicit that the shifted definition of `sharpConstant` is
literally the series over `d ≥ 1` from the mathematical statement. -/
theorem sharpConstant_eq_unshifted_tsum :
    sharpConstant = ∑' d : ℕ, unshiftedSharpTerm d := by
  have htail := summable_unshiftedSharpTerm.sum_add_tsum_nat_add 1
  rw [sharpConstant]
  calc
    (∑' n : ℕ, sharpTerm n) =
        ∑' n : ℕ, unshiftedSharpTerm (n + 1) := by
      apply tsum_congr
      intro n
      rw [unshiftedSharpTerm_succ]
    _ = ∑' d : ℕ, unshiftedSharpTerm d := by
      simpa only [sum_range_one, unshiftedSharpTerm_zero, zero_add] using htail

theorem sharpPartialSum_le_constant (N : ℕ) :
    sharpPartialSum N ≤ sharpConstant := by
  unfold sharpPartialSum sharpConstant
  exact summable_sharpTerm.sum_le_tsum (Finset.range N)
    (fun n _ ↦ sharpTerm_nonneg n)

theorem sharpPartialSum_tendsto :
    Tendsto sharpPartialSum atTop (nhds sharpConstant) := by
  unfold sharpPartialSum sharpConstant
  exact summable_sharpTerm.hasSum.tendsto_sum_nat

theorem sqrt_remainder_tendsto :
    Tendsto (fun N : ℕ ↦ Real.sqrt N / (N + 1 : ℝ)) atTop (nhds 0) := by
  have hsqrt : Tendsto (fun N : ℕ ↦ Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun N : ℕ ↦ (Real.sqrt (N : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  apply squeeze_zero' (g := fun N : ℕ ↦ (Real.sqrt (N : ℝ))⁻¹)
  · filter_upwards with N
    positivity
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hspos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
    have hsquare : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) :=
      Real.sq_sqrt (by positivity)
    rw [inv_eq_one_div, le_div_iff₀ hspos, div_mul_eq_mul_div, ← pow_two, hsquare]
    exact (div_le_one (by positivity)).2 (by norm_num)
  · exact hinv

/-- Finite Abel-summation identity.  In unshifted notation this says

`sum_{d=1}^N (√d - √(d-1))/d = sum_{d=1}^N 1/(√d(d+1)) + √N/(N+1)`.
-/
theorem incrementPartialSum_eq (N : ℕ) :
    incrementPartialSum N =
      sharpPartialSum N + Real.sqrt N / (N + 1 : ℝ) := by
  induction N with
  | zero => norm_num [incrementPartialSum, sharpPartialSum]
  | succ N ih =>
      simp only [incrementPartialSum, sharpPartialSum] at ih ⊢
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      unfold sharpTerm
      have hspos : 0 < Real.sqrt (N + 1 : ℝ) := by positivity
      have hsquare : Real.sqrt (N + 1 : ℝ) ^ 2 = (N + 1 : ℝ) :=
        Real.sq_sqrt (by positivity)
      have hlocal :
          Real.sqrt N / (N + 1 : ℝ) +
              (Real.sqrt (N + 1 : ℝ) - Real.sqrt N) / (N + 1 : ℝ) =
            1 / (Real.sqrt (N + 1 : ℝ) * (N + 2 : ℝ)) +
              Real.sqrt (N + 1 : ℝ) / (N + 2 : ℝ) := by
        field_simp
        nlinarith
      calc
        _ = (∑ x ∈ Finset.range N,
                1 / (Real.sqrt (x + 1 : ℝ) * (x + 2 : ℝ))) +
              (Real.sqrt N / (N + 1 : ℝ) +
                (Real.sqrt (N + 1 : ℝ) - Real.sqrt N) / (N + 1 : ℝ)) := by
            ring
        _ = (∑ x ∈ Finset.range N,
                1 / (Real.sqrt (x + 1 : ℝ) * (x + 2 : ℝ))) +
              (1 / (Real.sqrt (N + 1 : ℝ) * (N + 2 : ℝ)) +
                Real.sqrt (N + 1 : ℝ) / (N + 2 : ℝ)) := by
            rw [hlocal]
        _ = _ := by
            norm_num [Nat.cast_add, Nat.cast_one]
            ring

theorem incrementPartialSum_tendsto :
    Tendsto incrementPartialSum atTop (nhds sharpConstant) := by
  have h := sharpPartialSum_tendsto.add sqrt_remainder_tendsto
  simpa only [add_zero] using h.congr'
    (Eventually.of_forall fun N ↦ (incrementPartialSum_eq N).symm)

/-- The logarithmic/harmonic loss occurring in the finite sharp bound. -/
noncomputable def harmonicError (x : ℕ) : ℝ :=
  (2 + Real.log x) / Real.sqrt x

theorem harmonicError_tendsto :
    Tendsto harmonicError atTop (nhds 0) := by
  have hcast : Tendsto (fun x : ℕ ↦ (x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun x : ℕ ↦ Real.sqrt x) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hcast
  have hconst : Tendsto (fun x : ℕ ↦ (2 : ℝ) / Real.sqrt x) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hsqrt
  have hlogReal :
      Tendsto (fun y : ℝ ↦ Real.log y / Real.sqrt y) atTop (nhds 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop
        (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero
  have hlog : Tendsto (fun x : ℕ ↦ Real.log x / Real.sqrt x) atTop (nhds 0) :=
    hlogReal.comp hcast
  unfold harmonicError
  convert hconst.add hlog using 1
  · funext x
    ring_nf
  · norm_num

/-- An abstract bridge from the standard finite sharp estimate to its
eventual `c + ε` consequence.  It can be applied directly to the counting
function once its finite estimate has been established. -/
theorem eventually_normalized_le_of_finite_bound
    (F : ℕ → ℝ)
    (hfinite : ∀ x : ℕ, 0 < x →
      F x / Real.sqrt x ≤ sharpConstant + harmonicError x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      F x / Real.sqrt x ≤ sharpConstant + ε := by
  have herr : ∀ᶠ x : ℕ in atTop, harmonicError x < ε :=
    (tendsto_order.1 harmonicError_tendsto).2 ε hε
  filter_upwards [herr, eventually_gt_atTop 0] with x hxerr hxpos
  exact (hfinite x hxpos).trans (by linarith)

end Erdos440Constant
