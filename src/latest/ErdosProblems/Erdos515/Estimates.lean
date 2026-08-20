/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Real sequence estimates for Erdős Problem 515

This file isolates the elementary sequence estimates used in the
Lewis--Rossi--Weitsman construction.  They include iteration of endpoint
growth, solution of the path-length recurrence, and summability of an
exponential whose negative term grows geometrically.
-/

open Filter

open scoped BigOperators Topology

namespace Erdos515

/-- Iterating a one-step geometric lower bound, starting at an arbitrary index. -/
lemma endpoint_growth {u : ℕ → ℝ} {q : ℝ} (hq : 0 ≤ q)
    (hstep : ∀ k, q * u k ≤ u (k + 1)) (m k : ℕ) :
    q ^ k * u m ≤ u (m + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        q ^ (k + 1) * u m = q * (q ^ k * u m) := by ring
        _ ≤ q * u (m + k) := mul_le_mul_of_nonneg_left ih hq
        _ ≤ u (m + k + 1) := hstep (m + k)
        _ = u (m + (k + 1)) := by rw [Nat.add_assoc]

/-- The one-indexed form of `endpoint_growth`, matching the endpoint numbering in LRW. -/
lemma endpoint_growth_from_one {u : ℕ → ℝ} {q : ℝ} (hq : 0 ≤ q)
    (hstep : ∀ k, q * u (k + 1) ≤ u (k + 2)) (k : ℕ) :
    q ^ k * u 1 ≤ u (k + 1) := by
  simpa [Nat.add_comm] using
    endpoint_growth (u := fun j ↦ u (j + 1)) hq hstep 0 k

/-- Endpoint growth with the LRW multiplier `(1 - δ)⁻¹`. -/
lemma endpoint_growth_one_sub {u : ℕ → ℝ} {δ : ℝ} (hδ : δ < 1)
    (hstep : ∀ k, (1 - δ)⁻¹ * u (k + 1) ≤ u (k + 2)) (k : ℕ) :
    (1 - δ)⁻¹ ^ k * u 1 ≤ u (k + 1) := by
  exact endpoint_growth_from_one (inv_nonneg.mpr (sub_nonneg.mpr hδ.le)) hstep k

/--
If `q > 1`, positive geometrically growing endpoints tend to infinity.
-/
lemma endpoint_tendsto_atTop {u : ℕ → ℝ} {q : ℝ} (hq : 1 < q)
    (hu : 0 < u 0) (hstep : ∀ k, q * u k ≤ u (k + 1)) :
    Tendsto u atTop atTop := by
  exact tendsto_atTop_mono' atTop
    (Eventually.of_forall fun k ↦ by
      simpa using endpoint_growth (zero_le_one.trans hq.le) hstep 0 k)
    ((tendsto_pow_atTop_atTop_of_one_lt hq).atTop_mul_const hu)

/--
The partial-sum estimate behind the path-length recurrence.  If

`L k ≤ c * ((∑ i < k, L i) + d k)`

and `d` is nondecreasing, then the preceding lengths total at most
`((1 + c)^k - 1) * d k`.
-/
lemma length_partialSum_le {L d : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hd : Monotone d)
    (hL : ∀ k, L k ≤ c * ((∑ i ∈ Finset.range k, L i) + d k)) (k : ℕ) :
    (∑ i ∈ Finset.range k, L i) ≤ ((1 + c) ^ k - 1) * d k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hbase : 1 ≤ 1 + c := by linarith
      have hcoeff : 0 ≤ (1 + c) ^ (k + 1) - 1 :=
        sub_nonneg.mpr (one_le_pow₀ hbase)
      calc
        (∑ i ∈ Finset.range (k + 1), L i) =
            (∑ i ∈ Finset.range k, L i) + L k := Finset.sum_range_succ L k
        _ ≤ (∑ i ∈ Finset.range k, L i) +
            c * ((∑ i ∈ Finset.range k, L i) + d k) :=
          add_le_add le_rfl (hL k)
        _ = (1 + c) * (∑ i ∈ Finset.range k, L i) + c * d k := by ring
        _ ≤ (1 + c) * (((1 + c) ^ k - 1) * d k) + c * d k :=
          add_le_add (mul_le_mul_of_nonneg_left ih (by linarith)) le_rfl
        _ = ((1 + c) ^ (k + 1) - 1) * d k := by rw [pow_succ]; ring
        _ ≤ ((1 + c) ^ (k + 1) - 1) * d (k + 1) :=
          mul_le_mul_of_nonneg_left (hd (Nat.le_succ k)) hcoeff

/-- The closed-form bound obtained from the LRW path-length recurrence. -/
lemma length_recurrence {L d : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hd : Monotone d)
    (hL : ∀ k, L k ≤ c * ((∑ i ∈ Finset.range k, L i) + d k)) (k : ℕ) :
    L k ≤ c * (1 + c) ^ k * d k := by
  calc
    L k ≤ c * ((∑ i ∈ Finset.range k, L i) + d k) := hL k
    _ ≤ c * ((((1 + c) ^ k - 1) * d k) + d k) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (length_partialSum_le hc hd hL k) le_rfl) hc
    _ = c * (1 + c) ^ k * d k := by ring

/--
An exponential with a negative geometrically growing term is summable:
`exp (C k - b a^k)` has an eventually geometric tail whenever `a > 1`
and `b > 0`.
-/
theorem summable_exp_linear_sub_geometric (C : ℝ) {a b : ℝ}
    (ha : 1 < a) (hb : 0 < b) :
    Summable (fun k : ℕ ↦ Real.exp (C * (k : ℝ) - b * a ^ k)) := by
  have hcoeff : 0 < b * (a - 1) := mul_pos hb (sub_pos.mpr ha)
  have hpow : Tendsto (fun k : ℕ ↦ a ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt ha
  have hgrow : Tendsto (fun k : ℕ ↦ b * (a - 1) * a ^ k) atTop atTop :=
    hpow.const_mul_atTop hcoeff
  refine summable_of_ratio_norm_eventually_le (r := Real.exp (-1))
    (Real.exp_lt_one_iff.mpr (by norm_num)) ?_
  filter_upwards [hgrow.eventually (eventually_ge_atTop (C + 1))] with k hk
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [pow_succ]
  norm_num [Nat.cast_add, Nat.cast_one]
  nlinarith

end Erdos515
