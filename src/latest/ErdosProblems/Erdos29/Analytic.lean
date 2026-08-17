/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Analytic estimates for Erdős Problem 29

The mixed-radix construction used for Problem 29 has two elementary
asymptotic features.  At digit level `k`, its representation count is bounded
by a polynomial in `k` times a fixed exponential `M ^ k`.  On the other hand,
the place value below an integer of level `k` is at least
`(k / 2) ^ k`.  This file isolates the resulting analytic implication: the
representation count is smaller than every positive real power of the
integer.

The lemmas are stated for an arbitrary level map and arbitrary real-valued
function, so the combinatorial files need only supply the indicated pointwise
bounds.
-/

open Filter Topology

namespace Erdos29.Analytic

open scoped NNReal

/-! ## Polynomial times exponential growth along a level map -/

/-- A polynomial times a fixed exponential remains little-o of every strictly
larger exponential after composition with a level map tending to infinity. -/
theorem levelPolynomialExponential_isLittleO
    (level : ℕ → ℕ) (hlevel : Tendsto level atTop atTop)
    (d : ℕ) (C M R : ℝ) (hMR : |M| < R) :
    (fun n : ℕ ↦ C * (level n : ℝ) ^ d * M ^ level n) =o[atTop]
      (fun n : ℕ ↦ R ^ level n) := by
  have hR : 0 < R := (abs_nonneg M).trans_lt hMR
  have hratio : |M / R| < 1 := by
    rw [abs_div, abs_of_pos hR]
    exact (div_lt_one hR).2 hMR
  have hzero :
      Tendsto (fun k : ℕ ↦ (k : ℝ) ^ d * (M / R) ^ k) atTop (nhds 0) :=
    tendsto_pow_const_mul_const_pow_of_abs_lt_one d hratio
  have hbase :
      (fun k : ℕ ↦ C * (k : ℝ) ^ d * M ^ k) =o[atTop]
        (fun k : ℕ ↦ R ^ k) := by
    have hzeroC :
        Tendsto (fun k : ℕ ↦ C * ((k : ℝ) ^ d * (M / R) ^ k)) atTop (nhds 0) := by
      simpa using hzero.const_mul C
    rw [Asymptotics.isLittleO_iff_tendsto']
    · convert hzeroC using 1
      ext k
      rw [div_pow]
      ring
    · filter_upwards [] with k hk
      exact False.elim ((pow_ne_zero k hR.ne') hk)
  change
    ((fun k : ℕ ↦ C * (k : ℝ) ^ d * M ^ k) ∘ level) =o[atTop]
      ((fun k : ℕ ↦ R ^ k) ∘ level)
  exact hbase.comp_tendsto hlevel

/-- Transfer the preceding estimate through an eventual upper bound for the
function and an eventual lower bound for the target scale. -/
theorem isLittleO_of_levelExponential_bounds
    (f g : ℕ → ℝ) (level : ℕ → ℕ)
    (hlevel : Tendsto level atTop atTop)
    (d : ℕ) (C M R : ℝ)
    (_hC : 0 ≤ C) (hM : 0 ≤ M) (hR : 0 ≤ R) (hMR : M < R)
    (hf : ∀ᶠ n in atTop,
      |f n| ≤ C * (level n : ℝ) ^ d * M ^ level n)
    (hg : ∀ᶠ n in atTop, R ^ level n ≤ |g n|) :
    f =o[atTop] g := by
  have hMabs : |M| < R := by simpa [abs_of_nonneg hM] using hMR
  have hpoly :
      (fun n : ℕ ↦ C * (level n : ℝ) ^ d * M ^ level n) =o[atTop]
        (fun n : ℕ ↦ R ^ level n) :=
    levelPolynomialExponential_isLittleO level hlevel d C M R hMabs
  have hfO :
      f =O[atTop] (fun n : ℕ ↦ C * (level n : ℝ) ^ d * M ^ level n) := by
    apply Asymptotics.IsBigO.of_norm_eventuallyLE
    filter_upwards [hf] with n hn
    simpa [Real.norm_eq_abs] using hn
  have hgO : (fun n : ℕ ↦ R ^ level n) =O[atTop] g := by
    apply Asymptotics.IsBigO.of_bound'
    filter_upwards [hg] with n hn
    simpa [Real.norm_eq_abs, abs_pow, abs_of_nonneg hR] using hn
  exact (hfO.trans_isLittleO hpoly).trans_isBigO hgO

/-! ## Superexponential place values dominate every fixed exponential -/

/-- Division by two still tends to infinity along every natural-valued map
tending to infinity. -/
theorem tendsto_level_div_two_atTop
    (level : ℕ → ℕ) (hlevel : Tendsto level atTop atTop) :
    Tendsto (fun n ↦ level n / 2) atTop atTop := by
  have hdiv : Tendsto (fun k : ℕ ↦ k / 2) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨2 * b, ?_⟩
    intro a ha
    omega
  exact hdiv.comp hlevel

/-- If `n` dominates `(level n / 2) ^ level n`, then every fixed exponential
in the level is eventually bounded by `n ^ ε` for each `ε > 0`.

The exponent on the right is real (`Real.rpow`), as required by the exact
statement of Problem 29. -/
theorem eventually_constPowLevel_le_rpow_of_superexponential
    (level : ℕ → ℕ) (hlevel : Tendsto level atTop atTop)
    (M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε)
    (hgrowth : ∀ᶠ n in atTop, (level n / 2) ^ level n ≤ n) :
    ∀ᶠ n in atTop, (2 * M) ^ level n ≤ (n : ℝ) ^ ε := by
  let B : ℝ := (2 * M) ^ ε⁻¹
  have hB0 : 0 ≤ B := Real.rpow_nonneg (mul_nonneg (by norm_num) hM) _
  have hcastDiv :
      Tendsto (fun n ↦ ((level n / 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_level_div_two_atTop level hlevel)
  have hB : ∀ᶠ n in atTop, B ≤ ((level n / 2 : ℕ) : ℝ) :=
    hcastDiv.eventually_ge_atTop B
  filter_upwards [hB, hgrowth] with n hnB hnGrowth
  let q : ℕ := level n / 2
  have hbase : 2 * M ≤ (q : ℝ) ^ ε := by
    calc
      2 * M = B ^ ε := by
        symm
        simpa only [B] using
          (Real.rpow_inv_rpow (mul_nonneg (by norm_num) hM) hε.ne')
      _ ≤ (q : ℝ) ^ ε := Real.rpow_le_rpow hB0 hnB hε.le
  calc
    (2 * M) ^ level n ≤ ((q : ℝ) ^ ε) ^ level n := by
      gcongr
    _ = (((q ^ level n : ℕ) : ℝ) ^ ε) := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg q), mul_comm,
        Real.rpow_natCast_mul (Nat.cast_nonneg q), Nat.cast_pow]
    _ ≤ (n : ℝ) ^ ε := by
      apply Real.rpow_le_rpow (by positivity) _ hε.le
      exact_mod_cast hnGrowth

/-! ## End-to-end little-o criterion -/

/-- A convenient end-to-end criterion for the mixed-radix construction.

The three substantive hypotheses are precisely the outputs expected from the
digital part of the proof:

* the level tends to infinity;
* the integer at that level is at least `(level / 2) ^ level`;
* the representation count is bounded by `C * level ^ d * M ^ level`.

The conclusion is the exact real-valued little-o assertion used in Problem 29.
-/
theorem isLittleO_rpow_of_level_superexponential
    (f : ℕ → ℝ) (level : ℕ → ℕ)
    (d : ℕ) (C M ε : ℝ)
    (hC : 0 ≤ C) (hM : 0 < M) (hε : 0 < ε)
    (hlevel : Tendsto level atTop atTop)
    (hgrowth : ∀ᶠ n in atTop, (level n / 2) ^ level n ≤ n)
    (hf : ∀ᶠ n in atTop,
      |f n| ≤ C * (level n : ℝ) ^ d * M ^ level n) :
    f =o[atTop] (fun n : ℕ ↦ (n : ℝ) ^ ε) := by
  apply isLittleO_of_levelExponential_bounds
      f (fun n : ℕ ↦ (n : ℝ) ^ ε) level hlevel d C M (2 * M)
      hC hM.le (mul_nonneg (by norm_num) hM.le) (by linarith)
      hf
  simpa [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using
    eventually_constPowLevel_le_rpow_of_superexponential
    level hlevel M ε hM.le hε hgrowth

end Erdos29.Analytic
