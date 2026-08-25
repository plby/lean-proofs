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
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# Parameter estimates for Pippenger--Spencer

This file collects two elementary analytic bookkeeping facts used in a
finite nibble proof.

* An exponentially small bad-event probability beats any fixed polynomial
  dependency bound, so the symmetric local-lemma condition eventually holds.
* Floored batch sizes are bounded by a finite geometric series.  Explicit
  batch, residual, and rounding budgets then imply the desired total-colour
  bound.

There is no hypergraph dependency in this file.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos76
namespace PippengerSpencerParameters

noncomputable section

/-- The exponential tail times a polynomial tends to zero.  The form of the
expression matches the bad-event probability and dependency estimate in the
symmetric local lemma. -/
theorem tendsto_exp_tail_mul_polynomial (c C : ℝ) (r : ℕ) (hc : 0 < c) :
    Tendsto (fun x : ℝ ↦ 2 * Real.exp (-c * x) * (C * x ^ r + 1))
      atTop (𝓝 0) := by
  have hpow : Tendsto (fun x : ℝ ↦ x ^ r * Real.exp (-c * x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (r : ℝ) c hc
  have hexp : Tendsto (fun x : ℝ ↦ Real.exp (-c * x)) atTop (𝓝 0) := by
    simpa using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0 : ℝ) c hc)
  convert (hpow.const_mul (2 * C)).add (hexp.const_mul 2) using 1
  · ext x
    ring
  · norm_num

/-- For fixed positive exponential rate `c`, fixed coefficient `C`, and fixed
natural exponent `r`, the finite-LLL condition
`2 * exp (-cD) * (C D^r + 1) <= 1` holds for every sufficiently large natural
`D`.  The conclusion in fact needs no sign assumption on `C`. -/
theorem exists_exp_tail_mul_polynomial_le_one (c C : ℝ) (r : ℕ) (hc : 0 < c) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      2 * Real.exp (-c * (D : ℝ)) * (C * (D : ℝ) ^ r + 1) ≤ 1 := by
  have hnat :
      Tendsto
        (fun D : ℕ ↦ 2 * Real.exp (-c * (D : ℝ)) * (C * (D : ℝ) ^ r + 1))
        atTop (𝓝 0) :=
    (tendsto_exp_tail_mul_polynomial c C r hc).comp tendsto_natCast_atTop_atTop
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.mp ((tendsto_order.1 hnat).2 1 zero_lt_one)
  exact ⟨D₀, fun D hD ↦ (hD₀ D hD).le⟩

/-- The nonnegative-coefficient interface normally used for dependency
polynomials in a local-lemma application. -/
theorem exists_exp_tail_mul_polynomial_le_one_of_nonneg
    (c C : ℝ) (r : ℕ) (hc : 0 < c) (_hC : 0 ≤ C) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      2 * Real.exp (-c * (D : ℝ)) * (C * (D : ℝ) ^ r + 1) ≤ 1 :=
  exists_exp_tail_mul_polynomial_le_one c C r hc

/-- Total number of colours allocated in the first `s` nibble batches, after
rounding every real batch size down. -/
def batchColors (theta q : ℝ) (s D : ℕ) : ℕ :=
  ∑ i ∈ range s, ⌊theta * q ^ i * (D : ℝ)⌋₊

/-- The exact finite geometric-series identity in the normalization used by
the nibble parameters. -/
lemma sum_range_geometric_eq {q : ℝ} (s : ℕ) (hq : q < 1) :
    ∑ i ∈ range s, q ^ i = (1 - q ^ s) / (1 - q) := by
  rw [geom_sum_eq hq.ne s]
  rw [show q - 1 = -(1 - q) by ring, div_neg]
  ring

/-- A finite nonnegative geometric sum is at most its infinite-series
majorant.  This version also covers `q = 0`. -/
lemma sum_range_geometric_le_inv {q : ℝ} (s : ℕ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑ i ∈ range s, q ^ i ≤ (1 - q)⁻¹ := by
  simpa [one_div] using
    (geom_sum_Ico_le_of_lt_one (x := q) (m := 0) (n := s) hq0 hq1)

/-- Dropping floors bounds the total batch allocation by the corresponding
finite geometric sum. -/
lemma natCast_batchColors_le_geometricSum
    {theta q : ℝ} {s D : ℕ} (htheta : 0 ≤ theta) (hq : 0 ≤ q) :
    (batchColors theta q s D : ℝ) ≤
      theta * (∑ i ∈ range s, q ^ i) * (D : ℝ) := by
  rw [batchColors, Nat.cast_sum]
  calc
    (∑ i ∈ range s, (⌊theta * q ^ i * (D : ℝ)⌋₊ : ℝ)) ≤
        ∑ i ∈ range s, theta * q ^ i * (D : ℝ) := by
      apply sum_le_sum
      intro i hi
      exact Nat.floor_le
        (mul_nonneg (mul_nonneg htheta (pow_nonneg hq i)) (Nat.cast_nonneg D))
    _ = theta * (∑ i ∈ range s, q ^ i) * (D : ℝ) := by
      rw [Finset.mul_sum, Finset.sum_mul]

/-- Convenient infinite-geometric-series majorant for all floored batch
allocations. -/
lemma natCast_batchColors_le_div
    {theta q : ℝ} {s D : ℕ} (htheta : 0 ≤ theta) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (batchColors theta q s D : ℝ) ≤ theta / (1 - q) * (D : ℝ) := by
  calc
    (batchColors theta q s D : ℝ) ≤
        theta * (∑ i ∈ range s, q ^ i) * (D : ℝ) :=
      natCast_batchColors_le_geometricSum htheta hq0
    _ ≤ theta * (1 - q)⁻¹ * (D : ℝ) := by
      gcongr
      exact sum_range_geometric_le_inv s hq0 hq1
    _ = theta / (1 - q) * (D : ℝ) := by rw [div_eq_mul_inv]

/-- Component-budget form of the Pippenger--Spencer colour count.  The first
component pays for every floored nibble batch, the second for greedily
colouring the residual hypergraph, and `rho` pays for the final additive one. -/
theorem total_colors_le_of_components
    {theta q gamma sigma rho : ℝ} {k s D : ℕ}
    (htheta : 0 ≤ theta) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hrounding : 1 ≤ rho * (D : ℝ))
    (hbudget :
      theta / (1 - q) + (k : ℝ) * (1 + gamma) * q ^ s + rho ≤ 1 + sigma) :
    (batchColors theta q s D : ℝ) +
        (k : ℝ) * (1 + gamma) * q ^ s * (D : ℝ) + 1 ≤
      (1 + sigma) * (D : ℝ) := by
  have hbatch := natCast_batchColors_le_div
    (s := s) (D := D) htheta hq0 hq1
  calc
    (batchColors theta q s D : ℝ) +
          (k : ℝ) * (1 + gamma) * q ^ s * (D : ℝ) + 1 ≤
        theta / (1 - q) * (D : ℝ) +
          (k : ℝ) * (1 + gamma) * q ^ s * (D : ℝ) + rho * (D : ℝ) := by
      gcongr
    _ = (theta / (1 - q) + (k : ℝ) * (1 + gamma) * q ^ s + rho) *
          (D : ℝ) := by ring
    _ ≤ (1 + sigma) * (D : ℝ) :=
      mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg D)

/-- A split-budget interface convenient for choosing parameters in stages.
`beta` pays for the geometric batch sum, `delta` pays for the residual greedy
colouring, and `rho` pays for integer rounding. -/
theorem total_colors_le_of_split_components
    {theta q gamma sigma beta delta rho : ℝ} {k s D : ℕ}
    (htheta : 0 ≤ theta) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbatch : theta / (1 - q) ≤ beta)
    (hresidual : (k : ℝ) * (1 + gamma) * q ^ s ≤ delta)
    (hrounding : 1 ≤ rho * (D : ℝ))
    (hbudget : beta + delta + rho ≤ 1 + sigma) :
    (batchColors theta q s D : ℝ) +
        (k : ℝ) * (1 + gamma) * q ^ s * (D : ℝ) + 1 ≤
      (1 + sigma) * (D : ℝ) := by
  apply total_colors_le_of_components htheta hq0 hq1 hrounding
  exact (add_le_add (add_le_add hbatch hresidual) le_rfl).trans hbudget

/-- The same total-colour bound with the canonical rounding budget `1 / D`.
This is the displayed inequality normally used after the nibble iteration. -/
theorem total_colors_le_of_inverse_rounding
    {theta q gamma sigma : ℝ} {k s D : ℕ}
    (htheta : 0 ≤ theta) (hq0 : 0 ≤ q) (hq1 : q < 1) (hD : 0 < D)
    (hbudget :
      theta / (1 - q) + (k : ℝ) * (1 + gamma) * q ^ s + (D : ℝ)⁻¹ ≤
        1 + sigma) :
    (batchColors theta q s D : ℝ) +
        (k : ℝ) * (1 + gamma) * q ^ s * (D : ℝ) + 1 ≤
      (1 + sigma) * (D : ℝ) := by
  apply total_colors_le_of_components (rho := (D : ℝ)⁻¹) htheta hq0 hq1
  · simp [Nat.cast_ne_zero.mpr hD.ne']
  · exact hbudget

end
end PippengerSpencerParameters
end Erdos76
