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

/-!
# Scalar estimates for Alon's sparse-subgraph parameters

This file isolates the elementary asymptotic estimates used in the local
lemma step of Alon's linear-arboricity argument.  It deliberately does not
import the graph-theoretic sampling construction, so that construction can
use these estimates without creating an import cycle.
-/

open Filter
open scoped Topology

namespace Erdos622
namespace AlonScalar

noncomputable section

private lemma tendsto_natLog_atTop :
    Tendsto (fun D : ℕ ↦ Real.log (D : ℝ)) atTop atTop := by
  exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private lemma tendsto_natLogLog_atTop :
    Tendsto (fun D : ℕ ↦ Real.log (Real.log (D : ℝ))) atTop atTop := by
  exact Real.tendsto_log_atTop.comp tendsto_natLog_atTop

/-- A fixed power of the logarithm is eventually bounded by its argument,
specialized to the tenth power used as the sampled mean degree. -/
theorem eventually_log_pow_ten_le :
    ∀ᶠ D : ℕ in atTop, Real.log (D : ℝ) ^ 10 ≤ (D : ℝ) := by
  have hratio : Tendsto (fun D : ℕ ↦
      Real.log (D : ℝ) ^ 10 / (D : ℝ)) atTop (nhds 0) := by
    exact Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hlt := hratio.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hlt, eventually_gt_atTop (0 : ℕ)] with D hD hDpos
  have hDposReal : (0 : ℝ) < D := by exact_mod_cast hDpos
  rw [div_lt_iff₀ hDposReal] at hD
  simpa only [one_mul] using hD.le

/-- The integral short-cycle cutoff is eventually at most one quarter of
the square root of the ambient maximum degree. -/
theorem eventually_four_mul_floor_log_div_loglog_add_one_le_sqrt :
    ∀ᶠ D : ℕ in atTop,
      4 * ((⌊Real.log (D : ℝ) /
          (20 * Real.log (Real.log (D : ℝ)))⌋₊ + 1 : ℕ) : ℝ) ≤
        Real.sqrt D := by
  have hsmallReal :=
    (isLittleO_log_rpow_atTop (r := (1 : ℝ) / 2) (by norm_num)).bound
      (by norm_num : (0 : ℝ) < 1 / 8)
  have hsmallNat := tendsto_natCast_atTop_atTop.eventually hsmallReal
  filter_upwards [eventually_ge_atTop (64 : ℕ),
      tendsto_natLog_atTop.eventually_ge_atTop 1,
      tendsto_natLogLog_atTop.eventually_ge_atTop 1,
      hsmallNat] with D hD hlog hloglog hsmall
  have hDnonneg : (0 : ℝ) ≤ D := by positivity
  have hlognonneg : 0 ≤ Real.log (D : ℝ) := le_trans zero_le_one hlog
  have hsqrtnonneg : 0 ≤ Real.sqrt (D : ℝ) := Real.sqrt_nonneg _
  have hrpow : (D : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt D := by
    exact (Real.sqrt_eq_rpow (D : ℝ)).symm
  have hlogSmall :
      Real.log (D : ℝ) ≤ (1 / 8 : ℝ) * Real.sqrt D := by
    rw [Real.norm_of_nonneg hlognonneg] at hsmall
    have hrpowNonneg :
        0 ≤ (D : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hDnonneg _
    rw [Real.norm_of_nonneg hrpowNonneg] at hsmall
    rw [hrpow] at hsmall
    exact hsmall
  have hsqrtEight : (8 : ℝ) ≤ Real.sqrt D := by
    have hDR : (64 : ℝ) ≤ D := by exact_mod_cast hD
    nlinarith [Real.sq_sqrt hDnonneg]
  have hdenom : (1 : ℝ) ≤ 20 * Real.log (Real.log (D : ℝ)) := by
    nlinarith
  have harg_nonneg :
      0 ≤ Real.log (D : ℝ) /
        (20 * Real.log (Real.log (D : ℝ))) := by positivity
  have harg_le_log :
      Real.log (D : ℝ) /
          (20 * Real.log (Real.log (D : ℝ))) ≤
        Real.log (D : ℝ) := by
    exact div_le_self hlognonneg hdenom
  have hfloor :
      ((⌊Real.log (D : ℝ) /
          (20 * Real.log (Real.log (D : ℝ)))⌋₊ : ℕ) : ℝ) ≤
        Real.log (D : ℝ) :=
    (Nat.floor_le harg_nonneg).trans harg_le_log
  push_cast
  nlinarith

private theorem two_mul_floor_le_of_cutoff {D s : ℕ}
    (hD : 1 ≤ D)
    (hcutoff : 4 * (((s + 1 : ℕ) : ℝ)) ≤ Real.sqrt D) :
    2 * s ≤ D := by
  have hDnonneg : (0 : ℝ) ≤ D := by positivity
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hsqrt_le : Real.sqrt (D : ℝ) ≤ D := by
    nlinarith [Real.sq_sqrt hDnonneg, Real.sqrt_nonneg (D : ℝ)]
  have hsReal : ((2 * s : ℕ) : ℝ) ≤ D := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
      Nat.cast_one] at hcutoff ⊢
    nlinarith
  exact_mod_cast hsReal

/-- All scalar inequalities needed to instantiate the vertex and cycle
weights in Alon's asymmetric local-lemma argument hold simultaneously for
all sufficiently large natural degrees. -/
theorem eventually_alon_scalar_conditions :
    ∀ᶠ D : ℕ in atTop,
      32 ≤ D ∧
      12 ≤ Real.log (D : ℝ) ∧
      0 < Real.log (Real.log (D : ℝ)) ∧
      Real.log (D : ℝ) ^ 10 ≤ (D : ℝ) ∧
      2 * ⌊Real.log (D : ℝ) /
          (20 * Real.log (Real.log (D : ℝ)))⌋₊ ≤ D ∧
      4 * ((⌊Real.log (D : ℝ) /
          (20 * Real.log (Real.log (D : ℝ)))⌋₊ + 1 : ℕ) : ℝ) ≤
        Real.sqrt D := by
  filter_upwards [eventually_ge_atTop (32 : ℕ),
      tendsto_natLog_atTop.eventually_ge_atTop 12,
      tendsto_natLogLog_atTop.eventually_gt_atTop 0,
      eventually_log_pow_ten_le,
      eventually_four_mul_floor_log_div_loglog_add_one_le_sqrt] with
      D hD hlog hloglog hpow hcutoff
  have htwice :
      2 * ⌊Real.log (D : ℝ) /
          (20 * Real.log (Real.log (D : ℝ)))⌋₊ ≤ D :=
    two_mul_floor_le_of_cutoff (by omega) hcutoff
  exact ⟨hD, hlog, hloglog, hpow, htwice, hcutoff⟩

end

end AlonScalar
end Erdos622
