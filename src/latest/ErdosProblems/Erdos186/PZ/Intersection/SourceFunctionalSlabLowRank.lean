/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SourceFunctionalSlabDenseDilation
import ErdosProblems.Erdos186.PZ.SourceParameterAsymptotics

/-!
# The source-parameter low-rank slab hierarchy

The source growth `gamma * delta^eta * N^eta → ∞` dominates the one
finite constant needed for every rank below `rankCeiling`.  The eligible-input
scale lower bound then converts that growth into selected CFP dilation.
-/

namespace Erdos186.PZ.Intersection

open Filter
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- Eventually every dense eligible input of bounded rank satisfies both
forward and reverse low-rank functional-slab inequalities. -/
theorem eventually_sourceFunctionalSlab_lowRank
    {beta eta : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (heta : 0 < eta)
    (kappa K : ℝ) (hK : 0 < K)
    (forwardConstant reverseConstant : ℝ)
    (hforward : 0 ≤ forwardConstant) (hreverse : 0 ≤ reverseConstant) :
    ∀ᶠ N : ℕ in atTop,
      ∀ {r : ℕ} {X : Finset (LatticePoint r)}
        (I : Reduction.EligibleInput context X),
        r ≤ rankCeiling →
        delta kappa N * (N : ℝ) ≤ (X.card : ℝ) →
        sourceFunctionalSlabFixedTerm context forwardConstant r <
            (I.selectedCFP.dilation : ℝ) * gamma kappa K N ∧
          sourceFunctionalSlabFixedTerm context reverseConstant r <
            (I.selectedCFP.dilation : ℝ) * gamma kappa K N := by
  let D : ℕ := Reduction.scaleDenSum context rankCeiling
  let B : ℝ := sourceFunctionalSlabTermBound context rankCeiling
    forwardConstant reverseConstant
  have hD : 0 < D := Reduction.scaleDenSum_pos context rankCeiling
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hB : 0 ≤ B := sourceFunctionalSlabTermBound_nonneg
    (context := context) hforward hreverse
  have hgrowth := eventually_const_le_gamma_mul_delta_rpow_mul_nat_rpow
    kappa K heta ((D : ℝ) * B + 1)
  filter_upwards [hgrowth, eventually_delta_pos kappa,
      eventually_gamma_pos kappa hK]
    with N hgrowthN hdeltaN hgammaN
  intro r X I hrank hdense
  have hpower : delta kappa N ^ eta * (N : ℝ) ^ eta ≤
      (D : ℝ) * (I.selectedCFP.dilation : ℝ) := by
    simpa only [D] using fixed_dense_power_le_scaleDenSum_mul_dilation
      context I heta.le hdeltaN.le hrank hdense
  have hscaled :
      gamma kappa K N *
          (delta kappa N ^ eta * (N : ℝ) ^ eta) ≤
        gamma kappa K N *
          ((D : ℝ) * (I.selectedCFP.dilation : ℝ)) :=
    mul_le_mul_of_nonneg_left hpower hgammaN.le
  have hDB : (D : ℝ) * B <
      (D : ℝ) *
        ((I.selectedCFP.dilation : ℝ) * gamma kappa K N) := by
    calc
      (D : ℝ) * B < (D : ℝ) * B + 1 := by linarith
      _ ≤ gamma kappa K N * delta kappa N ^ eta *
          (N : ℝ) ^ eta := by simpa only [mul_assoc] using hgrowthN
      _ ≤ gamma kappa K N *
          ((D : ℝ) * (I.selectedCFP.dilation : ℝ)) := by
        simpa only [mul_assoc] using hscaled
      _ = (D : ℝ) *
          ((I.selectedCFP.dilation : ℝ) * gamma kappa K N) := by ring
  have hBstrict : B <
      (I.selectedCFP.dilation : ℝ) * gamma kappa K N :=
    (mul_lt_mul_iff_of_pos_left hDreal).mp hDB
  constructor
  · exact (sourceFunctionalSlabFixedTerm_le_bound
      hforward hreverse hrank).trans_lt hBstrict
  · exact (sourceFunctionalSlabReverseFixedTerm_le_bound
      hforward hreverse hrank).trans_lt hBstrict

end

end Erdos186.PZ.Intersection
