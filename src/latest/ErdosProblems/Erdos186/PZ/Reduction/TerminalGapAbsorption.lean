/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.Asymptotic

/-!
# Uniform terminal GAP absorption
-/

namespace Erdos186.PZ.Reduction

open Filter
open scoped Topology

noncomputable section

/-- Choose the source parameter `K` so that the shrink saving at the
population guard dominates the fixed initial polynomial loss.  The natural
threshold is uniform for all `K` above `K0`. -/
theorem exists_terminalGapAbsorption
    (fixed beta tau : ℝ) (changeCap : ℕ)
    (hfixed : 0 < fixed) (htau : tau < 1) :
    ∃ K0 : ℕ, 1 ≤ K0 ∧
      ∃ threshold : ℕ, 2 ≤ threshold ∧
        ∀ K : ℕ, K0 ≤ K → ∀ m : ℕ, threshold ≤ m →
          fixed * Real.rpow (m : ℝ)
            (beta - (K : ℝ) * (1 - tau) +
              ((changeCap + 1 : ℕ) : ℝ) / 3) < 1 := by
  have honeTau : 0 < 1 - tau := sub_pos.mpr htau
  obtain ⟨K0, hK0⟩ := exists_nat_gt
    (max 1 ((beta + ((changeCap + 1 : ℕ) : ℝ) / 3) / (1 - tau)))
  have hK01 : 1 ≤ K0 := by
    have : (1 : ℝ) < K0 := (le_max_left _ _).trans_lt hK0
    exact_mod_cast this.le
  have hgap : beta + ((changeCap + 1 : ℕ) : ℝ) / 3 <
      (K0 : ℝ) * (1 - tau) := by
    have hratio :
        (beta + ((changeCap + 1 : ℕ) : ℝ) / 3) / (1 - tau) < K0 :=
      (le_max_right _ _).trans_lt hK0
    exact (div_lt_iff₀ honeTau).mp hratio
  let q : ℝ := (K0 : ℝ) * (1 - tau) -
    (beta + ((changeCap + 1 : ℕ) : ℝ) / 3)
  have hq : 0 < q := by dsimp [q]; linarith
  have heventual := (nat_rpow_tendsto_atTop hq).eventually_gt_atTop fixed
  obtain ⟨t, ht⟩ := eventually_atTop.1 heventual
  let threshold := max 2 t
  refine ⟨K0, hK01, threshold, le_max_left _ _, ?_⟩
  intro K hK m hm
  have htm : t ≤ m := (le_max_right 2 t).trans hm
  have hm2 : 2 ≤ m := (le_max_left 2 t).trans hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hmone : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
  have hfixedGrowth : fixed < Real.rpow (m : ℝ) q := ht m htm
  have hbase : fixed * Real.rpow (m : ℝ) (-q) < 1 := by
    rw [show Real.rpow (m : ℝ) (-q) =
      (Real.rpow (m : ℝ) q)⁻¹ from Real.rpow_neg hmpos.le q,
      ← div_eq_mul_inv]
    exact (div_lt_one (Real.rpow_pos_of_pos hmpos _)).2 hfixedGrowth
  have hexponent :
      beta - (K : ℝ) * (1 - tau) +
          ((changeCap + 1 : ℕ) : ℝ) / 3 ≤ -q := by
    have hKreal : (K0 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    dsimp [q]
    nlinarith
  calc
    fixed * Real.rpow (m : ℝ)
        (beta - (K : ℝ) * (1 - tau) +
          ((changeCap + 1 : ℕ) : ℝ) / 3) ≤
      fixed * Real.rpow (m : ℝ) (-q) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hmone hexponent) hfixed.le
    _ < 1 := hbase

end

end Erdos186.PZ.Reduction
