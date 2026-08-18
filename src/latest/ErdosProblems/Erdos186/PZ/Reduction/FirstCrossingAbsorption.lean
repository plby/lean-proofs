/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.Asymptotic

namespace Erdos186.PZ.Reduction

open Filter
open scoped Topology

noncomputable section

/-- A fixed loss is absorbed by the negative power obtained at the first
forbidden upward-jump crossing. -/
theorem exists_firstCrossingAbsorption_threshold
    (cost initialCost beta a : ℝ) (changeCap J : ℕ)
    (hcost : 0 < cost) (hinitialCost : 0 < initialCost)
    (hgap : beta < a * (J + 1 : ℕ)) :
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ m : ℕ, threshold ≤ m →
        cost ^ changeCap * (Real.rpow (m : ℝ) (-a)) ^ (J + 1) *
          (initialCost * Real.rpow (m : ℝ) beta) < 1 := by
  let q : ℝ := a * (J + 1 : ℕ) - beta
  have hq : 0 < q := by dsimp [q]; linarith
  let fixed : ℝ := cost ^ changeCap * initialCost
  have hfixed : 0 < fixed := mul_pos (pow_pos hcost _) hinitialCost
  have heventual := (nat_rpow_tendsto_atTop hq).eventually_gt_atTop fixed
  obtain ⟨t, ht⟩ := eventually_atTop.1 heventual
  refine ⟨max 2 t, le_max_left _ _, ?_⟩
  intro m hm
  have htm : t ≤ m := (le_max_right 2 t).trans hm
  have hmgrowth : fixed < Real.rpow (m : ℝ) q := ht m htm
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (show 0 < m by omega)
  have hmqpos : 0 < Real.rpow (m : ℝ) q :=
    Real.rpow_pos_of_pos hmpos _
  have hpower : (Real.rpow (m : ℝ) (-a)) ^ (J + 1) *
      Real.rpow (m : ℝ) beta =
        (Real.rpow (m : ℝ) q)⁻¹ := by
    calc
      (Real.rpow (m : ℝ) (-a)) ^ (J + 1) *
          Real.rpow (m : ℝ) beta =
        Real.rpow (m : ℝ) ((-a) * (J + 1 : ℕ)) *
          Real.rpow (m : ℝ) beta := by
            have hnat := Real.rpow_natCast (Real.rpow (m : ℝ) (-a)) (J + 1)
            have hp' : Real.rpow (m : ℝ) ((-a) * ((J + 1 : ℕ) : ℝ)) =
                Real.rpow (Real.rpow (m : ℝ) (-a)) ((J + 1 : ℕ) : ℝ) := by
              exact Real.rpow_mul hmpos.le (-a) ((J + 1 : ℕ) : ℝ)
            have hpowNat : (Real.rpow (m : ℝ) (-a)) ^ (J + 1) =
                Real.rpow (m : ℝ) ((-a) * ((J + 1 : ℕ) : ℝ)) :=
              hnat.symm.trans hp'.symm
            rw [hpowNat]
      _ = Real.rpow (m : ℝ) (((-a) * (J + 1 : ℕ)) + beta) :=
        (Real.rpow_add hmpos _ _).symm
      _ = Real.rpow (m : ℝ) (-q) := by
        congr 1
        dsimp [q]
        ring
      _ = (Real.rpow (m : ℝ) q)⁻¹ := Real.rpow_neg hmpos.le q
  calc
    cost ^ changeCap * (Real.rpow (m : ℝ) (-a)) ^ (J + 1) *
          (initialCost * Real.rpow (m : ℝ) beta) =
        fixed * ((Real.rpow (m : ℝ) (-a)) ^ (J + 1) *
          Real.rpow (m : ℝ) beta) := by ring
    _ = fixed / Real.rpow (m : ℝ) q := by rw [hpower, div_eq_mul_inv]
    _ < 1 := (div_lt_one hmqpos).2 hmgrowth

end

end Erdos186.PZ.Reduction
