/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.ScaleAsymptotics
import ErdosProblems.Erdos446.SizedBlockBounds

/-!
# Erdős Problem 446: the uniform small-atom condition

At Ford's selected depth the construction scale is the fourth power of the
small-factor bound, while maximality of the depth puts the ambient parameter
below the eighth power of that bound.  This elementary amount of slack makes
`r B/y` smaller than `1/(8 log y)` for every fixed `r`.
-/

namespace Erdos446

open Filter Real
open scoped Topology

/-- Pointwise form of the uniform atom estimate. -/
theorem fordConstructionBound_atom_of_interval
    {M k r y : ℕ}
    (hscale : fordConstructionScale M k ≤ y)
    (hupper : y < fordConstructionScale M k ^ 2)
    (hlarge : 64 * (r : ℝ) ≤ (fordConstructionBound M k : ℝ) ^ 2) :
    (r : ℝ) *
        ((fordConstructionBound M k : ℝ) / (y : ℝ)) ≤
      1 / (8 * Real.log (y : ℝ)) := by
  let B := fordConstructionBound M k
  have hB2 : 2 ≤ B := fordConstructionBound_one_lt M k
  have hBR : 0 < (B : ℝ) := by positivity
  have hy2 : 2 ≤ y := by
    have hBscale : B ≤ fordConstructionScale M k := by
      rw [fordConstructionScale_eq_pow]
      simpa using Nat.pow_le_pow_right (by omega : 0 < B)
        (by omega : 1 ≤ 4)
    omega
  have hyR : 0 < (y : ℝ) := by positivity
  have hylog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hyB8 : y ≤ B ^ 8 := by
    have hsquare : fordConstructionScale M k ^ 2 = B ^ 8 := by
      rw [fordConstructionScale_eq_pow]
      ring
    rw [hsquare] at hupper
    exact hupper.le
  have hlogB : Real.log (B : ℝ) ≤ (B : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hBR
    linarith
  have hlogY : Real.log (y : ℝ) ≤ 8 * (B : ℝ) := by
    have hcast : (y : ℝ) ≤ (B : ℝ) ^ 8 := by
      exact_mod_cast hyB8
    calc
      Real.log (y : ℝ) ≤ Real.log ((B : ℝ) ^ 8) :=
        Real.log_le_log hyR hcast
      _ = 8 * Real.log (B : ℝ) := by rw [Real.log_pow]; norm_num
      _ ≤ 8 * (B : ℝ) := mul_le_mul_of_nonneg_left hlogB (by norm_num)
  have hlogLarge :
      8 * (r : ℝ) * Real.log (y : ℝ) ≤ (B : ℝ) ^ 3 := by
    calc
      8 * (r : ℝ) * Real.log (y : ℝ) ≤
          8 * (r : ℝ) * (8 * (B : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogY (by positivity)
      _ = (64 * (r : ℝ)) * (B : ℝ) := by ring
      _ ≤ (B : ℝ) ^ 2 * (B : ℝ) :=
        mul_le_mul_of_nonneg_right hlarge hBR.le
      _ = (B : ℝ) ^ 3 := by ring
  have hcross :
      ((r : ℝ) * (B : ℝ)) * (8 * Real.log (y : ℝ)) ≤ (y : ℝ) := by
    calc
      ((r : ℝ) * (B : ℝ)) * (8 * Real.log (y : ℝ)) =
          (8 * (r : ℝ) * Real.log (y : ℝ)) * (B : ℝ) := by ring
      _ ≤ (B : ℝ) ^ 3 * (B : ℝ) :=
        mul_le_mul_of_nonneg_right hlogLarge hBR.le
      _ = ((fordConstructionScale M k : ℕ) : ℝ) := by
        rw [fordConstructionScale_eq_pow]
        norm_num [B]
        ring
      _ ≤ (y : ℝ) := by exact_mod_cast hscale
  rw [show (r : ℝ) * ((B : ℝ) / (y : ℝ)) =
      ((r : ℝ) * (B : ℝ)) / (y : ℝ) by ring]
  apply (div_le_iff₀ hyR).2
  calc
    (r : ℝ) * (B : ℝ) ≤ (y : ℝ) / (8 * Real.log (y : ℝ)) :=
      (le_div_iff₀ (mul_pos (by norm_num) hylog)).2 hcross
    _ = (1 / (8 * Real.log (y : ℝ))) * (y : ℝ) := by ring

/-- The construction bound tends to infinity at Ford's selected depth. -/
theorem tendsto_fordConstructionBound_fordScaleDepth_atTop (M : ℕ) :
    Tendsto (fun y : ℕ ↦
      fordConstructionBound M (fordScaleDepth M y)) atTop atTop := by
  have hpow : Tendsto (fun y : ℕ ↦ 2 ^ fordScaleDepth M y) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by omega : (1 : ℕ) < 2)).comp
      (tendsto_fordScaleDepth_atTop M)
  refine Filter.tendsto_atTop_mono' atTop (f₁ := fun y : ℕ ↦
    2 ^ fordScaleDepth M y) ?_ hpow
  filter_upwards with y
  apply Nat.pow_le_pow_right (by omega)
  let k := fordScaleDepth M y
  have hkpow : k ≤ 2 ^ k := k.lt_two_pow_self.le
  have hpowMono : 2 ^ k ≤ 2 ^ (M + k) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  exact hkpow.trans (hpowMono.trans
    (Nat.le_mul_of_pos_left _ (by omega : 0 < 32)))

/-- Eventual uniform atom condition consumed by the finite
exact-multiplicity assembly. -/
theorem eventually_fordConstructionBound_atom
    (r M : ℕ) :
    ∀ᶠ y : ℕ in atTop,
      (r : ℝ) *
          ((fordConstructionBound M (fordScaleDepth M y) : ℝ) /
            (y : ℝ)) ≤
        1 / (8 * Real.log (y : ℝ)) := by
  have hBlarge :=
    (tendsto_fordConstructionBound_fordScaleDepth_atTop M).eventually
      (eventually_ge_atTop (64 * r))
  filter_upwards
      [eventually_ge_atTop (fordConstructionScale M 1), hBlarge]
      with y hy hBlargeY
  let k := fordScaleDepth M y
  have hk : 0 < k := fordScaleDepth_pos hy
  have hinter := fordScaleDepth_interval hy
  have hlargeR :
      64 * (r : ℝ) ≤ (fordConstructionBound M k : ℝ) ^ 2 := by
    have hcast : 64 * (r : ℝ) ≤
        (fordConstructionBound M k : ℝ) := by
      exact_mod_cast hBlargeY
    have hB1 : (1 : ℝ) ≤ fordConstructionBound M k := by
      exact_mod_cast (fordConstructionBound_one_lt M k).le
    exact hcast.trans (by nlinarith)
  exact fordConstructionBound_atom_of_interval hinter.1 hinter.2 hlargeR

end Erdos446
