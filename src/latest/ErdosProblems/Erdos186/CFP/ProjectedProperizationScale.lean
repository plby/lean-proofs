/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.ProjectedProperizationInitialBody
import ErdosProblems.Erdos186.CFP.Bilu.Section92OuterInjectivityBridge

/-!
# Uniform scales for projected properization

The Section 3 outer Mahler box in rank `n` has seminorm radius bounded by
`n^2 * (outerConstant n + 1)` per unit of coefficient dilation.  Taking a
finite sum of ceilings over all `n ≤ D` gives one natural bound.  Dividing
the source dilation by `(D+1)` times this bound leaves enough room for the
terminal outer box and for at most `D` additive rank-drop lifting costs.
-/

namespace Erdos186.CFP.ProjectedProperization

open Bilu.MahlerOuterContainer
open Bilu.Section92OuterInjectivityBridge

noncomputable section

/-- A positive natural upper bound for every unit-dilation outer-body cost
in rank at most `D`. -/
def uniformOuterCost (D : ℕ) : ℕ :=
  1 + ∑ n ∈ Finset.range (D + 1),
    ⌈(n : ℝ) ^ 2 * (outerConstant n + 1)⌉₊

theorem uniformOuterCost_pos (D : ℕ) : 0 < uniformOuterCost D := by
  unfold uniformOuterCost
  omega

/-- The total unit budget: one terminal outer body plus one lifting cost
for every possible rank drop. -/
def projectionUnit (D : ℕ) : ℕ := (D + 1) * uniformOuterCost D

theorem projectionUnit_pos (D : ℕ) : 0 < projectionUnit D := by
  exact Nat.mul_pos (by omega) (uniformOuterCost_pos D)

/-- The advertised loss factor.  The factor two absorbs the floor in the
chosen output scale. -/
def projectionFactor (D : ℕ) : ℕ := 2 * projectionUnit D

theorem projectionFactor_pos (D : ℕ) : 0 < projectionFactor D := by
  exact Nat.mul_pos (by omega) (projectionUnit_pos D)

/-- Output dilation selected from the large source dilation. -/
def projectionScale (D k : ℕ) : ℕ := k / projectionUnit D

/-- Seminorm radius at which every intermediate projected map is tested. -/
def projectionTestRadius (D k : ℕ) : ℕ :=
  uniformOuterCost D * projectionScale D k

theorem outer_unit_cost_le_uniformOuterCost {n D : ℕ} (hn : n ≤ D) :
    (n : ℝ) ^ 2 * (outerConstant n + 1) ≤
      (uniformOuterCost D : ℝ) := by
  let a : ℕ := ⌈(n : ℝ) ^ 2 * (outerConstant n + 1)⌉₊
  have hceil : (n : ℝ) ^ 2 * (outerConstant n + 1) ≤ (a : ℝ) := by
    exact Nat.le_ceil _
  have hmem : n ∈ Finset.range (D + 1) := by
    simp only [Finset.mem_range]
    omega
  have hsum : a ≤ ∑ m ∈ Finset.range (D + 1),
      ⌈(m : ℝ) ^ 2 * (outerConstant m + 1)⌉₊ := by
    exact Finset.single_le_sum
      (fun (i : ℕ) _hi ↦ Nat.zero_le
        ⌈(i : ℝ) ^ 2 * (outerConstant i + 1)⌉₊)
      hmem
  have hsum' : a ≤ uniformOuterCost D := by
    unfold uniformOuterCost
    omega
  exact hceil.trans <| by exact_mod_cast hsum'

/-- The selected output scale is positive throughout the large branch. -/
theorem projectionScale_pos {D k : ℕ}
    (hk : projectionFactor D ≤ k) : 0 < projectionScale D k := by
  apply Nat.div_pos
  · have huFactor : projectionUnit D ≤ projectionFactor D := by
      unfold projectionFactor
      omega
    exact huFactor.trans hk
  · exact projectionUnit_pos D

theorem projectionScale_le_source (D k : ℕ) :
    projectionScale D k ≤ k := by
  exact Nat.div_le_self _ _

/-- The advertised factor recovers the source dilation after flooring. -/
theorem source_le_projectionFactor_mul_scale {D k : ℕ}
    (hk : projectionFactor D ≤ k) :
    k ≤ projectionFactor D * projectionScale D k := by
  let u := projectionUnit D
  let q := projectionScale D k
  have hu : 0 < u := projectionUnit_pos D
  have hu_le : u ≤ k := by
    dsimp only [u]
    have huFactor : projectionUnit D ≤ projectionFactor D := by
      unfold projectionFactor
      omega
    exact huFactor.trans hk
  have hq : 0 < q := by
    dsimp only [q, projectionScale]
    exact Nat.div_pos hu_le hu
  have hklt : k < u * (q + 1) := by
    simpa only [u, q, projectionScale] using Nat.lt_mul_div_succ k hu
  have hsucc : q + 1 ≤ 2 * q := by omega
  calc
    k ≤ u * (q + 1) := Nat.le_of_lt hklt
    _ ≤ u * (2 * q) := Nat.mul_le_mul_left u hsucc
    _ = projectionFactor D * projectionScale D k := by
      simp only [u, q, projectionFactor, Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm]

/-- The terminal outer Mahler box at the selected scale fits inside the
common injectivity-test radius in every surviving rank. -/
theorem outerDilationBound_le_projectionTestRadius
    {n D k : ℕ} (hn : n ≤ D) :
    outerDilationBound n (projectionScale D k) ≤
      (projectionTestRadius D k : ℝ) := by
  unfold outerDilationBound projectionTestRadius
  have hcost := outer_unit_cost_le_uniformOuterCost hn
  have hs : (0 : ℝ) ≤ projectionScale D k := by positivity
  calc
    (projectionScale D k : ℝ) * (n : ℝ) ^ 2 *
          (outerConstant n + 1) =
        (projectionScale D k : ℝ) *
          ((n : ℝ) ^ 2 * (outerConstant n + 1)) := by ring
    _ ≤ (projectionScale D k : ℝ) * uniformOuterCost D :=
      mul_le_mul_of_nonneg_left hcost hs
    _ = (uniformOuterCost D * projectionScale D k : ℕ) := by
      push_cast
      ring

/-- The terminal outer-body cost plus at most `D` rank-drop costs fits in
the original source dilation. -/
theorem succ_mul_projectionTestRadius_le_source
    {D k drops : ℕ} (hdrops : drops ≤ D) :
    (drops + 1) * projectionTestRadius D k ≤ k := by
  have hcount : drops + 1 ≤ D + 1 := by omega
  calc
    (drops + 1) * projectionTestRadius D k ≤
        (D + 1) * projectionTestRadius D k :=
      Nat.mul_le_mul_right _ hcount
    _ = projectionUnit D * projectionScale D k := by
      simp only [projectionTestRadius, projectionUnit, Nat.mul_assoc,
        Nat.mul_left_comm, Nat.mul_comm]
    _ ≤ k := by
      simpa only [projectionScale] using
        Nat.mul_div_le k (projectionUnit D)

end

end Erdos186.CFP.ProjectedProperization

#print axioms Erdos186.CFP.ProjectedProperization.outer_unit_cost_le_uniformOuterCost
#print axioms Erdos186.CFP.ProjectedProperization.source_le_projectionFactor_mul_scale
#print axioms Erdos186.CFP.ProjectedProperization.succ_mul_projectionTestRadius_le_source
