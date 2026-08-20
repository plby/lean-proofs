/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Finite separated selections

This file records the elementary packing argument used to replace a finite
family of zero ordinates by a separated subfamily which still covers every
ordinate.  The statement is given directly in real-distance language so its
consumers do not need to manipulate `ENNReal` coercions.
-/

namespace Erdos48

open Set Metric
open scoped NNReal ENNReal

noncomputable section

/-- Every finite set in a metric space has a finite maximal separated subset,
and maximality makes that subset a cover. -/
theorem exists_finite_separated_cover
    {X : Type*} [PseudoMetricSpace X] (A : Set X) (hA : A.Finite)
    (r : ℝ) (hr : 0 ≤ r) :
    ∃ S : Set X,
      S ⊆ A ∧ S.Finite ∧
        (∀ x ∈ S, ∀ y ∈ S, x ≠ y → r < dist x y) ∧
        ∀ x ∈ A, ∃ y ∈ S, dist x y ≤ r := by
  let eps : ℝ≥0 := ⟨r, hr⟩
  have hpack : Metric.packingNumber eps A ≠ ⊤ := by
    intro htop
    have hle := Metric.packingNumber_le_encard_self (ε := eps) A
    rw [htop] at hle
    have hencard : A.encard = ⊤ := top_unique hle
    exact (Set.encard_ne_top_iff.mpr hA) hencard
  let S : Set X := Metric.maximalSeparatedSet eps A
  have hSsub : S ⊆ A := Metric.maximalSeparatedSet_subset
  have hSfinite : S.Finite := by
    rw [← Set.encard_ne_top_iff]
    rw [Metric.encard_maximalSeparatedSet hpack]
    exact hpack
  have hsep := Metric.isSeparated_maximalSeparatedSet (ε := eps) (A := A)
  have hcover := Metric.isCover_maximalSeparatedSet (ε := eps) (A := A) hpack
  refine ⟨S, hSsub, hSfinite, ?_, ?_⟩
  · intro x hx y hy hxy
    have hed := hsep hx hy hxy
    change (eps : ℝ≥0∞) < edist x y at hed
    rw [edist_dist] at hed
    rw [ENNReal.coe_nnreal_eq] at hed
    change ENNReal.ofReal r < ENNReal.ofReal (dist x y) at hed
    exact (ENNReal.ofReal_lt_ofReal_iff').mp hed |>.1
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hcover hx
    refine ⟨y, hy, ?_⟩
    change edist x y ≤ (eps : ℝ≥0∞) at hxy
    rw [edist_dist] at hxy
    rw [ENNReal.coe_nnreal_eq] at hxy
    change ENNReal.ofReal (dist x y) ≤ ENNReal.ofReal r at hxy
    exact (ENNReal.ofReal_le_ofReal_iff hr).mp hxy

/-- Forward intervals of a common radius based at sufficiently separated
real points are pairwise disjoint. -/
theorem pairwiseDisjoint_Ioc_add_of_separated
    {S : Set ℝ} {r : ℝ}
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 2 * r < dist x y) :
    Set.PairwiseDisjoint S (fun x ↦ Set.Ioc x (x + r)) := by
  intro x hx y hy hxy
  change Disjoint (Set.Ioc x (x + r)) (Set.Ioc y (y + r))
  rw [Set.disjoint_left]
  intro z hzx hzy
  have hxyDist := hsep x hx y hy hxy
  rw [Real.dist_eq] at hxyDist
  rcases hzx with ⟨hxz, hzx⟩
  rcases hzy with ⟨hyz, hzy⟩
  by_cases hxyLe : x ≤ y
  · have : |x - y| ≤ r := by
      rw [abs_of_nonpos (sub_nonpos.mpr hxyLe)]
      linarith
    linarith
  · have hyxLe : y ≤ x := le_of_not_ge hxyLe
    have : |x - y| ≤ r := by
      rw [abs_of_nonneg (sub_nonneg.mpr hyxLe)]
      linarith
    linarith

end

end Erdos48
