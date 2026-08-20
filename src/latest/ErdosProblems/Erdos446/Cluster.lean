/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.Counting
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Erdős Problem 446: logarithmic divisor clusters

The central finite object in Ford's proof is the union of logarithmic
intervals contributed by the divisors of an integer.  This module introduces
that union and its Lebesgue length, together with the elementary covering
facts used by both sides of the dyadic estimate.
-/

namespace Erdos446

open Finset Set MeasureTheory Real
open scoped BigOperators ENNReal NNReal Topology

/-- The logarithmic interval of length `log 2` attached to a positive
integer `d`. -/
def divisorLogInterval (d : ℕ) : Set ℝ :=
  Set.Ico (Real.log (d : ℝ) - Real.log 2) (Real.log (d : ℝ))

/-- Ford's union `ℒ(a)` of logarithmic divisor intervals. -/
def divisorCluster (a : ℕ) : Set ℝ :=
  ⋃ d ∈ a.divisors, divisorLogInterval d

/-- Lebesgue length `L(a)` of the logarithmic divisor cluster. -/
noncomputable def clusterLength (a : ℕ) : ℝ :=
  (volume (divisorCluster a)).toReal

/-- Ordered pairs of divisors whose quotient is within a factor two. -/
noncomputable def closeDivisorPairs (a : ℕ) : Finset (ℕ × ℕ) :=
  (a.divisors ×ˢ a.divisors).filter fun dd ↦
    |Real.log (dd.1 : ℝ) - Real.log (dd.2 : ℝ)| ≤ Real.log 2

/-- Ford's close-pair count `W(a)`. -/
noncomputable def closePairCount (a : ℕ) : ℕ :=
  (closeDivisorPairs a).card

theorem measurableSet_divisorLogInterval (d : ℕ) :
    MeasurableSet (divisorLogInterval d) :=
  measurableSet_Ico

theorem measurableSet_divisorCluster (a : ℕ) :
    MeasurableSet (divisorCluster a) := by
  unfold divisorCluster
  refine MeasurableSet.iUnion fun d ↦ ?_
  by_cases hd : d ∈ a.divisors
  · simpa [hd] using measurableSet_divisorLogInterval d
  · simp [hd]

theorem volume_divisorLogInterval (d : ℕ) :
    volume (divisorLogInterval d) = ENNReal.ofReal (Real.log 2) := by
  rw [divisorLogInterval, Real.volume_Ico]
  congr 1
  ring

theorem clusterLength_nonneg (a : ℕ) : 0 ≤ clusterLength a := by
  exact ENNReal.toReal_nonneg

theorem volume_divisorCluster_lt_top (a : ℕ) :
    volume (divisorCluster a) < ∞ := by
  have hle : volume (divisorCluster a) ≤
      ∑ d ∈ a.divisors, volume (divisorLogInterval d) := by
    simpa only [divisorCluster] using
      (measure_biUnion_finset_le (μ := volume) a.divisors divisorLogInterval)
  refine lt_of_le_of_lt hle ?_
  simp only [volume_divisorLogInterval]
  exact ENNReal.sum_lt_top.mpr fun _ _ ↦ ENNReal.ofReal_lt_top

/-- The union has length at most the sum of its interval lengths. -/
theorem clusterLength_le_card_divisors_mul_log_two (a : ℕ) :
    clusterLength a ≤ (a.divisors.card : ℝ) * Real.log 2 := by
  have hreal := MeasureTheory.measureReal_biUnion_finset_le
    (μ := volume) a.divisors divisorLogInterval
  simpa only [clusterLength, divisorCluster, Measure.real,
    volume_divisorLogInterval,
    ENNReal.toReal_ofReal (Real.log_nonneg one_le_two), Finset.sum_const,
    nsmul_eq_mul] using hreal

theorem mem_divisorCluster_of_dvd {a d : ℕ} (ha : a ≠ 0) (hd : d ∣ a)
    {u : ℝ} (hu : u ∈ divisorLogInterval d) :
    u ∈ divisorCluster a := by
  rw [divisorCluster, Set.mem_iUnion]
  refine ⟨d, ?_⟩
  rw [Set.mem_iUnion]
  exact ⟨Nat.mem_divisors.mpr ⟨hd, ha⟩, hu⟩

theorem divisorLogInterval_subset_cluster {a d : ℕ} (hd : d ∈ a.divisors) :
    divisorLogInterval d ⊆ divisorCluster a := by
  intro u hu
  rw [divisorCluster, Set.mem_iUnion]
  exact ⟨d, Set.mem_iUnion.mpr ⟨hd, hu⟩⟩

/-- Every positive integer contributes its diagonal divisor pairs. -/
theorem card_divisors_le_closePairCount (a : ℕ) :
    a.divisors.card ≤ closePairCount a := by
  let diag : ℕ → ℕ × ℕ := fun d ↦ (d, d)
  have hinj : Function.Injective diag := by
    intro d e h
    exact congrArg Prod.fst h
  have hsub : a.divisors.image diag ⊆ closeDivisorPairs a := by
    intro dd hdd
    rcases Finset.mem_image.mp hdd with ⟨d, hd, rfl⟩
    rw [closeDivisorPairs, Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨hd, hd⟩, ?_⟩
    change |Real.log (d : ℝ) - Real.log (d : ℝ)| ≤ Real.log 2
    simpa using Real.log_nonneg one_le_two
  calc
    a.divisors.card = (a.divisors.image diag).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (closeDivisorPairs a).card := Finset.card_le_card hsub
    _ = closePairCount a := rfl

/-- Membership in a cluster supplies an actual divisor whose logarithm is
within one `log 2` interval. -/
theorem mem_divisorCluster_iff (a : ℕ) (u : ℝ) :
    u ∈ divisorCluster a ↔
      ∃ d ∈ a.divisors,
        Real.log (d : ℝ) - Real.log 2 ≤ u ∧ u < Real.log (d : ℝ) := by
  simp only [divisorCluster, divisorLogInterval, Set.mem_iUnion, Set.mem_Ico]
  constructor
  · rintro ⟨d, hd, hlow, hupp⟩
    exact ⟨d, hd, hlow, hupp⟩
  · rintro ⟨d, hd, hlow, hupp⟩
    exact ⟨d, hd, hlow, hupp⟩

end Erdos446
