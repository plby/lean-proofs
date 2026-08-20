/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.ClusterUpper
import Mathlib.MeasureTheory.Group.Measure

/-!
# Erdős Problem 446: the sharp cluster product inequality

Translation invariance of Lebesgue measure gives the sharp elementary
inequality

`L(a * b) ≤ τ(b) L(a)`.

Indeed, factor every divisor of `a * b` as a divisor of `a` times a divisor
of `b`.  For each fixed divisor of `b`, all resulting logarithmic intervals
form one translate of the divisor cluster of `a`.
-/

namespace Erdos446

open Finset Set MeasureTheory Real
open scoped BigOperators Pointwise

/-- The translate of the divisor cluster of `a` by `log d`, expressed as a
preimage so that translation invariance of volume applies directly. -/
private def translatedDivisorCluster (a d : ℕ) : Set ℝ :=
  (fun u ↦ -Real.log (d : ℝ) + u) ⁻¹' divisorCluster a

private theorem measurableSet_translatedDivisorCluster (a d : ℕ) :
    MeasurableSet (translatedDivisorCluster a d) := by
  exact (measurable_const.add measurable_id)
    (measurableSet_divisorCluster a)

private theorem volume_translatedDivisorCluster (a d : ℕ) :
    volume (translatedDivisorCluster a d) = volume (divisorCluster a) := by
  exact measure_preimage_add volume (-Real.log (d : ℝ)) (divisorCluster a)

private theorem divisorCluster_mul_subset_translatedClusters {a b : ℕ}
    (_ha : 0 < a) (_hb : 0 < b) :
    divisorCluster (a * b) ⊆
      ⋃ d ∈ b.divisors, translatedDivisorCluster a d := by
  intro u hu
  obtain ⟨d, hd, hlow, hupp⟩ :=
    (mem_divisorCluster_iff (a * b) u).mp hu
  rw [Nat.divisors_mul] at hd
  obtain ⟨da, hda, db, hdb, rfl⟩ := Finset.mem_mul.mp hd
  have hdaPos : 0 < da := Nat.pos_of_mem_divisors hda
  have hdbPos : 0 < db := Nat.pos_of_mem_divisors hdb
  have hlogMul : Real.log ((da * db : ℕ) : ℝ) =
      Real.log (da : ℝ) + Real.log (db : ℝ) := by
    push_cast
    rw [Real.log_mul (by exact_mod_cast hdaPos.ne')
      (by exact_mod_cast hdbPos.ne')]
  rw [hlogMul] at hlow hupp
  rw [Set.mem_iUnion]
  refine ⟨db, Set.mem_iUnion.mpr ⟨hdb, ?_⟩⟩
  rw [translatedDivisorCluster, Set.mem_preimage,
    mem_divisorCluster_iff]
  refine ⟨da, hda, ?_, ?_⟩ <;> linarith

/-- Ford's sharp multiplicative cluster inequality: multiplying by `b`
costs at most one translate of the old cluster for every divisor of `b`. -/
theorem clusterLength_mul_le_card_divisors_mul_clusterLength {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) :
    clusterLength (a * b) ≤
      (b.divisors.card : ℝ) * clusterLength a := by
  calc
    clusterLength (a * b) ≤
        volume.real (⋃ d ∈ b.divisors, translatedDivisorCluster a d) := by
      exact MeasureTheory.measureReal_mono
        (divisorCluster_mul_subset_translatedClusters ha hb)
        (by
          apply ne_of_lt
          refine lt_of_le_of_lt
            (measure_biUnion_finset_le ( μ := volume) b.divisors
              (translatedDivisorCluster a)) ?_
          exact ENNReal.sum_lt_top.mpr fun d _ ↦ by
            rw [volume_translatedDivisorCluster]
            exact volume_divisorCluster_lt_top a)
    _ ≤ ∑ d ∈ b.divisors,
        volume.real (translatedDivisorCluster a d) := by
      exact MeasureTheory.measureReal_biUnion_finset_le
        (μ := volume) b.divisors (translatedDivisorCluster a)
    _ = ∑ _d ∈ b.divisors, clusterLength a := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Measure.real, volume_translatedDivisorCluster]
      rfl
    _ = (b.divisors.card : ℝ) * clusterLength a := by
      simp

/-- Multiplication by a prime at most doubles divisor-cluster length. -/
theorem clusterLength_prime_mul_le_two_mul {p a : ℕ}
    (hp : p.Prime) (ha : 0 < a) :
    clusterLength (p * a) ≤ 2 * clusterLength a := by
  have hcard : p.divisors.card = 2 := by
    rw [hp.divisors]
    simp [hp.ne_one.symm]
  rw [mul_comm]
  simpa [hcard] using
    (clusterLength_mul_le_card_divisors_mul_clusterLength ha hp.pos)

end Erdos446
