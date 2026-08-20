/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.LowerBound
import Mathlib.Data.Finset.NatDivisors

/-!
# Erdős Problem 446: elementary upper bounds for divisor clusters

These are the three elementary properties of Ford's cluster length used in
the upper bound.  The key product estimate covers the cluster of `a*b` by
one translated interval for every divisor of `b`.
-/

namespace Erdos446

open Finset Set MeasureTheory Real
open scoped BigOperators Pointwise

theorem divisorCluster_subset_globalInterval {a : ℕ} (ha : 0 < a) :
    divisorCluster a ⊆
      Set.Ico (-Real.log 2) (Real.log (a : ℝ)) := by
  intro u hu
  obtain ⟨d, hd, hlow, hupp⟩ := (mem_divisorCluster_iff a u).mp hu
  have hdPos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hdPos
  have hda : d ≤ a := Nat.le_of_dvd ha (Nat.dvd_of_mem_divisors hd)
  constructor
  · have : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hdOne
    linarith
  · exact hupp.trans_le (Real.log_le_log (by exact_mod_cast hdPos)
      (by exact_mod_cast hda))

theorem clusterLength_le_log_add_log_two {a : ℕ} (ha : 0 < a) :
    clusterLength a ≤ Real.log (a : ℝ) + Real.log 2 := by
  have hlog : 0 ≤ Real.log (a : ℝ) :=
    Real.log_nonneg (by exact_mod_cast ha)
  calc
    clusterLength a ≤
        volume.real (Set.Ico (-Real.log 2) (Real.log (a : ℝ))) :=
      MeasureTheory.measureReal_mono (divisorCluster_subset_globalInterval ha)
        (measure_Ico_lt_top.ne)
    _ = Real.log (a : ℝ) + Real.log 2 := by
      rw [Real.volume_real_Ico_of_le]
      · ring
      · linarith [Real.log_nonneg one_le_two]

private def divisorTranslateEnvelope (a d : ℕ) : Set ℝ :=
  Set.Ico (Real.log (d : ℝ) - Real.log 2)
    (Real.log (d : ℝ) + Real.log (a : ℝ))

private theorem divisorCluster_mul_subset_envelopes {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) :
    divisorCluster (a * b) ⊆
      ⋃ d ∈ b.divisors, divisorTranslateEnvelope a d := by
  intro u hu
  obtain ⟨d, hd, hlow, hupp⟩ :=
    (mem_divisorCluster_iff (a * b) u).mp hu
  rw [Nat.divisors_mul] at hd
  obtain ⟨da, hda, db, hdb, rfl⟩ := Finset.mem_mul.mp hd
  have hdaPos : 0 < da := Nat.pos_of_mem_divisors hda
  have hdbPos : 0 < db := Nat.pos_of_mem_divisors hdb
  have hdaLe : da ≤ a := Nat.le_of_dvd ha (Nat.dvd_of_mem_divisors hda)
  have hlogDa : 0 ≤ Real.log (da : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hdaPos)
  rw [Set.mem_iUnion]
  refine ⟨db, Set.mem_iUnion.mpr ⟨hdb, ?_⟩⟩
  rw [divisorTranslateEnvelope, Set.mem_Ico]
  have hlogMul : Real.log ((da * db : ℕ) : ℝ) =
      Real.log (da : ℝ) + Real.log (db : ℝ) := by
    push_cast
    rw [Real.log_mul (by exact_mod_cast hdaPos.ne')
      (by exact_mod_cast hdbPos.ne')]
  rw [hlogMul] at hlow hupp
  constructor
  · linarith
  · have hdaPosR : (0 : ℝ) < da := by exact_mod_cast hdaPos
    have hdaLeR : (da : ℝ) ≤ a := by exact_mod_cast hdaLe
    have hlogLe := Real.log_le_log hdaPosR hdaLeR
    linarith

private theorem volume_real_divisorTranslateEnvelope {a d : ℕ}
    (ha : 0 < a) (hd : 0 < d) :
    volume.real (divisorTranslateEnvelope a d) =
      Real.log (a : ℝ) + Real.log 2 := by
  rw [divisorTranslateEnvelope, Real.volume_real_Ico_of_le]
  · ring
  · have hlogA : 0 ≤ Real.log (a : ℝ) :=
      Real.log_nonneg (by exact_mod_cast ha)
    linarith [Real.log_nonneg one_le_two]

theorem clusterLength_mul_le_card_divisors_mul {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) :
    clusterLength (a * b) ≤
      (b.divisors.card : ℝ) *
        (Real.log (a : ℝ) + Real.log 2) := by
  have hUnionTop : volume (⋃ d ∈ b.divisors,
      divisorTranslateEnvelope a d) ≠ ⊤ := by
    apply ne_of_lt
    refine lt_of_le_of_lt
      (measure_biUnion_finset_le (μ := volume) b.divisors
        (divisorTranslateEnvelope a)) ?_
    exact ENNReal.sum_lt_top.mpr fun d hd ↦ measure_Ico_lt_top
  calc
    clusterLength (a * b) ≤
        volume.real (⋃ d ∈ b.divisors, divisorTranslateEnvelope a d) :=
      MeasureTheory.measureReal_mono (divisorCluster_mul_subset_envelopes ha hb)
        hUnionTop
    _ ≤ ∑ d ∈ b.divisors, volume.real (divisorTranslateEnvelope a d) := by
      exact MeasureTheory.measureReal_biUnion_finset_le
        (μ := volume) b.divisors (divisorTranslateEnvelope a)
    _ = ∑ d ∈ b.divisors,
        (Real.log (a : ℝ) + Real.log 2) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [volume_real_divisorTranslateEnvelope ha
        (Nat.pos_of_mem_divisors hd)]
    _ = (b.divisors.card : ℝ) *
        (Real.log (a : ℝ) + Real.log 2) := by
      simp
      ring

/-! ## Ford's prefix/tail estimate for a squarefree integer -/

theorem clusterLength_squarefree_prefix {a : ℕ} (ha : Squarefree a)
    {J : Finset ℕ} (hJ : J ⊆ a.primeFactors) :
    clusterLength a ≤
      (2 : ℝ) ^ (a.primeFactors \ J).card *
        (Real.log ((∏ p ∈ J, p : ℕ) : ℝ) + Real.log 2) := by
  let b := ∏ p ∈ J, p
  let c := ∏ p ∈ a.primeFactors \ J, p
  have hb : 0 < b := by
    dsimp [b]
    apply Finset.prod_pos
    intro p hp
    exact (Nat.prime_of_mem_primeFactors (hJ hp)).pos
  have hc : 0 < c := by
    dsimp [c]
    apply Finset.prod_pos
    intro p hp
    exact (Nat.prime_of_mem_primeFactors
      (Finset.mem_sdiff.mp hp).1).pos
  have hbc : b * c = a := by
    rw [mul_comm]
    calc
      c * b = ∏ p ∈ a.primeFactors, p := by
        simpa [b, c] using (Finset.prod_sdiff hJ :
          (∏ p ∈ a.primeFactors \ J, p) *
            (∏ p ∈ J, p) = ∏ p ∈ a.primeFactors, p)
      _ = a := Nat.prod_primeFactors_of_squarefree ha
  have hcSq : Squarefree c := by
    dsimp [c]
    refine Finset.squarefree_prod_of_pairwise_isCoprime ?_
      (fun p hp ↦ (Nat.prime_of_mem_primeFactors
        (Finset.mem_sdiff.mp hp).1).squarefree)
    intro p hp q hq hpq
    simp only [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes
      (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1)
      (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq).1)).mpr hpq
  have hpf : c.primeFactors = a.primeFactors \ J := by
    dsimp [c]
    exact Nat.primeFactors_prod fun p hp ↦
      Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1
  calc
    clusterLength a = clusterLength (b * c) := by rw [hbc]
    _ ≤ (c.divisors.card : ℝ) *
        (Real.log (b : ℝ) + Real.log 2) :=
      clusterLength_mul_le_card_divisors_mul hb hc
    _ = (2 : ℝ) ^ (a.primeFactors \ J).card *
        (Real.log ((∏ p ∈ J, p : ℕ) : ℝ) + Real.log 2) := by
      rw [card_divisors_eq_two_pow_primeFactors_card hc hcSq, hpf]
      push_cast
      simp [b]

/-- Ford's elementary minimum estimate: every chosen prefix of the prime
support supplies one admissible cluster-length envelope. -/
theorem clusterLength_squarefree_le_prefixInf {a : ℕ} (ha : Squarefree a) :
    clusterLength a ≤
      (a.primeFactors.powerset.image fun J ↦
        (2 : ℝ) ^ (a.primeFactors \ J).card *
          (Real.log ((∏ p ∈ J, p : ℕ) : ℝ) + Real.log 2)).min' (by
            exact Finset.image_nonempty.mpr
              (Finset.powerset_nonempty a.primeFactors)) := by
  apply Finset.le_min'
  intro x hx
  obtain ⟨J, hJpow, rfl⟩ := Finset.mem_image.mp hx
  exact clusterLength_squarefree_prefix ha (Finset.mem_powerset.mp hJpow)

end Erdos446
