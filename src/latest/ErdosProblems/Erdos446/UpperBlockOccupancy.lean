/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperClusterMass
import ErdosProblems.Erdos446.BlockPartition
import ErdosProblems.Erdos446.SmirnovOccupancy

/-!
# Erdős Problem 446: block cluster masses and Smirnov occupancies

This file is the discrete bridge from the prime-block decomposition to the
Smirnov estimate.  A block-count vector has reciprocal mass at most a product
of elementary prime masses.  When every block mass is bounded by `B`, this is
at most `B^k / ∏ bᵢ!`.  Consequently any uniform cluster-length envelope on a
Smirnov family sums to the corresponding Smirnov occupancy mass.

This route avoids introducing continuous ordered simplices: the same
reciprocal-factorial weights already occur exactly in the finite prime-block
partition.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- Reciprocal cluster mass of one block-count family. -/
noncomputable def compositionBlockClusterMass (M : ℕ) {K : ℕ}
    (b : Fin K → ℕ) : ℝ :=
  ∑ a ∈ compositionBlockFamily M b, clusterLength a / (a : ℝ)

theorem compositionBlockClusterMass_nonneg (M : ℕ) {K : ℕ}
    (b : Fin K → ℕ) :
    0 ≤ compositionBlockClusterMass M b := by
  apply Finset.sum_nonneg
  intro a ha
  exact div_nonneg (clusterLength_nonneg a) (Nat.cast_nonneg a)

/-- Uniformly bounding the reciprocal mass of every prime block turns the
product of elementary masses into one reciprocal-factorial weight. -/
theorem compositionBlockFamily_reciprocal_sum_upper_uniform
    {M K : ℕ} {b : Fin K → ℕ} {B : ℝ} (_hB : 0 ≤ B)
    (hmass : ∀ i : Fin K, primeBlockMass (M + i) ≤ B) :
    (∑ a ∈ compositionBlockFamily M b, 1 / (a : ℝ)) ≤
      B ^ (∑ i : Fin K, b i) / compositionFactorial b := by
  have hbase := blockFamily_reciprocal_sum_upper M K (extendComposition b)
  calc
    (∑ a ∈ compositionBlockFamily M b, 1 / (a : ℝ)) ≤
        ∏ i : Fin K,
          primeBlockMass (M + i) ^ b i /
            ((b i).factorial : ℝ) := by
      simpa only [compositionBlockFamily, extendComposition_fin] using hbase
    _ ≤ ∏ i : Fin K, B ^ b i / ((b i).factorial : ℝ) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact div_nonneg
          (pow_nonneg (primeBlockMass_nonneg _) _)
          (by positivity)
      · intro i hi
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact pow_le_pow_left₀ (primeBlockMass_nonneg _) (hmass i) _
    _ = B ^ (∑ i : Fin K, b i) / compositionFactorial b := by
      rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
      rfl

/-- A pointwise cluster envelope and a reciprocal-family estimate combine
without any loss. -/
theorem compositionBlockClusterMass_le_of_envelope
    {M K : ℕ} {b : Fin K → ℕ} {C R : ℝ}
    (hC : 0 ≤ C)
    (henvelope : ∀ a ∈ compositionBlockFamily M b, clusterLength a ≤ C)
    (hreciprocal :
      (∑ a ∈ compositionBlockFamily M b, 1 / (a : ℝ)) ≤ R) :
    compositionBlockClusterMass M b ≤ C * R := by
  calc
    compositionBlockClusterMass M b ≤
        ∑ a ∈ compositionBlockFamily M b, C * (1 / (a : ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      have haPos : (0 : ℝ) < a := by
        exact_mod_cast blockFamily_pos ha
      rw [div_eq_mul_inv, one_div]
      exact mul_le_mul_of_nonneg_right (henvelope a ha)
        (inv_nonneg.mpr haPos.le)
    _ = C * (∑ a ∈ compositionBlockFamily M b, 1 / (a : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ C * R := mul_le_mul_of_nonneg_left hreciprocal hC

/-- Exact prime-block product form.  No common upper bound on the block
masses is introduced, so the sharp base `log 2` can be recovered using the
geometrically decaying block-mass errors. -/
theorem compositionBlockClusterMass_le_product
    {M K : ℕ} {b : Fin K → ℕ} {C : ℝ}
    (hC : 0 ≤ C)
    (henvelope : ∀ a ∈ compositionBlockFamily M b, clusterLength a ≤ C) :
    compositionBlockClusterMass M b ≤
      C * ∏ i : Fin K,
        primeBlockMass (M + i) ^ b i /
          ((b i).factorial : ℝ) := by
  exact compositionBlockClusterMass_le_of_envelope hC henvelope
    (by simpa only [compositionBlockFamily, extendComposition_fin] using
      blockFamily_reciprocal_sum_upper M K (extendComposition b))

/-- One block-count family, in the form directly used before summing over a
Smirnov barrier event. -/
theorem compositionBlockClusterMass_le_uniform
    {M K : ℕ} {b : Fin K → ℕ} {B C : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hmass : ∀ i : Fin K, primeBlockMass (M + i) ≤ B)
    (henvelope : ∀ a ∈ compositionBlockFamily M b, clusterLength a ≤ C) :
    compositionBlockClusterMass M b ≤
      C * (B ^ (∑ i : Fin K, b i) / compositionFactorial b) := by
  exact compositionBlockClusterMass_le_of_envelope hC henvelope
    (compositionBlockFamily_reciprocal_sum_upper_uniform hB hmass)

/-- Total cluster mass over all block vectors satisfying the Smirnov barrier. -/
noncomputable def smirnovBlockClusterMass (M k u v : ℕ) : ℝ :=
  ∑ b ∈ smirnovOccupancies k u v, compositionBlockClusterMass M b

/-- Cluster mass over an arbitrary finite collection of block-count vectors.
Dyadic layers of the sharp envelope use this form. -/
noncomputable def blockClusterMassOver {v : ℕ} (M : ℕ)
    (I : Finset (Fin v → ℕ)) : ℝ :=
  ∑ b ∈ I, compositionBlockClusterMass M b

theorem smirnovBlockClusterMass_nonneg (M k u v : ℕ) :
    0 ≤ smirnovBlockClusterMass M k u v := by
  apply Finset.sum_nonneg
  intro b hb
  exact compositionBlockClusterMass_nonneg M b

theorem blockClusterMassOver_nonneg {v : ℕ} (M : ℕ)
    (I : Finset (Fin v → ℕ)) :
    0 ≤ blockClusterMassOver M I := by
  apply Finset.sum_nonneg
  intro b hb
  exact compositionBlockClusterMass_nonneg M b

/-- Summing a uniform cluster envelope over the barrier event produces
exactly the Smirnov reciprocal-factorial mass. -/
theorem smirnovBlockClusterMass_le_occupancyMass
    {M k u v : ℕ} {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hmass : ∀ i : Fin v, primeBlockMass (M + i) ≤ B)
    (henvelope : ∀ b ∈ smirnovOccupancies k u v,
      ∀ a ∈ compositionBlockFamily M b, clusterLength a ≤ C) :
    smirnovBlockClusterMass M k u v ≤
      C * B ^ k * smirnovOccupancyMass k u v := by
  calc
    smirnovBlockClusterMass M k u v ≤
        ∑ b ∈ smirnovOccupancies k u v,
          C * (B ^ k / compositionFactorial b) := by
      apply Finset.sum_le_sum
      intro b hb
      have hsum : ∑ i : Fin v, b i = k := (mem_smirnovOccupancies.mp hb).1
      simpa only [hsum] using
        compositionBlockClusterMass_le_uniform hB hC hmass
          (henvelope b hb)
    _ = C * B ^ k * smirnovOccupancyMass k u v := by
      rw [smirnovOccupancyMass]
      simp_rw [div_eq_mul_inv]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring

/-- Algebraic removal of the probability normalization. -/
theorem smirnovOccupancyMass_eq_probability_mul
    {k u v : ℕ} (hv : 0 < v) :
    smirnovOccupancyMass k u v =
      smirnovProbability k u v * (v : ℝ) ^ k /
        (k.factorial : ℝ) := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hpow : (0 : ℝ) < (v : ℝ) ^ k := pow_pos hvR k
  have hfac : (0 : ℝ) < k.factorial := by positivity
  dsimp [smirnovProbability]
  field_simp [hpow.ne', hfac.ne']

/-- The preceding bridge with the Smirnov probability exposed.  A
quantitative probability lemma can be substituted directly on the right. -/
theorem smirnovBlockClusterMass_le_probability
    {M k u v : ℕ} {B C : ℝ} (hv : 0 < v)
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hmass : ∀ i : Fin v, primeBlockMass (M + i) ≤ B)
    (henvelope : ∀ b ∈ smirnovOccupancies k u v,
      ∀ a ∈ compositionBlockFamily M b, clusterLength a ≤ C) :
    smirnovBlockClusterMass M k u v ≤
      C * B ^ k *
        (smirnovProbability k u v * (v : ℝ) ^ k /
          (k.factorial : ℝ)) := by
  rw [← smirnovOccupancyMass_eq_probability_mul hv]
  exact smirnovBlockClusterMass_le_occupancyMass hB hC hmass henvelope

/-- Plug-in interface for any quantitative Smirnov probability estimate. -/
theorem smirnovBlockClusterMass_le_of_probability_bound
    {M k u v : ℕ} {B C Q : ℝ} (hv : 0 < v)
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hmass : ∀ i : Fin v, primeBlockMass (M + i) ≤ B)
    (henvelope : ∀ b ∈ smirnovOccupancies k u v,
      ∀ a ∈ compositionBlockFamily M b, clusterLength a ≤ C)
    (hprob : smirnovProbability k u v ≤ Q) :
    smirnovBlockClusterMass M k u v ≤
      C * B ^ k * (Q * (v : ℝ) ^ k / (k.factorial : ℝ)) := by
  have hvpow : 0 ≤ (v : ℝ) ^ k := by positivity
  have hfac : (0 : ℝ) < k.factorial := by positivity
  calc
    smirnovBlockClusterMass M k u v ≤
        C * B ^ k *
          (smirnovProbability k u v * (v : ℝ) ^ k /
            (k.factorial : ℝ)) :=
      smirnovBlockClusterMass_le_probability hv hB hC hmass henvelope
    _ ≤ C * B ^ k *
        (Q * (v : ℝ) ^ k / (k.factorial : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (pow_nonneg hB k))
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hprob hvpow) hfac.le

/-- Dyadic-layer interface: if every vector in a finite layer satisfies one
Smirnov barrier and has cluster envelope at most `C`, its full arithmetic
mass is controlled by the probability of that barrier. -/
theorem blockClusterMassOver_le_of_probability_bound
    {M k u v : ℕ} {I : Finset (Fin v → ℕ)} {B C Q : ℝ}
    (hv : 0 < v) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hI : I ⊆ smirnovOccupancies k u v)
    (hmass : ∀ i : Fin v, primeBlockMass (M + i) ≤ B)
    (henvelope : ∀ b ∈ I,
      ∀ a ∈ compositionBlockFamily M b, clusterLength a ≤ C)
    (hprob : smirnovProbability k u v ≤ Q) :
    blockClusterMassOver M I ≤
      C * B ^ k * (Q * (v : ℝ) ^ k / (k.factorial : ℝ)) := by
  have hfac : (0 : ℝ) < k.factorial := by positivity
  have hsubsetMass :
      (∑ b ∈ I, 1 / compositionFactorial b) ≤
        smirnovOccupancyMass k u v := by
    rw [smirnovOccupancyMass]
    exact Finset.sum_le_sum_of_subset_of_nonneg hI
      (fun b hb hnot ↦ by
        have hcf : 0 < compositionFactorial b := by
          dsimp [compositionFactorial]
          positivity
        exact (one_div_pos.mpr hcf).le)
  have hlayer : blockClusterMassOver M I ≤
      C * B ^ k * (∑ b ∈ I, 1 / compositionFactorial b) := by
    calc
      blockClusterMassOver M I ≤
          ∑ b ∈ I, C * (B ^ k / compositionFactorial b) := by
        apply Finset.sum_le_sum
        intro b hb
        have hsum : ∑ i : Fin v, b i = k :=
          (mem_smirnovOccupancies.mp (hI hb)).1
        simpa only [hsum] using
          compositionBlockClusterMass_le_uniform hB hC hmass
            (henvelope b hb)
      _ = C * B ^ k * (∑ b ∈ I, 1 / compositionFactorial b) := by
        simp_rw [div_eq_mul_inv]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        ring
  calc
    blockClusterMassOver M I ≤
        C * B ^ k * smirnovOccupancyMass k u v :=
      hlayer.trans (mul_le_mul_of_nonneg_left hsubsetMass
        (mul_nonneg hC (pow_nonneg hB k)))
    _ = C * B ^ k *
        (smirnovProbability k u v * (v : ℝ) ^ k /
          (k.factorial : ℝ)) := by
      rw [smirnovOccupancyMass_eq_probability_mul hv]
    _ ≤ C * B ^ k *
        (Q * (v : ℝ) ^ k / (k.factorial : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (pow_nonneg hB k))
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hprob (by positivity)) hfac.le

end Erdos446
