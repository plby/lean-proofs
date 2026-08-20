/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperBlockOccupancy
import ErdosProblems.Erdos446.BlockCloseBounds
import ErdosProblems.Erdos446.UpperFiniteLayers

/-!
# Erdős Problem 446: sharp nonuniform prime-block masses in the upper bound

The reciprocal mass of the `i`th block is not replaced by a fixed number
larger than `log 2`.  Such a replacement would introduce a factor
`(1 + c)^k` and would change Ford's exponent.  Instead, the Smirnov prefix
barrier caps the number of repeated prime slots in the early blocks, while
the Mertens errors decay geometrically.  The sum of all relative errors is
therefore bounded by

`4 * (u + 1) * C / (log 2 * 2^M)`.

Exponentiating this *sum* costs a single factor and retains the exact base
`(log 2)^k`.  The final theorems insert this estimate directly in the
block-family and occupancy sums used in Ford's equation (30).
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- Threshold form of the proved Mertens estimate.  In particular, after
one fixed initial block every later block satisfies the geometric error
bound with the same constant. -/
theorem exists_primeBlockMass_geometric_error_threshold :
    ∃ C : ℝ, 0 < C ∧ ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      |primeBlockMass j - Real.log 2| ≤ C / (2 : ℝ) ^ j := by
  obtain ⟨C, hC, hmass⟩ := exists_primeBlockMass_geometric_error
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp hmass
  exact ⟨C, hC, J, hJ⟩

/-- One coordinate is bounded by the prefix containing that coordinate. -/
theorem occupancyCoordinate_le_prefix_succ {v : ℕ} (b : Fin v → ℕ)
    (i : Fin v) : b i ≤ occupancyPrefix b (i.val + 1) := by
  rw [occupancyPrefix]
  exact Finset.single_le_sum (fun j _hj ↦ Nat.zero_le (b j))
    (by simp)

/-- A Smirnov barrier gives the linear coordinate cap which makes the
geometric Mertens errors summable. -/
theorem smirnovOccupancy_linear_cap {k u v : ℕ} {b : Fin v → ℕ}
    (hb : b ∈ smirnovOccupancies k u v) (i : Fin v) :
    extendComposition b i ≤ (u + 1) * (i.val + 1) := by
  rw [extendComposition_fin]
  have hpref := (mem_smirnovOccupancies.mp hb).2
    (i.val + 1) (by omega) (by omega)
  have hcoord := occupancyCoordinate_le_prefix_succ b i
  calc
    b i ≤ occupancyPrefix b (i.val + 1) := hcoord
    _ ≤ u + i.val := by omega
    _ ≤ (u + 1) * (i.val + 1) := by nlinarith

/-- The total repeated-slot Mertens error in a Smirnov occupancy is
geometrically summable. -/
theorem smirnovSlotGeometricError_sum_le
    {M k u v : ℕ} {b : Fin v → ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hb : b ∈ smirnovOccupancies k u v) :
    (∑ s : BlockSlot v (extendComposition b),
        C / (2 : ℝ) ^ (M + s.1.val)) ≤
      4 * (u + 1) * C / (2 : ℝ) ^ M := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (slot_geometric_error_sum_le
      (M := M) (k := v) (K := u + 1) (b := extendComposition b)
      hC (smirnovOccupancy_linear_cap hb))

/-- Product of the actual, nonuniform block masses over all repeated slots.
The exact main base is `log 2`; only one exponential error factor remains. -/
theorem smirnovSlotMassProduct_upper
    {M k u v : ℕ} {b : Fin v → ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hb : b ∈ smirnovOccupancies k u v)
    (hmass : ∀ i : Fin v,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val)) :
    (∏ s : BlockSlot v (extendComposition b),
        primeBlockMass (M + s.1)) ≤
      Real.log 2 ^ k *
        Real.exp (4 * (u + 1) * (C / Real.log 2) / (2 : ℝ) ^ M) := by
  let z : BlockSlot v (extendComposition b) → ℝ :=
    blockMassRelativeError C M b
  have hz0 : ∀ s, 0 ≤ z s :=
    fun s ↦ blockMassRelativeError_nonneg hC M b s
  have hp := prod_upper_of_relative_error
    (Real.log 2) (Real.log_pos one_lt_two).le
    (fun s : BlockSlot v (extendComposition b) ↦
      primeBlockMass (M + s.1)) z
    (fun s ↦ primeBlockMass_nonneg _) hz0
    (primeBlockMass_upper_relative hmass)
  have hcard : Fintype.card (BlockSlot v (extendComposition b)) = k := by
    rw [card_blockSlot, slotCount]
    simp only [extendComposition_fin]
    exact (mem_smirnovOccupancies.mp hb).1
  rw [hcard] at hp
  have hsum : (∑ s, z s) ≤
      4 * (u + 1) * (C / Real.log 2) / (2 : ℝ) ^ M := by
    simpa only [z, blockMassRelativeError, Nat.cast_add, Nat.cast_one]
      using smirnovSlotGeometricError_sum_le
        (M := M) (C := C / Real.log 2) (by positivity) hb
  exact hp.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr hsum) (by positivity))

/-- Power-product form of the preceding slot estimate. -/
theorem smirnovBlockMassPowerProduct_upper
    {M k u v : ℕ} {b : Fin v → ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hb : b ∈ smirnovOccupancies k u v)
    (hmass : ∀ i : Fin v,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val)) :
    (∏ i : Fin v, primeBlockMass (M + i) ^ b i) ≤
      Real.log 2 ^ k *
        Real.exp (4 * (u + 1) * (C / Real.log 2) / (2 : ℝ) ^ M) := by
  calc
    (∏ i : Fin v, primeBlockMass (M + i) ^ b i) =
        ∏ s : BlockSlot v (extendComposition b),
          primeBlockMass (M + s.1) := by
      simpa only [extendComposition_fin] using
        (prod_blockSlot_fiber
          (k := v) (b := extendComposition b)
          (fun i : Fin v ↦ primeBlockMass (M + i))).symm
    _ ≤ _ := smirnovSlotMassProduct_upper hC hb hmass

/-- Sharp reciprocal-mass estimate for one block-count family. -/
theorem compositionBlockFamily_reciprocal_sum_upper_smirnov
    {M k u v : ℕ} {b : Fin v → ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hb : b ∈ smirnovOccupancies k u v)
    (hmass : ∀ i : Fin v,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val)) :
    (∑ a ∈ compositionBlockFamily M b, 1 / (a : ℝ)) ≤
      (Real.log 2 ^ k *
        Real.exp (4 * (u + 1) * (C / Real.log 2) / (2 : ℝ) ^ M)) /
          compositionFactorial b := by
  have hbase := blockFamily_reciprocal_sum_upper M v (extendComposition b)
  have hprod := smirnovBlockMassPowerProduct_upper hC hb hmass
  calc
    (∑ a ∈ compositionBlockFamily M b, 1 / (a : ℝ)) ≤
        ∏ i : Fin v,
          primeBlockMass (M + i) ^ b i /
            ((b i).factorial : ℝ) := by
      simpa only [compositionBlockFamily, extendComposition_fin] using hbase
    _ = (∏ i : Fin v, primeBlockMass (M + i) ^ b i) /
          compositionFactorial b := by
      rw [Finset.prod_div_distrib]
      rfl
    _ ≤ (Real.log 2 ^ k *
          Real.exp (4 * (u + 1) * (C / Real.log 2) /
            (2 : ℝ) ^ M)) /
          compositionFactorial b := by
      exact div_le_div_of_nonneg_right hprod (by
        dsimp [compositionFactorial]
        positivity)

/-- A pointwise cluster envelope combined with the sharp nonuniform mass
estimate for one Smirnov occupancy. -/
theorem compositionBlockClusterMass_le_smirnov
    {M k u v : ℕ} {b : Fin v → ℕ} {C A : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hb : b ∈ smirnovOccupancies k u v)
    (hmass : ∀ i : Fin v,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (henvelope : ∀ a ∈ compositionBlockFamily M b, clusterLength a ≤ A) :
    compositionBlockClusterMass M b ≤
      A * (Real.log 2 ^ k *
        Real.exp (4 * (u + 1) * (C / Real.log 2) / (2 : ℝ) ^ M) /
          compositionFactorial b) := by
  exact compositionBlockClusterMass_le_of_envelope hA henvelope
    (compositionBlockFamily_reciprocal_sum_upper_smirnov hC hb hmass)

/-- Summed sharp estimate over an arbitrary layer of Smirnov occupancies.
This is the nonuniform block-mass input to the discrete form of Ford's
equation (30). -/
theorem blockClusterMassOver_le_smirnovOccupancyMass
    {M k u v : ℕ} {I : Finset (Fin v → ℕ)} {C A : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hI : I ⊆ smirnovOccupancies k u v)
    (hmass : ∀ i : Fin v,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (henvelope : ∀ b ∈ I, ∀ a ∈ compositionBlockFamily M b,
      clusterLength a ≤ A) :
    blockClusterMassOver M I ≤
      A * Real.log 2 ^ k *
        Real.exp (4 * (u + 1) * (C / Real.log 2) / (2 : ℝ) ^ M) *
          smirnovOccupancyMass k u v := by
  calc
    blockClusterMassOver M I ≤
        ∑ b ∈ I,
          A * (Real.log 2 ^ k *
            Real.exp (4 * (u + 1) * (C / Real.log 2) /
              (2 : ℝ) ^ M) /
                compositionFactorial b) := by
      apply Finset.sum_le_sum
      intro b hb
      exact compositionBlockClusterMass_le_smirnov hC hA (hI hb) hmass
        (henvelope b hb)
    _ = A * Real.log 2 ^ k *
        Real.exp (4 * (u + 1) * (C / Real.log 2) / (2 : ℝ) ^ M) *
          (∑ b ∈ I, 1 / compositionFactorial b) := by
      simp_rw [div_eq_mul_inv]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ ≤ A * Real.log 2 ^ k *
        Real.exp (4 * (u + 1) * (C / Real.log 2) / (2 : ℝ) ^ M) *
          smirnovOccupancyMass k u v := by
      apply mul_le_mul_of_nonneg_left
      · rw [smirnovOccupancyMass]
        exact Finset.sum_le_sum_of_subset_of_nonneg hI
          (fun b hb hnot ↦ by
            apply one_div_nonneg.mpr
            dsimp [compositionFactorial]
            positivity)
      · positivity

/-- Full Smirnov-family form of the sharp nonuniform block estimate. -/
theorem smirnovBlockClusterMass_le_geometric_error
    {M k u v : ℕ} {C A : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hmass : ∀ i : Fin v,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (henvelope : ∀ b ∈ smirnovOccupancies k u v,
      ∀ a ∈ compositionBlockFamily M b, clusterLength a ≤ A) :
    smirnovBlockClusterMass M k u v ≤
      A * Real.log 2 ^ k *
        Real.exp (4 * (u + 1) * (C / Real.log 2) / (2 : ℝ) ^ M) *
          smirnovOccupancyMass k u v := by
  simpa only [smirnovBlockClusterMass, blockClusterMassOver] using
    (blockClusterMassOver_le_smirnovOccupancyMass
      hC hA (Finset.Subset.rfl) hmass henvelope)

/-- The preceding finite estimate instantiated by the unconditional
eventual Mertens bound.  The constants `C,J` are absolute and work
simultaneously for every length, cardinality, and Smirnov offset. -/
theorem exists_smirnovBlockClusterMass_geometric_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ J : ℕ, ∀ M : ℕ, J ≤ M →
      ∀ (k u v : ℕ) (A : ℝ), 0 ≤ A →
      (∀ b ∈ smirnovOccupancies k u v,
        ∀ a ∈ compositionBlockFamily M b, clusterLength a ≤ A) →
      smirnovBlockClusterMass M k u v ≤
        A * Real.log 2 ^ k *
          Real.exp (4 * (u + 1) * (C / Real.log 2) /
            (2 : ℝ) ^ M) *
            smirnovOccupancyMass k u v := by
  obtain ⟨C, hC, J, htail⟩ :=
    exists_primeBlockMass_geometric_error_threshold
  refine ⟨C, hC, J, ?_⟩
  intro M hMJ k u v A hA henvelope
  apply smirnovBlockClusterMass_le_geometric_error hC.le hA
    (henvelope := henvelope)
  intro i
  exact htail (M + i.val) (by omega)

/-! ## Global multinomial normalization -/

/-- Summed over the first `v` blocks, the geometric Mertens errors still
cost only one absolute `O(2^{-M})` term. -/
theorem primeBlockMass_sum_error
    {M v : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hmass : ∀ i : Fin v,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val)) :
    |(∑ i : Fin v, primeBlockMass (M + i)) -
        (v : ℝ) * Real.log 2| ≤
      4 * C / (2 : ℝ) ^ M := by
  have hgeom := slot_geometric_error_sum_le
    (M := M) (k := v) (K := 1) (b := fun _i : ℕ ↦ 1) hC
    (fun i ↦ by simp)
  have hgeom' :
      (∑ i : Fin v, C / (2 : ℝ) ^ (M + i.val)) ≤
        4 * C / (2 : ℝ) ^ M := by
    rw [Fintype.sum_sigma] at hgeom
    simpa using hgeom
  have hrewrite :
      (∑ i : Fin v, primeBlockMass (M + i)) -
          (v : ℝ) * Real.log 2 =
        ∑ i : Fin v, (primeBlockMass (M + i) - Real.log 2) := by
    rw [Finset.sum_sub_distrib]
    simp
  rw [hrewrite]
  calc
    |∑ i : Fin v, (primeBlockMass (M + i) - Real.log 2)| ≤
        ∑ i : Fin v, |primeBlockMass (M + i) - Real.log 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin v, C / (2 : ℝ) ^ (M + i.val) :=
      Finset.sum_le_sum fun i hi ↦ hmass i
    _ ≤ 4 * C / (2 : ℝ) ^ M := hgeom'

/-- Weighted multinomial identity for the exact block masses. -/
theorem sum_blockMassPowers_div_compositionFactorial
    (M v k : ℕ) :
    (∑ b ∈ compositionsOf v k,
        (∏ i : Fin v, primeBlockMass (M + i) ^ b i) /
          compositionFactorial b) =
      (∑ i : Fin v, primeBlockMass (M + i)) ^ k /
        (k.factorial : ℝ) := by
  have hpow := Finset.sum_pow_eq_sum_piAntidiag
    (s := (Finset.univ : Finset (Fin v)))
    (f := fun i : Fin v ↦ primeBlockMass (M + i)) k
  have hfin :
      Finset.piAntidiag (Finset.univ : Finset (Fin v)) k =
        compositionsOf v k := by
    ext b
    simp [compositionsOf]
  rw [hfin] at hpow
  calc
    (∑ b ∈ compositionsOf v k,
        (∏ i : Fin v, primeBlockMass (M + i) ^ b i) /
          compositionFactorial b) =
      ∑ b ∈ compositionsOf v k,
        ((Nat.multinomial Finset.univ b : ℝ) *
          ∏ i : Fin v, primeBlockMass (M + i) ^ b i) /
            (k.factorial : ℝ) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [show (∏ i : Fin v, primeBlockMass (M + i) ^ b i) /
          compositionFactorial b =
        (∏ i : Fin v, primeBlockMass (M + i) ^ b i) *
          (1 / compositionFactorial b) by ring]
      rw [inv_compositionFactorial_eq_multinomial_div_of_mem hb]
      ring
    _ = (∑ b ∈ compositionsOf v k,
        (Nat.multinomial Finset.univ b : ℝ) *
          ∏ i : Fin v, primeBlockMass (M + i) ^ b i) /
            (k.factorial : ℝ) := by
      rw [Finset.sum_div]
    _ = (∑ i : Fin v, primeBlockMass (M + i)) ^ k /
        (k.factorial : ℝ) := by rw [← hpow]

/-- Summing the independent block-family majorants over every occupancy
recovers the exact multinomial normalization. -/
theorem sum_compositionBlockFamily_reciprocal_upper
    (M v k : ℕ) :
    (∑ b ∈ compositionsOf v k,
      ∑ a ∈ compositionBlockFamily M b, 1 / (a : ℝ)) ≤
      (∑ i : Fin v, primeBlockMass (M + i)) ^ k /
        (k.factorial : ℝ) := by
  calc
    (∑ b ∈ compositionsOf v k,
      ∑ a ∈ compositionBlockFamily M b, 1 / (a : ℝ)) ≤
        ∑ b ∈ compositionsOf v k,
          (∏ i : Fin v, primeBlockMass (M + i) ^ b i) /
            compositionFactorial b := by
      apply Finset.sum_le_sum
      intro b hb
      have hbase := blockFamily_reciprocal_sum_upper M v (extendComposition b)
      calc
        (∑ a ∈ compositionBlockFamily M b, 1 / (a : ℝ)) ≤
            ∏ i : Fin v,
              primeBlockMass (M + i) ^ b i /
                ((b i).factorial : ℝ) := by
          simpa only [compositionBlockFamily, extendComposition_fin] using hbase
        _ = (∏ i : Fin v, primeBlockMass (M + i) ^ b i) /
              compositionFactorial b := by
          rw [Finset.prod_div_distrib]
          rfl
    _ = _ := sum_blockMassPowers_div_compositionFactorial M v k

/-- For Ford's range `k ≤ 10v`, global multinomial normalization absorbs
all block-mass errors into one absolute exponential factor.  This is the
second (unconstrained) form of the sharp error control behind equation (30).
-/
theorem primeBlockMass_sum_pow_upper
    {M v k : ℕ} {C : ℝ} (hC : 0 ≤ C) (hv : 0 < v)
    (hkv : k ≤ 10 * v)
    (hmass : ∀ i : Fin v,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val)) :
    (∑ i : Fin v, primeBlockMass (M + i)) ^ k ≤
      ((v : ℝ) * Real.log 2) ^ k *
        Real.exp (40 * C / (Real.log 2 * (2 : ℝ) ^ M)) := by
  let B : ℝ := (v : ℝ) * Real.log 2
  let D : ℝ := 4 * C / (2 : ℝ) ^ M
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hsum0 : 0 ≤ ∑ i : Fin v, primeBlockMass (M + i) :=
    Finset.sum_nonneg fun i hi ↦ primeBlockMass_nonneg _
  have hsumUpper :
      (∑ i : Fin v, primeBlockMass (M + i)) ≤ B + D := by
    have herr := le_of_abs_le (primeBlockMass_sum_error hC hmass)
    dsimp [B, D]
    linarith
  have hz : 0 ≤ D / B := div_nonneg hD hB.le
  have honeExp : 1 + D / B ≤ Real.exp (D / B) := by
    simpa only [add_comm] using Real.add_one_le_exp (D / B)
  have hkR : ((k : ℕ) : ℝ) ≤ 10 * (v : ℝ) := by exact_mod_cast hkv
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have harg :
      (k : ℝ) * (D / B) ≤
        40 * C / (Real.log 2 * (2 : ℝ) ^ M) := by
    have hkvDiv : (k : ℝ) / (v : ℝ) ≤ 10 :=
      (div_le_iff₀ hvR).2 (by simpa only [mul_comm] using hkR)
    have hfactor : 0 ≤ 4 * C /
        (Real.log 2 * (2 : ℝ) ^ M) := by positivity
    calc
      (k : ℝ) * (D / B) =
          ((k : ℝ) / (v : ℝ)) *
            (4 * C / (Real.log 2 * (2 : ℝ) ^ M)) := by
        dsimp [B, D]
        field_simp
      _ ≤ 10 * (4 * C /
          (Real.log 2 * (2 : ℝ) ^ M)) :=
        mul_le_mul_of_nonneg_right hkvDiv hfactor
      _ = 40 * C / (Real.log 2 * (2 : ℝ) ^ M) := by ring
  calc
    (∑ i : Fin v, primeBlockMass (M + i)) ^ k ≤ (B + D) ^ k :=
      pow_le_pow_left₀ hsum0 hsumUpper k
    _ = B ^ k * (1 + D / B) ^ k := by
      have hBD : B + D = B * (1 + D / B) := by
        field_simp [hB.ne']
      rw [hBD, mul_pow]
    _ ≤ B ^ k * (Real.exp (D / B)) ^ k := by
      apply mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) honeExp k)
      positivity
    _ = B ^ k * Real.exp ((k : ℝ) * (D / B)) := by
      rw [← Real.exp_nat_mul]
    _ ≤ B ^ k *
        Real.exp (40 * C / (Real.log 2 * (2 : ℝ) ^ M)) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by positivity)
    _ = ((v : ℝ) * Real.log 2) ^ k *
        Real.exp (40 * C / (Real.log 2 * (2 : ℝ) ^ M)) := by rfl

/-- Equation-(30) normalization for the sum of all block families, retaining
the exact base `v * log 2` rather than `(log 2 + ε) * v`. -/
theorem sum_compositionBlockFamily_reciprocal_upper_sharp
    {M v k : ℕ} {C : ℝ} (hC : 0 ≤ C) (hv : 0 < v)
    (hkv : k ≤ 10 * v)
    (hmass : ∀ i : Fin v,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val)) :
    (∑ b ∈ compositionsOf v k,
      ∑ a ∈ compositionBlockFamily M b, 1 / (a : ℝ)) ≤
      (((v : ℝ) * Real.log 2) ^ k *
        Real.exp (40 * C / (Real.log 2 * (2 : ℝ) ^ M))) /
          (k.factorial : ℝ) := by
  exact (sum_compositionBlockFamily_reciprocal_upper M v k).trans
    (div_le_div_of_nonneg_right
      (primeBlockMass_sum_pow_upper hC hv hkv hmass) (by positivity))

/-- If the Smirnov offset is no larger than the initial geometric scale,
the entire nonuniformity costs an absolute factor independent of `k` and
`v`, while the base remains exactly `log 2`. -/
theorem blockClusterMassOver_le_smirnovOccupancyMass_of_offset
    {M k u v : ℕ} {I : Finset (Fin v → ℕ)} {C A : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hu : u + 1 ≤ 2 ^ M)
    (hI : I ⊆ smirnovOccupancies k u v)
    (hmass : ∀ i : Fin v,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (henvelope : ∀ b ∈ I, ∀ a ∈ compositionBlockFamily M b,
      clusterLength a ≤ A) :
    blockClusterMassOver M I ≤
      A * Real.log 2 ^ k * Real.exp (4 * C / Real.log 2) *
        smirnovOccupancyMass k u v := by
  have hraw := blockClusterMassOver_le_smirnovOccupancyMass
    hC hA hI hmass henvelope
  have hpow : (0 : ℝ) < (2 : ℝ) ^ M := by positivity
  have huR : ((u + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ M := by
    exact_mod_cast hu
  have hexpArg :
      4 * (u + 1) * (C / Real.log 2) / (2 : ℝ) ^ M ≤
        4 * C / Real.log 2 := by
    have hratio : ((u + 1 : ℕ) : ℝ) / (2 : ℝ) ^ M ≤ 1 :=
      (div_le_one hpow).2 huR
    have hnonneg : 0 ≤ 4 * (C / Real.log 2) := by positivity
    calc
      4 * (u + 1) * (C / Real.log 2) / (2 : ℝ) ^ M =
          (4 * (C / Real.log 2)) *
            (((u + 1 : ℕ) : ℝ) / (2 : ℝ) ^ M) := by
        push_cast
        ring
      _ ≤ (4 * (C / Real.log 2)) * 1 :=
        mul_le_mul_of_nonneg_left hratio hnonneg
      _ = 4 * C / Real.log 2 := by ring
  apply hraw.trans
  apply mul_le_mul_of_nonneg_right _
    (smirnovOccupancyMass_nonneg k u v)
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexpArg)
  positivity

/-! ## Concrete finite dyadic layers -/

/-- The sharp prefix envelope is never smaller than `log 2`. -/
theorem log_two_le_blockClusterSharpPrefixEnvelope
    (M k : ℕ) {v : ℕ} (b : Fin v → ℕ) (h : ℕ) :
    Real.log 2 ≤ blockClusterSharpPrefixEnvelope M k b h := by
  rw [blockClusterSharpPrefixEnvelope]
  have hp : (1 : ℝ) ≤ (2 : ℝ) ^ (k - blockPrefixCount b h) :=
    one_le_pow₀ (by norm_num)
  have hi : (1 : ℝ) ≤
      (2 : ℝ) ^ (M + 1) * (blockPrefixWeight b h : ℝ) + 1 := by
    have hnonneg : 0 ≤
        (2 : ℝ) ^ (M + 1) * (blockPrefixWeight b h : ℝ) := by
      positivity
    linarith
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc
    Real.log 2 = 1 * (1 * Real.log 2) := by ring
    _ ≤ (2 : ℝ) ^ (k - blockPrefixCount b h) *
        (((2 : ℝ) ^ (M + 1) * (blockPrefixWeight b h : ℝ) + 1) *
          Real.log 2) := by
      exact mul_le_mul hp (mul_le_mul_of_nonneg_right hi hl)
        (mul_nonneg (by norm_num) hl) (by positivity)

/-- The minimum over sharp prefixes retains the same positive lower bound. -/
theorem log_two_le_blockClusterSharpEnvelope
    (M k : ℕ) {v : ℕ} (b : Fin v → ℕ) :
    Real.log 2 ≤ blockClusterSharpEnvelope M k b := by
  rw [blockClusterSharpEnvelope]
  apply Finset.le_min'
  intro x hx
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hx
  exact log_two_le_blockClusterSharpPrefixEnvelope M k b h

/-- Only finitely many dyadic layers are nonempty.  This explicit cutoff is
what lets one choose the initial block far enough out once and then use the
absolute-factor form of the Mertens-error estimate on every genuine layer. -/
theorem sharpBlockDyadicLayer_eq_empty_of_add_le
    {M k v m : ℕ} (hm : M + k + 2 ≤ m) :
    sharpBlockDyadicLayer M k v m = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hbData := mem_sharpBlockDyadicLayer.mp hb
  have hlower := log_two_le_blockClusterSharpEnvelope M k b
  have hpow : (2 : ℝ) ^ (M + k + 2) ≤ (2 : ℝ) ^ m := by
    exact pow_le_pow_right₀ (by norm_num) hm
  have hpowm : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hratio : (2 : ℝ) ^ (M + k + 2) / (2 : ℝ) ^ m ≤ 1 :=
    (div_le_one hpowm).2 hpow
  have hupper :
      sharpBlockLayerScale M * (2 : ℝ) ^ (k + 1) /
          (2 : ℝ) ^ m ≤ Real.log 2 := by
    calc
      sharpBlockLayerScale M * (2 : ℝ) ^ (k + 1) /
          (2 : ℝ) ^ m =
          Real.log 2 *
            ((2 : ℝ) ^ (M + k + 2) / (2 : ℝ) ^ m) := by
        rw [sharpBlockLayerScale]
        have hpowers :
            (2 : ℝ) ^ (M + k + 2) =
              (2 : ℝ) ^ (M + 1) * (2 : ℝ) ^ (k + 1) := by
          rw [show M + k + 2 = (M + 1) + (k + 1) by omega, pow_add]
        rw [hpowers]
        ring
      _ ≤ Real.log 2 * 1 :=
        mul_le_mul_of_nonneg_left hratio
          (Real.log_nonneg (by norm_num))
      _ = Real.log 2 := by ring
  exact (not_lt_of_ge hlower) (hbData.2.2.trans_le hupper)

/-- A member of a genuine layer has an index below the explicit cutoff. -/
theorem sharpBlockDyadicLayer_index_lt
    {M k v m : ℕ} {b : Fin v → ℕ}
    (hb : b ∈ sharpBlockDyadicLayer M k v m) :
    m < M + k + 2 := by
  by_contra hm
  have hempty := sharpBlockDyadicLayer_eq_empty_of_add_le
    (M := M) (k := k) (v := v) (m := m) (by omega)
  rw [hempty] at hb
  simp at hb

/-- If `2^M` dominates the finite layer cutoff, every genuine layer has a
Smirnov offset at most `2^M`. -/
theorem sharpBlockDyadicLayer_offset_le_two_pow
    {M k v m : ℕ} {b : Fin v → ℕ}
    (hM : M + k + blockLayerSlack k + 2 ≤ 2 ^ M)
    (hb : b ∈ sharpBlockDyadicLayer M k v m) :
    m + blockLayerSlack k + 1 ≤ 2 ^ M := by
  have hm := sharpBlockDyadicLayer_index_lt hb
  omega

/-- Fully concrete layer estimate with actual prime-block masses and the
exact base `log 2`.  The only error is the absolute factor
`exp (4 C / log 2)`, independent of the layer and of `k`. -/
theorem sharpBlockDyadicLayer_mass_le
    {M k v m : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hM : M + k + blockLayerSlack k + 2 ≤ 2 ^ M)
    (hmass : ∀ i : Fin v,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val)) :
    blockClusterMassOver M (sharpBlockDyadicLayer M k v m) ≤
      (sharpBlockLayerScale M * (2 : ℝ) ^ (k + 1) / (2 : ℝ) ^ m) *
        Real.log 2 ^ k * Real.exp (4 * C / Real.log 2) *
          smirnovOccupancyMass k (m + blockLayerSlack k) v := by
  by_cases hempty : sharpBlockDyadicLayer M k v m = ∅
  · rw [hempty]
    simp only [blockClusterMassOver, Finset.sum_empty]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (div_nonneg (mul_nonneg (sharpBlockLayerScale_pos M).le
            (by positivity)) (by positivity))
          (by positivity))
        (Real.exp_pos _).le)
      (smirnovOccupancyMass_nonneg k (m + blockLayerSlack k) v)
  · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hA : 0 ≤
        sharpBlockLayerScale M * (2 : ℝ) ^ (k + 1) /
          (2 : ℝ) ^ m := by
      exact div_nonneg
        (mul_nonneg (sharpBlockLayerScale_pos M).le (by positivity))
        (by positivity)
    apply blockClusterMassOver_le_smirnovOccupancyMass_of_offset
      hC hA
      (sharpBlockDyadicLayer_offset_le_two_pow hM hb)
      (sharpBlockDyadicLayer_subset_smirnov M k v m) hmass
    intro c hc a ha
    exact sharpBlockDyadicLayer_clusterLength_le hc ha

/-- Canonical integral-layer analogue.  Since the canonical layer indices
satisfy `m ≤ k`, it is enough that `2^M` dominate `k` plus the logarithmic
barrier slack. -/
theorem blockIntegerDyadicLayer_mass_le
    {M k v m : ℕ} {C : ℝ} (hC : 0 ≤ C) (hmk : m ≤ k)
    (hM : k + blockLayerSlack k + 1 ≤ 2 ^ M)
    (hmass : ∀ i : Fin v,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val)) :
    blockClusterMassOver M (blockIntegerDyadicLayer k v m) ≤
      (sharpBlockLayerScale M * (2 : ℝ) ^ (k - m + 1)) *
        Real.log 2 ^ k * Real.exp (4 * C / Real.log 2) *
          smirnovOccupancyMass k (m + blockLayerSlack k) v := by
  have hu : m + blockLayerSlack k + 1 ≤ 2 ^ M :=
    (Nat.add_le_add_right hmk (blockLayerSlack k + 1)).trans (by
      simpa only [Nat.add_assoc] using hM)
  apply blockClusterMassOver_le_smirnovOccupancyMass_of_offset
    hC (by
      exact mul_nonneg (sharpBlockLayerScale_pos M).le (by positivity))
    hu (blockIntegerDyadicLayer_subset_smirnov k v m) hmass
  intro b hb a ha
  exact blockIntegerDyadicLayer_clusterLength_le hb ha

end Erdos446
