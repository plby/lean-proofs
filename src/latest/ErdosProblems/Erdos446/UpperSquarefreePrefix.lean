/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperComplementaryClusterReduction
import ErdosProblems.Erdos851.DyadicDensity

/-!
# Erdős Problem 446: from squarefree shells to squarefree prefixes

This file isolates the exact dyadic induction needed after the complementary
largest-prime shell argument.  Its hypotheses retain the endpoint term and
the lower shell cutoff explicitly; this makes the later powerful-part
summation free of hidden asymptotic or rounding assumptions.
-/

namespace Erdos446

open Finset Set MeasureTheory Real Filter
open scoped BigOperators Topology

noncomputable section

/-- Squarefree integers having a divisor in the indicated interval. -/
def squarefreeDivisorSet (y z : ℕ) : Set ℕ :=
  {n | Squarefree n ∧ 0 < divisorCountIoc y z n}

/-- The corresponding count in `[0,N)`. -/
def squarefreeDivisorPrefixSet (N y z : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun n ↦
    Squarefree n ∧ 0 < divisorCountIoc y z n

/-- The cardinality of `squarefreeDivisorPrefixSet`. -/
def squarefreeDivisorPrefixCount (N y z : ℕ) : ℕ := by
  exact (squarefreeDivisorPrefixSet N y z).card

@[simp] theorem card_squarefreeDivisorPrefixSet (N y z : ℕ) :
    (squarefreeDivisorPrefixSet N y z).card =
      squarefreeDivisorPrefixCount N y z := rfl

theorem squarefreeDivisorPrefixCount_eq_exceptionalPrefixCount
    (N y z : ℕ) :
    squarefreeDivisorPrefixCount N y z =
      Erdos851.exceptionalPrefixCount (squarefreeDivisorSet y z) N := by
  classical
  unfold squarefreeDivisorPrefixCount squarefreeDivisorPrefixSet
    Erdos851.exceptionalPrefixCount squarefreeDivisorSet
  simp only [Set.mem_setOf_eq]

theorem squarefreeDivisorShell_card_eq_exceptionalDyadicCount
    (X y z : ℕ) :
    (squarefreeDivisorShell X (2 * X) y z).card =
      Erdos851.exceptionalDyadicCount (squarefreeDivisorSet y z) X := by
  classical
  rw [Erdos851.exceptionalDyadicCount_eq_filter_card]
  apply congrArg Finset.card
  ext n
  simp only [squarefreeDivisorShell, squarefreeDivisorSet,
    Erdos851.dyadicInterval, Finset.mem_filter, Finset.mem_Ioc,
    Set.mem_setOf_eq, and_assoc]

/-- Every positive integer contributes the interval belonging to the divisor
`1`, hence its cluster has length at least `log 2`. -/
theorem log_two_le_clusterLength_of_pos {a : ℕ} (ha : 0 < a) :
    Real.log 2 ≤ clusterLength a := by
  have hmem : 1 ∈ a.divisors :=
    Nat.mem_divisors.mpr ⟨one_dvd a, ha.ne'⟩
  have hsub : divisorLogInterval 1 ⊆ divisorCluster a :=
    divisorLogInterval_subset_cluster hmem
  have hmono : volume.real (divisorLogInterval 1) ≤
      volume.real (divisorCluster a) :=
    MeasureTheory.measureReal_mono hsub
      (volume_divisorCluster_lt_top a).ne
  simpa only [Measure.real, volume_divisorLogInterval,
    ENNReal.toReal_ofReal (Real.log_nonneg one_le_two), clusterLength]
    using hmono

/-- The empty prime support gives a uniform positive term in the smooth
squarefree cluster mass. -/
theorem log_two_le_squarefreeClusterMass (P : ℕ) :
    Real.log 2 ≤ squarefreeClusterMass P := by
  rw [squarefreeClusterMass_eq_powersetMoment_zero]
  unfold powersetAdditiveMoment
  simp only [pow_zero, mul_one]
  have hempty : ∅ ∈ (primesUpTo P).powerset := by simp
  have hterm : Real.log 2 ≤ primeSubsetClusterTerm ∅ := by
    simpa [primeSubsetClusterTerm] using
      (log_two_le_clusterLength_of_pos (a := 1) (by norm_num))
  calc
    Real.log 2 ≤ primeSubsetClusterTerm ∅ := hterm
    _ ≤ ∑ S ∈ (primesUpTo P).powerset,
        primeSubsetClusterTerm S := by
      apply Finset.single_le_sum
      · intro S hS
        exact primeSubsetClusterTerm_nonneg S
      · simpa using hempty

/-- The variable-denominator sum is strictly positive.  This fact is used
only to make the two slopes in the dyadic induction genuinely distinct. -/
theorem fordVariableDenominatorSum_pos {Y P : ℕ} (hY : 2 ≤ Y) :
    0 < fordVariableDenominatorSum Y P := by
  have hempty : ∅ ∈ (primesUpTo P).powerset := by simp
  have hcluster : 0 < primeSubsetClusterTerm ∅ := by
    have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hlower : Real.log 2 ≤ primeSubsetClusterTerm ∅ := by
      simpa [primeSubsetClusterTerm] using
        (log_two_le_clusterLength_of_pos (a := 1) (by norm_num))
    linarith
  have harg : 1 < fordVariableLogArgument Y ∅ := by
    have hpow : 1 < (Y : ℝ) ^ (2 / 3 : ℝ) :=
      Real.one_lt_rpow (by exact_mod_cast (show 1 < Y by omega))
        (by norm_num)
    simpa [fordVariableLogArgument, primeSupportMax] using hpow
  have hlog : 0 < Real.log (fordVariableLogArgument Y ∅) :=
    Real.log_pos harg
  have hpositive : 0 < primeSubsetClusterTerm ∅ /
      Real.log (fordVariableLogArgument Y ∅) ^ 2 := by positivity
  unfold fordVariableDenominatorSum
  have hsingle : primeSubsetClusterTerm ∅ /
        Real.log (fordVariableLogArgument Y ∅) ^ 2 ≤
      ∑ S ∈ (primesUpTo P).powerset,
        primeSubsetClusterTerm S /
          Real.log (fordVariableLogArgument Y S) ^ 2 := by
    let f : Finset ℕ → ℝ := fun S ↦ primeSubsetClusterTerm S /
      Real.log (fordVariableLogArgument Y S) ^ 2
    have hsum := Finset.single_le_sum (s := (primesUpTo P).powerset)
      (f := f) (fun S hS ↦
        div_nonneg (primeSubsetClusterTerm_nonneg S) (sq_nonneg _)) hempty
    simpa [f] using hsum
  exact hpositive.trans_le hsingle

/-- A quantitative form of positivity, supplied by the empty support.  The
slightly wasteful constant `1` (instead of the exact `9/4`) is convenient in
all later endpoint absorptions. -/
theorem log_two_div_log_sq_le_fordVariableDenominatorSum
    {Y P : ℕ} (hY : 2 ≤ Y) :
    Real.log 2 / Real.log (Y : ℝ) ^ 2 ≤
      fordVariableDenominatorSum Y P := by
  have hlogY : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hempty : ∅ ∈ (primesUpTo P).powerset := by simp
  have hcluster : Real.log 2 ≤ primeSubsetClusterTerm ∅ := by
    simpa [primeSubsetClusterTerm] using
      (log_two_le_clusterLength_of_pos (a := 1) (by norm_num))
  have harg : fordVariableLogArgument Y ∅ =
      (Y : ℝ) ^ (2 / 3 : ℝ) := by
    simp [fordVariableLogArgument, primeSupportMax]
  have hlogarg : Real.log (fordVariableLogArgument Y ∅) =
      (2 / 3 : ℝ) * Real.log (Y : ℝ) := by
    rw [harg, Real.log_rpow (by exact_mod_cast (show 0 < Y by omega))]
  have hden : Real.log (fordVariableLogArgument Y ∅) ^ 2 ≤
      Real.log (Y : ℝ) ^ 2 := by
    rw [hlogarg]
    nlinarith [sq_nonneg (Real.log (Y : ℝ))]
  have hsingle : primeSubsetClusterTerm ∅ /
        Real.log (fordVariableLogArgument Y ∅) ^ 2 ≤
      fordVariableDenominatorSum Y P := by
    unfold fordVariableDenominatorSum
    let f : Finset ℕ → ℝ := fun S ↦ primeSubsetClusterTerm S /
      Real.log (fordVariableLogArgument Y S) ^ 2
    have hsum := Finset.single_le_sum (s := (primesUpTo P).powerset)
      (f := f) (fun S hS ↦
        div_nonneg (primeSubsetClusterTerm_nonneg S) (sq_nonneg _)) hempty
    simpa [f] using hsum
  calc
    Real.log 2 / Real.log (Y : ℝ) ^ 2 ≤
        primeSubsetClusterTerm ∅ / Real.log (Y : ℝ) ^ 2 := by
      exact div_le_div_of_nonneg_right hcluster (sq_nonneg _)
    _ ≤ primeSubsetClusterTerm ∅ /
          Real.log (fordVariableLogArgument Y ∅) ^ 2 := by
      exact div_le_div_of_nonneg_left
        (primeSubsetClusterTerm_nonneg ∅)
        (by rw [hlogarg]; positivity) hden
    _ ≤ fordVariableDenominatorSum Y P := hsingle

/-- A target-denominator squarefree shell estimate yields an affine prefix
estimate.  The hypotheses `hscale` and `hendpoint` are exactly the two
conditions needed at the first dyadic shell; monotonicity then supplies them
at every larger shell. -/
theorem exists_pos_squarefreeDivisorPrefix_le_affine_targetDenominator :
    ∃ K : ℝ, 0 < K ∧ ∀ Y v M N : ℕ,
      2 ≤ Y → 1 ≤ v → v ≤ Y →
      (Y : ℝ) ^ (2 / 3 : ℝ) ≤ (v : ℝ) →
      4 * v ≤ M →
      (Y : ℝ) ^ (2 / 3 : ℝ) ≤ (M / (4 * v) : ℕ) →
      (2 * v + 1 : ℕ) ≤
        K * fordVariableDenominatorSum Y (2 * Y) * (M : ℝ) →
      (squarefreeDivisorPrefixCount N v (2 * v) : ℝ) ≤
        4 * K * fordVariableDenominatorSum Y (2 * Y) * (N : ℝ) +
          2 * (M : ℝ) := by
  obtain ⟨K, hK, hshell⟩ :=
    exists_pos_squarefreeDyadicShell_le_targetVariableDenominator
  refine ⟨K, hK, fun Y v M N hY hv hvY hvscale hMv hscale hendpoint ↦ ?_⟩
  let V : ℝ := fordVariableDenominatorSum Y (2 * Y)
  let δ : ℝ := 3 * K * V
  let c : ℝ := 4 * K * V
  have hV : 0 < V := fordVariableDenominatorSum_pos hY
  have hM : 2 ≤ M := by omega
  have hδc : δ < c := by dsimp [δ, c, V]; nlinarith
  have hc : 0 ≤ c := by dsimp [c, V]; positivity
  have hgap : c ≤ (c - δ) * M := by
    have hMfour : (4 : ℝ) ≤ M := by exact_mod_cast (show 4 ≤ M by omega)
    dsimp [c, δ, V]
    nlinarith [mul_pos hK hV]
  have hshell' : ∀ R, M ≤ R →
      (Erdos851.exceptionalDyadicCount (squarefreeDivisorSet v (2 * v)) R : ℝ) ≤
        δ * R := by
    intro R hMR
    have hRv : 8 * v ≤ 2 * R := by omega
    have hdivmono : M / (4 * v) ≤ R / (4 * v) :=
      Nat.div_le_div_right hMR
    have hscaleR : (Y : ℝ) ^ (2 / 3 : ℝ) ≤
        ((2 * R) / (8 * v) : ℕ) := by
      have hscaleR' : (Y : ℝ) ^ (2 / 3 : ℝ) ≤
          (R / (4 * v) : ℕ) :=
        hscale.trans (by exact_mod_cast hdivmono)
      have hid : (2 * R) / (8 * v) = R / (4 * v) := by
        rw [show 8 * v = 2 * (4 * v) by omega]
        exact Nat.mul_div_mul_left R (4 * v) (by norm_num)
      rw [hid]
      exact hscaleR'
    have hbase := hshell Y v (2 * R) hY hv hvY hRv hvscale hscaleR
    have hendpointR : ((2 * v + 1 : ℕ) : ℝ) ≤
        K * V * (R : ℝ) := by
      exact hendpoint.trans (mul_le_mul_of_nonneg_left
        (by exact_mod_cast hMR) (mul_nonneg hK.le hV.le))
    push_cast at hendpointR
    have hhalf : (2 * R) / 2 = R := by omega
    rw [hhalf, squarefreeDivisorShell_card_eq_exceptionalDyadicCount] at hbase
    dsimp [δ, V]
    calc
      (Erdos851.exceptionalDyadicCount
          (squarefreeDivisorSet v (2 * v)) R : ℝ) ≤
          (2 * v + 1 : ℕ) + K * ((2 * R : ℕ) : ℝ) * V := by
        simpa [Nat.mul_div_left] using hbase
      _ ≤ K * V * (R : ℝ) + K * (2 * (R : ℝ)) * V := by
        push_cast
        gcongr
      _ = 3 * K * V * (R : ℝ) := by ring
  have hbasePrefix : ∀ T, T < 2 * M →
      (Erdos851.exceptionalPrefixCount
          (squarefreeDivisorSet v (2 * v)) T : ℝ) ≤
        c * T + 2 * (M : ℝ) := by
    intro T hTM
    have htriv : (Erdos851.exceptionalPrefixCount
        (squarefreeDivisorSet v (2 * v)) T : ℝ) ≤ T := by
      exact_mod_cast Erdos851.exceptionalPrefixCount_le
        (squarefreeDivisorSet v (2 * v)) T
    have hT : (T : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast hTM.le
    have hcT : 0 ≤ c * (T : ℝ) := mul_nonneg hc (Nat.cast_nonneg T)
    linarith
  have hall := Erdos851.exceptionalPrefixCount_le_affine_of_dyadic
    (squarefreeDivisorSet v (2 * v)) hM hδc hc hgap hshell' hbasePrefix N
  rw [← squarefreeDivisorPrefixCount_eq_exceptionalPrefixCount] at hall
  simpa [c, V, mul_assoc] using hall

end

end Erdos446
