/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.BoundedMomentPowerBudget
import ErdosProblems.Erdos207.GeometricCrudeStateTails

/-! # A single integer power exponent for all four geometric crude cutoffs -/

namespace Erdos207

open scoped NNReal

noncomputable section

def dyadicCrudeExponent (q a u : ℕ) : ℕ := a + 2 * q * (u + 1) + 1

def dyadicCrudeThresholds (V : Type*) [Fintype V] (t k : ℕ) : CrudeThresholds where
  rooted := fun j c ↦ (Fintype.card V + 1 : ℝ≥0) ^ (j - c - 5) * (t : ℝ≥0) ^ k
  pair := (t : ℝ≥0) ^ k
  common := (t : ℝ≥0) ^ k
  gain := fun j c ↦ (Fintype.card V + 1 : ℝ≥0) ^ (j - c - 4) * (t : ℝ≥0) ^ k

theorem boundedMoment_uniform_power_cutoff
    (q t a u d : ℕ) (w κ Z : ℝ≥0) (ht : 1 ≤ t) (hd : d ≤ 2 * q)
    (hw : w ≤ (t : ℝ≥0) ^ u) (hκ : κ ≤ Z * (t : ℝ≥0) ^ a)
    (hconst : 2 * (2 * q + 1) ^ (2 * q + 1) ≤ t) :
    2 * (w ^ d * ((boundedIntersectionMomentCoefficient d t : ℝ≥0) * κ)) ≤
      Z * (t : ℝ≥0) ^ dyadicCrudeExponent q a u := by
  have hpow : (d + 1) ^ (d + 1) ≤ (2 * q + 1) ^ (2 * q + 1) :=
    (Nat.pow_le_pow_left (by omega) (d + 1)).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hconstd : 2 * (d + 1) ^ (d + 1) ≤ t :=
    (Nat.mul_le_mul_left 2 hpow).trans hconst
  have hc : 2 * (((d + 1) ^ (d + 1) : ℕ) : ℝ≥0) * 1 ≤ (t : ℝ≥0) := by
    exact_mod_cast (show 2 * (d + 1) ^ (d + 1) * 1 ≤ t by simpa using hconstd)
  have hbase := boundedMoment_power_cutoff d t a u (t : ℝ≥0) w κ 1 Z ht le_rfl hw
    (by simpa only [one_mul] using hκ) hc
  apply hbase.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_right₀ (by exact_mod_cast ht)
  unfold dyadicCrudeExponent
  have hm := Nat.mul_le_mul_right (u + 1) hd
  omega

theorem dyadicCrudeThresholds_geometric
    {V : Type*} [Fintype V] [DecidableEq V]
    (q t a u : ℕ) (bank : TripleSystemOn V) (ht : 1 ≤ t)
    (hconst : 2 * (2 * q + 1) ^ (2 * q + 1) ≤ t)
    (hroot : (2 : ℝ≥0) ^ q * pairExactBankExtensionCoefficient q bank ≤ (t : ℝ≥0) ^ a)
    (hpair : (pairTwoAwayThreatExtensionCoefficient q bank : ℝ≥0) ≤ (t : ℝ≥0) ^ a)
    (hcommon : absorberCommonThreatWeightBound q bank ≤ (t : ℝ≥0) ^ a)
    (hgain : absorberGainDefectWeightBound q bank ≤ (t : ℝ≥0) ^ a) :
    GeometricCrudeCutoffs q t bank ((t : ℝ≥0) ^ u)
      (dyadicCrudeThresholds V t (dyadicCrudeExponent q a u)) := by
  have htpos : (0 : ℝ≥0) < t := by exact_mod_cast (show 0 < t by omega)
  have hNpos : (0 : ℝ≥0) < Fintype.card V + 1 := by positivity
  constructor
  · intro i
    dsimp only [dyadicCrudeThresholds]
    positivity
  · dsimp only [dyadicCrudeThresholds]
    positivity
  · dsimp only [dyadicCrudeThresholds]
    positivity
  · intro i
    dsimp only [dyadicCrudeThresholds]
    positivity
  · intro i
    have hd : i.chosen ≤ 2 * q := by have hb := i.budget; have hj := i.order_le; omega
    have hpow : (2 : ℝ≥0) ^ (i.order - 2) ≤ 2 ^ q :=
      pow_le_pow_right₀ (by norm_num) (by have hj := i.order_le; omega)
    have hc : (2 : ℝ≥0) ^ (i.order - 2) * pairExactBankExtensionCoefficient q bank ≤ (t : ℝ≥0) ^ a :=
      (mul_le_mul_of_nonneg_right hpow (by positivity)).trans hroot
    apply boundedMoment_uniform_power_cutoff q t a u i.chosen _ _ _ ht hd le_rfl ?_ hconst
    calc
      _ ≤ (t : ℝ≥0) ^ a * (Fintype.card V + 1 : ℝ≥0) ^ (i.order - i.chosen - 5) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring
  · have h := boundedMoment_uniform_power_cutoff q t a u q ((t : ℝ≥0) ^ u) _ 1 ht
      (by omega) le_rfl (by simpa only [one_mul] using hpair) hconst
    simpa only [one_mul, dyadicCrudeThresholds] using h
  · have h := boundedMoment_uniform_power_cutoff q t a u (2 * q) ((t : ℝ≥0) ^ u) _ 1 ht
      le_rfl le_rfl (by simpa only [one_mul] using hcommon) hconst
    simpa only [one_mul, dyadicCrudeThresholds] using h
  · intro i
    apply boundedMoment_uniform_power_cutoff q t a u (2 * q) _ _ _ ht le_rfl le_rfl ?_ hconst
    calc
      _ ≤ (t : ℝ≥0) ^ a * (Fintype.card V + 1 : ℝ≥0) ^ (i.order - i.chosen - 4) :=
        mul_le_mul_of_nonneg_right hgain (by positivity)
      _ = _ := by ring

end

end Erdos207
