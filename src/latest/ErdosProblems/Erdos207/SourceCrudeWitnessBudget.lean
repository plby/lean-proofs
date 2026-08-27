/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceCrudeTailExpressions

/-! # Uniform polynomial bounds for source witnesses and the crude index -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sourceCrudeUniformWitnessFactor (q h : ℕ) : ℝ≥0 :=
  h * (2 : ℝ≥0) ^ q + (h : ℝ≥0) ^ 2 * (q + 1 : ℝ≥0) + (h : ℝ≥0) ^ 2 * (2 : ℝ≥0) ^ q

theorem sourceCrudeWitnessCount_le
    {I : Type*} [Fintype I] (order : I → ℕ) (q N : ℕ) (horder : ∀ i, order i ≤ q) :
    sourceCrudeWitnessCount order N ≤
      (Fintype.card I : ℝ≥0) * (2 : ℝ≥0) ^ q * (N + 1 : ℝ≥0) ^ (6 * q) := by
  have hN : (1 : ℝ≥0) ≤ N + 1 := by exact_mod_cast (show 1 ≤ N + 1 by omega)
  have hsum := sum_le_sum (s := (univ : Finset I)) (fun i _ ↦
    mul_le_mul' (pow_le_pow_right₀ (by norm_num : (1 : ℝ≥0) ≤ 2) (horder i))
      (pow_le_pow_right₀ hN (show 3 * order i ≤ 6 * q by have hi := horder i; omega)))
  simpa only [sourceCrudeWitnessCount, sum_const, card_univ, nsmul_eq_mul, mul_assoc] using hsum

theorem sourceCrudeUniformWitnessFactor_linear (q h : ℕ) :
    h * (2 : ℝ≥0) ^ q ≤ sourceCrudeUniformWitnessFactor q h :=
  (le_add_of_nonneg_right zero_le).trans (le_add_of_nonneg_right zero_le)

theorem sourceCrudeUniformWitnessFactor_common (q h : ℕ) :
    (h : ℝ≥0) ^ 2 * (q + 1 : ℝ≥0) ≤ sourceCrudeUniformWitnessFactor q h :=
  (le_add_of_nonneg_left zero_le).trans (le_add_of_nonneg_right zero_le)

theorem sourceCrudeUniformWitnessFactor_gain (q h : ℕ) :
    (h : ℝ≥0) ^ 2 * (2 : ℝ≥0) ^ q ≤ sourceCrudeUniformWitnessFactor q h :=
  le_add_of_nonneg_left zero_le

theorem sourceCrudeWitnessCount_le_uniform
    {I : Type*} [Fintype I] (order : I → ℕ) (q N h : ℕ)
    (horder : ∀ i, order i ≤ q) (hcard : Fintype.card I ≤ h) :
    sourceCrudeWitnessCount order N ≤ sourceCrudeUniformWitnessFactor q h * (N + 1 : ℝ≥0) ^ (6 * q) := by
  have hcard' : (Fintype.card I : ℝ≥0) ≤ h := by exact_mod_cast hcard
  refine (sourceCrudeWitnessCount_le order q N horder).trans ?_
  apply mul_le_mul_of_nonneg_right _ zero_le
  exact (mul_le_mul_of_nonneg_right hcard' zero_le).trans (sourceCrudeUniformWitnessFactor_linear q h)

theorem boundedIntersectionMomentCoefficient_mono_order (d q s : ℕ) (hd : d ≤ q) :
    boundedIntersectionMomentCoefficient d s ≤ boundedIntersectionMomentCoefficient q s := by
  unfold boundedIntersectionMomentCoefficient
  apply Nat.mul_le_mul (by omega)
  exact (Nat.pow_le_pow_left (by nlinarith : s * d + 1 ≤ s * q + 1) d).trans
    (Nat.pow_le_pow_right (by omega) hd)

theorem ambient_add_one_power_le (N R e : ℕ) (t : ℝ≥0) (ht : 1 ≤ t)
    (hN : (N : ℝ≥0) ≤ t ^ R) :
    (N + 1 : ℝ≥0) ^ e ≤ (2 : ℝ≥0) ^ e * t ^ (R * e) := by
  have hbase : (N + 1 : ℝ≥0) ≤ 2 * t ^ R := by
    calc
      _ ≤ t ^ R + t ^ R := add_le_add hN (one_le_pow₀ ht)
      _ = _ := by ring
  simpa only [mul_pow, ← pow_mul] using pow_le_pow_left' hbase e

theorem card_crudeStatisticIndex_power_bound
    (V : Type*) [Fintype V] [DecidableEq V] (q R : ℕ) (t : ℝ≥0)
    (ht : 1 ≤ t) (hN : (Fintype.card V : ℝ≥0) ≤ t ^ R) :
    (Fintype.card (CrudeStatisticIndex V q) : ℝ≥0) ≤
      (256 * (q + 1 : ℝ≥0) ^ 2) * t ^ (6 * R) := by
  have hcard : (Fintype.card (CrudeStatisticIndex V q) : ℝ≥0) ≤
      4 * (q + 1 : ℝ≥0) ^ 2 * (Fintype.card V + 1 : ℝ≥0) ^ 6 := by
    exact_mod_cast card_crudeStatisticIndex_le_polynomial V q
  have hpow := ambient_add_one_power_le (Fintype.card V) R 6 t ht hN
  calc
    _ ≤ 4 * (q + 1 : ℝ≥0) ^ 2 * ((2 : ℝ≥0) ^ 6 * t ^ (R * 6)) :=
      hcard.trans (mul_le_mul_of_nonneg_left hpow zero_le)
    _ = _ := by rw [Nat.mul_comm R 6]; ring

end

end Erdos207
