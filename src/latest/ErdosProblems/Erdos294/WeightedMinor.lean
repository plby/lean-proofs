/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos294.WeightedMajor
import UnitFractions.MainResults

/-!
# Weighted minor-arc estimates for Erdős Problem 294

This file reuses the local prime-power classes and the common-nearby-multiple
condition from the unit-fraction library.  The estimates differ from the
older `p = 1/2` argument only in keeping the Bernoulli variance as an
explicit positive constant.
-/

open scoped BigOperators ArithmeticFunction.omega

namespace Erdos294.WeightedMinor

open Complex Finset Real
open UnitFractions
open Erdos297
open Erdos294.WeightedMajor

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Nearest integral representative of `h` modulo `n`. -/
def centeredResidue (h : ℤ) (n : ℕ) : ℤ :=
  h - (n : ℤ) * round ((h : ℝ) / n)

def residueMagnitude (h : ℤ) (n : ℕ) : ℝ :=
  |(centeredResidue h n : ℝ)|

lemma circleDistance_int_div_nat {h : ℤ} {n : ℕ} (hn : 0 < n) :
    circleDistance ((h : ℝ) / n) = residueMagnitude h n / n := by
  rw [circleDistance_eq_round]
  unfold residueMagnitude centeredResidue
  rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [show (h : ℝ) / n - round ((h : ℝ) / n) =
      ((h : ℝ) - n * round ((h : ℝ) / n)) / n by field_simp]
  rw [abs_div, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ))]

lemma centeredResidue_emod (h : ℤ) {n : ℕ} (hn : n ≠ 0) :
    centeredResidue h n % n = h % n := by
  unfold centeredResidue
  rw [Int.sub_emod]
  simp [hn]

/-- A global family of denominators with no nearby multiple forces a
quadratic amount of circle distance. -/
lemma global_distance_lower
    {A : Finset ℕ} {N : ℕ} {h : ℤ} {K T : ℝ} {I : Finset ℤ}
    (hA0 : 0 ∉ A) (hAN : ∀ n ∈ A, n ≤ N) (hK : 0 < K)
    (hI : I = Finset.Icc ⌈(h : ℝ) - K / 2⌉ ⌊(h : ℝ) + K / 2⌋)
    (hmissing : T ≤ ((A.filter fun n : ℕ ↦ ∀ x ∈ I, ¬ ((n : ℤ) ∣ x)).card : ℝ)) :
    T * (K ^ 2 / (4 * N ^ 2)) ≤
      ∑ n ∈ A, circleDistance ((h : ℝ) / n) ^ 2 := by
  let r : ℕ → ℤ := fun n ↦ centeredResidue h n
  have hrmod : ∀ n ∈ A, r n % (n : ℤ) = h % (n : ℤ) := by
    intro n hn
    exact centeredResidue_emod h (ne_of_mem_of_not_mem hn hA0)
  have hsum := missing_bridge_sum (A := A) (t := h) (K := K) (M := T)
    (I := I) (tn := r) hK hI hrmod hmissing
  by_cases hN0 : N = 0
  · have hAempty : A = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have hn0 := ne_of_mem_of_not_mem hn hA0
      have := hAN n hn
      omega
    subst N
    simp [hAempty]
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
  have hpoint : ∀ n ∈ A,
      (r n : ℝ) ^ 2 / (N : ℝ) ^ 2 ≤ circleDistance ((h : ℝ) / n) ^ 2 := by
    intro n hn
    have hn0 : 0 < n := Nat.pos_of_ne_zero (ne_of_mem_of_not_mem hn hA0)
    rw [circleDistance_int_div_nat hn0]
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast hAN n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
    unfold residueMagnitude r
    rw [div_pow, sq_abs]
    exact div_le_div_of_nonneg_left (sq_nonneg _)
      (sq_pos_of_pos hnR) (pow_le_pow_left₀ hnR.le hnN 2)
  calc
    T * (K ^ 2 / (4 * N ^ 2)) =
        (T * (K ^ 2 / 4)) / (N : ℝ) ^ 2 := by ring
    _ ≤ (∑ n ∈ A, (r n : ℝ) ^ 2) / (N : ℝ) ^ 2 := by
      gcongr
    _ = ∑ n ∈ A, (r n : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
      rw [Finset.sum_div]
    _ ≤ ∑ n ∈ A, circleDistance ((h : ℝ) / n) ^ 2 := by
      exact Finset.sum_le_sum fun n hn ↦ hpoint n hn

lemma weighted_product_global_bound
    {A : Finset ℕ} {N : ℕ} {p : ℕ → ℝ} {h : ℤ}
    {K T δ : ℝ} {I : Finset ℤ}
    (hA0 : 0 ∉ A) (hAN : ∀ n ∈ A, n ≤ N)
    (hp0 : ∀ n ∈ A, 0 ≤ p n) (hp1 : ∀ n ∈ A, p n ≤ 1)
    (hvar : ∀ n ∈ A, δ ≤ p n * (1 - p n)) (hδ : 0 ≤ δ)
    (hK : 0 < K)
    (hI : I = Finset.Icc ⌈(h : ℝ) - K / 2⌉ ⌊(h : ℝ) + K / 2⌋)
    (hmissing : T ≤ ((A.filter fun n : ℕ ↦ ∀ x ∈ I, ¬ ((n : ℤ) ∣ x)).card : ℝ)) :
    ‖∏ n ∈ A, bernoulliFactor (p n) ((h : ℝ) / n)‖ ≤
      Real.exp (-(8 * δ * T * K ^ 2 / (4 * N ^ 2))) := by
  have hbase := bernoulliFactor_prod_norm_le_exp A p
    (fun n ↦ (h : ℝ) / n) hp0 hp1
  apply hbase.trans
  apply Real.exp_le_exp.mpr
  have hdist := global_distance_lower hA0 hAN hK hI hmissing
  have hsum : δ * ∑ n ∈ A, circleDistance ((h : ℝ) / n) ^ 2 ≤
      ∑ n ∈ A, p n * (1 - p n) * circleDistance ((h : ℝ) / n) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun n hn ↦
      mul_le_mul_of_nonneg_right (hvar n hn) (sq_nonneg _)
  have hchain :
      8 * δ * (T * (K ^ 2 / (4 * N ^ 2))) ≤
        8 * ∑ n ∈ A,
          p n * (1 - p n) * circleDistance ((h : ℝ) / n) ^ 2 := by
    calc
      8 * δ * (T * (K ^ 2 / (4 * N ^ 2))) ≤
          8 * δ * ∑ n ∈ A, circleDistance ((h : ℝ) / n) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hdist (mul_nonneg (by norm_num) hδ)
      _ ≤ 8 * ∑ n ∈ A,
          p n * (1 - p n) * circleDistance ((h : ℝ) / n) ^ 2 := by
        simpa [mul_assoc] using
          (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 8))
  calc
    -(8 * ∑ n ∈ A,
        p n * (1 - p n) * circleDistance ((h : ℝ) / n) ^ 2) ≤
        -(8 * δ * (T * (K ^ 2 / (4 * N ^ 2)))) := neg_le_neg hchain
    _ = -(8 * δ * T * K ^ 2 / (4 * N ^ 2)) := by ring

/-- Re-indexing the local prime-power classes. -/
lemma sum_local_squares_eq
    (A Q : Finset ℕ) (r : ℕ → ℝ) :
    ∑ q ∈ Q, ∑ n ∈ local_part A q, r n =
      ∑ n ∈ A, ((Q.filter fun q ↦ n ∈ local_part A q).card : ℝ) * r n := by
  change
    ∑ q ∈ Q, ∑ n ∈ A.filter (fun n ↦ q ∣ n ∧ Nat.Coprime q (n / q)), r n = _
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    ∑ q ∈ Q, (if q ∣ n ∧ Nat.Coprime q (n / q) then r n else 0) =
        ∑ _q ∈ Q.filter (fun q ↦ q ∣ n ∧ Nat.Coprime q (n / q)), r n := by
      rw [Finset.sum_filter]
    _ = ((Q.filter fun q ↦ n ∈ local_part A q).card : ℝ) * r n := by
      have heq : Q.filter (fun q ↦ q ∣ n ∧ Nat.Coprime q (n / q)) =
          Q.filter (fun q ↦ n ∈ local_part A q) := by
        ext q
        simp [local_part, hn]
      rw [heq]
      simp [nsmul_eq_mul]

/-- Missing exact prime-power classes force quadratic distance, with `F`
accounting for how many classes can contain one denominator. -/
lemma local_distance_lower
    {A D : Finset ℕ} {N F : ℕ} {h : ℤ} {K L S : ℝ} {I : Finset ℤ}
    (hA0 : 0 ∉ A) (hAN : ∀ n ∈ A, n ≤ N)
    (hK : 0 < K) (hL : 0 ≤ L) (hS : 0 < S)
    (hI : I = Finset.Icc ⌈(h : ℝ) - K / 2⌉ ⌊(h : ℝ) + K / 2⌋)
    (hD : D ⊆ ppowers_in_set A)
    (hqS : ∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ S)
    (hrare : ∀ q ∈ D,
      L / q ≤ (((local_part A q).filter fun n : ℕ ↦
        ∀ x ∈ I, ¬ ((n : ℤ) ∣ x)).card : ℝ))
    (hfac : ∀ n ∈ A,
      ((ppowers_in_set A).filter fun q ↦ n ∈ local_part A q).card ≤ F)
    (hF : 0 < F) :
    ((D.card : ℝ) * (L / S) * K ^ 2 / 4) / (F * (N : ℝ) ^ 2) ≤
      ∑ n ∈ A, circleDistance ((h : ℝ) / n) ^ 2 := by
  by_cases hN0 : N = 0
  · have hAempty : A = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have hn0 := ne_of_mem_of_not_mem hn hA0
      have := hAN n hn
      omega
    have hDempty : D = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      have := hD hq
      simp [hAempty] at this
    subst N
    simp [hAempty, hDempty]
  let rZ : ℕ → ℤ := fun n ↦ centeredResidue h n
  let r : ℕ → ℝ := fun n ↦ (rZ n : ℝ) ^ 2
  have hrmod : ∀ n ∈ A, rZ n % (n : ℤ) = h % (n : ℤ) := by
    intro n hn
    exact centeredResidue_emod h (ne_of_mem_of_not_mem hn hA0)
  have hqsum : ∀ q ∈ D,
      (L / S) * (K ^ 2 / 4) ≤ ∑ n ∈ local_part A q, r n := by
    intro q hq
    calc
      (L / S) * (K ^ 2 / 4) ≤ (L / q) * (K ^ 2 / 4) := by
        have hqpos : (0 : ℝ) < q := by
          exact_mod_cast (mem_ppowers_in_set.mp (hD hq)).1.pos
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left hL hqpos (hqS q (hD hq))) (by positivity)
      _ ≤ ∑ n ∈ local_part A q, r n := by
        apply missing_bridge_sum (A := local_part A q) (t := h) (K := K)
          (M := L / q) (I := I) (tn := rZ) hK hI
        · intro n hn
          exact hrmod n (local_part_subset hn)
        · exact hrare q hq
  have hsumlower : (D.card : ℝ) * (L / S) * (K ^ 2 / 4) ≤
      ∑ q ∈ D, ∑ n ∈ local_part A q, r n := by
    calc
      (D.card : ℝ) * (L / S) * (K ^ 2 / 4) =
          ∑ _q ∈ D, (L / S) * (K ^ 2 / 4) := by
        simp
        ring
      _ ≤ ∑ q ∈ D, ∑ n ∈ local_part A q, r n :=
        Finset.sum_le_sum fun q hq ↦ hqsum q hq
  have hweightedUpper :
      ∑ q ∈ D, ∑ n ∈ local_part A q, r n ≤
        (F : ℝ) * ∑ n ∈ A, r n := by
    calc
      ∑ q ∈ D, ∑ n ∈ local_part A q, r n ≤
          ∑ q ∈ ppowers_in_set A, ∑ n ∈ local_part A q, r n := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hD (fun q hq hnot ↦
          Finset.sum_nonneg fun n hn ↦ sq_nonneg _)
      _ = ∑ n ∈ A,
          (((ppowers_in_set A).filter fun q ↦ n ∈ local_part A q).card : ℝ) * r n :=
        sum_local_squares_eq A (ppowers_in_set A) r
      _ ≤ ∑ n ∈ A, (F : ℝ) * r n := by
        apply Finset.sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfac n hn) (sq_nonneg _)
      _ = (F : ℝ) * ∑ n ∈ A, r n := by rw [Finset.mul_sum]
  have hrsum :
      ((D.card : ℝ) * (L / S) * (K ^ 2 / 4)) / F ≤ ∑ n ∈ A, r n := by
    have hFR : (0 : ℝ) < F := by exact_mod_cast hF
    rw [div_le_iff₀ hFR]
    calc
      (D.card : ℝ) * (L / S) * (K ^ 2 / 4) ≤
          ∑ q ∈ D, ∑ n ∈ local_part A q, r n := hsumlower
      _ ≤ (F : ℝ) * ∑ n ∈ A, r n := hweightedUpper
      _ = (∑ n ∈ A, r n) * (F : ℝ) := by ring
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
  have hpoint : ∀ n ∈ A,
      r n / (N : ℝ) ^ 2 ≤ circleDistance ((h : ℝ) / n) ^ 2 := by
    intro n hn
    have hn0 : 0 < n := Nat.pos_of_ne_zero (ne_of_mem_of_not_mem hn hA0)
    rw [circleDistance_int_div_nat hn0]
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast hAN n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    unfold residueMagnitude r rZ
    rw [div_pow, sq_abs]
    exact div_le_div_of_nonneg_left (sq_nonneg _)
      (sq_pos_of_pos hnR) (pow_le_pow_left₀ hnR.le hnN 2)
  calc
    ((D.card : ℝ) * (L / S) * K ^ 2 / 4) / (F * (N : ℝ) ^ 2) =
        (((D.card : ℝ) * (L / S) * (K ^ 2 / 4)) / F) /
          (N : ℝ) ^ 2 := by ring
    _ ≤ (∑ n ∈ A, r n) / (N : ℝ) ^ 2 := by gcongr
    _ = ∑ n ∈ A, r n / (N : ℝ) ^ 2 := by rw [Finset.sum_div]
    _ ≤ ∑ n ∈ A, circleDistance ((h : ℝ) / n) ^ 2 :=
      Finset.sum_le_sum fun n hn ↦ hpoint n hn

lemma weighted_product_local_bound
    {A D : Finset ℕ} {N F : ℕ} {p : ℕ → ℝ} {h : ℤ}
    {K L S δ : ℝ} {I : Finset ℤ}
    (hA0 : 0 ∉ A) (hAN : ∀ n ∈ A, n ≤ N)
    (hp0 : ∀ n ∈ A, 0 ≤ p n) (hp1 : ∀ n ∈ A, p n ≤ 1)
    (hvar : ∀ n ∈ A, δ ≤ p n * (1 - p n)) (hδ : 0 ≤ δ)
    (hK : 0 < K) (hL : 0 ≤ L) (hS : 0 < S)
    (hI : I = Finset.Icc ⌈(h : ℝ) - K / 2⌉ ⌊(h : ℝ) + K / 2⌋)
    (hD : D ⊆ ppowers_in_set A)
    (hqS : ∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ S)
    (hrare : ∀ q ∈ D,
      L / q ≤ (((local_part A q).filter fun n : ℕ ↦
        ∀ x ∈ I, ¬ ((n : ℤ) ∣ x)).card : ℝ))
    (hfac : ∀ n ∈ A,
      ((ppowers_in_set A).filter fun q ↦ n ∈ local_part A q).card ≤ F)
    (hF : 0 < F) :
    ‖∏ n ∈ A, bernoulliFactor (p n) ((h : ℝ) / n)‖ ≤
      Real.exp (-(8 * δ *
        (((D.card : ℝ) * (L / S) * K ^ 2 / 4) /
          (F * (N : ℝ) ^ 2)))) := by
  have hbase := bernoulliFactor_prod_norm_le_exp A p
    (fun n ↦ (h : ℝ) / n) hp0 hp1
  apply hbase.trans
  apply Real.exp_le_exp.mpr
  have hdist := local_distance_lower hA0 hAN hK hL hS hI hD hqS hrare hfac hF
  have hsum : δ * ∑ n ∈ A, circleDistance ((h : ℝ) / n) ^ 2 ≤
      ∑ n ∈ A, p n * (1 - p n) * circleDistance ((h : ℝ) / n) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun n hn ↦
      mul_le_mul_of_nonneg_right (hvar n hn) (sq_nonneg _)
  have hchain :
      8 * δ * (((D.card : ℝ) * (L / S) * K ^ 2 / 4) /
          (F * (N : ℝ) ^ 2)) ≤
        8 * ∑ n ∈ A,
          p n * (1 - p n) * circleDistance ((h : ℝ) / n) ^ 2 := by
    calc
      8 * δ * (((D.card : ℝ) * (L / S) * K ^ 2 / 4) /
          (F * (N : ℝ) ^ 2)) ≤
          8 * δ * ∑ n ∈ A, circleDistance ((h : ℝ) / n) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hdist (mul_nonneg (by norm_num) hδ)
      _ ≤ 8 * ∑ n ∈ A,
          p n * (1 - p n) * circleDistance ((h : ℝ) / n) ^ 2 := by
        simpa [mul_assoc] using
          (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 8))
  exact neg_le_neg hchain

end

end Erdos294.WeightedMinor
