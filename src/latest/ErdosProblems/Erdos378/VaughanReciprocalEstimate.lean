/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.ReciprocalCorrelationEstimate
import BoundedGaps.BombieriVinogradov.Analytic.GranvilleRamarePrefix

/-!
# Vaughan's fourth term for a reciprocal phase

This file combines the uniform reciprocal correlation estimate with the two
coefficient-energy estimates in Vaughan's identity.  The cutoff coefficients
are deliberately kept in the statements, so the estimates apply directly to
the padded rectangles from `VaughanReciprocalBlocks`.
-/

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace Erdos378
namespace VaughanReciprocalEstimate

open BoundedGaps.Maynard
open PrimeReciprocal
open BilinearReciprocal
open ReciprocalCorrelationEstimate
open VaughanReciprocalBlocks

noncomputable section

noncomputable def reciprocalCorrelationRootConstant : ℝ :=
  reciprocalCorrelationUniformConstant ^ (16 : ℝ)⁻¹

lemma reciprocalCorrelationRootConstant_nonneg :
  0 ≤ reciprocalCorrelationRootConstant := by
  unfold reciprocalCorrelationRootConstant
  exact Real.rpow_nonneg reciprocalCorrelationUniformConstant_pos.le _

lemma reciprocalCorrelationBound_eq_rpow (M : ℕ) :
    reciprocalCorrelationBound M =
      reciprocalCorrelationRootConstant * (M : ℝ) ^ (7 / 8 : ℝ) := by
  unfold reciprocalCorrelationBound reciprocalCorrelationRootConstant
  rw [Real.mul_rpow reciprocalCorrelationUniformConstant_pos.le (by positivity)]
  congr 1
  rw [show ((M : ℝ) ^ 14) = (M : ℝ) ^ (14 : ℝ) by
    exact (Real.rpow_natCast (M : ℝ) 14).symm]
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ M)]
  norm_num

lemma reciprocalVaughanBlock_eq_zero_of_product_above
    (X U V : ℝ) (x y M K : ℕ) (hy : y < M * K) :
    reciprocalBilinearBlock X x y M (2 * M) K (2 * K)
      (cutoffMangoldtCoefficient U) (cutoffFourthCoefficient V) = 0 := by
  unfold reciprocalBilinearBlock
  apply Finset.sum_eq_zero
  intro m hm
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro k hk
  apply mul_eq_zero_of_right
  unfold reciprocalCutoffWeight
  rw [if_neg]
  intro hactive
  have hmlo := (Finset.mem_Ioc.mp hm).1
  have hklo := (Finset.mem_Ioc.mp hk).1
  have hprod : M * K < m * k := by
    calc
      M * K ≤ m * K := Nat.mul_le_mul_right K hmlo.le
      _ < m * k := Nat.mul_lt_mul_of_pos_left hklo (by omega)
  exact (not_le_of_gt (hy.trans hprod)) hactive.2

lemma reciprocalVaughanBlock_eq_zero_of_product_below
    (X U V : ℝ) (x y M K : ℕ) (hx : 4 * M * K ≤ x) :
    reciprocalBilinearBlock X x y M (2 * M) K (2 * K)
      (cutoffMangoldtCoefficient U) (cutoffFourthCoefficient V) = 0 := by
  unfold reciprocalBilinearBlock
  apply Finset.sum_eq_zero
  intro m hm
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro k hk
  apply mul_eq_zero_of_right
  unfold reciprocalCutoffWeight
  rw [if_neg]
  intro hactive
  have hmhi := (Finset.mem_Ioc.mp hm).2
  have hkhi := (Finset.mem_Ioc.mp hk).2
  nlinarith

lemma reciprocalVaughanBlock_eq_zero_of_mangoldt_cutoff
    (X U V : ℝ) (x y M K : ℕ) (hU : (2 * M : ℕ) ≤ U) :
    reciprocalBilinearBlock X x y M (2 * M) K (2 * K)
      (cutoffMangoldtCoefficient U) (cutoffFourthCoefficient V) = 0 := by
  unfold reciprocalBilinearBlock
  apply Finset.sum_eq_zero
  intro m hm
  apply mul_eq_zero_of_left
  unfold cutoffMangoldtCoefficient
  rw [if_neg]
  have hmhiR : (m : ℝ) ≤ (2 * M : ℕ) := by
    exact_mod_cast (Finset.mem_Ioc.mp hm).2
  exact not_lt_of_ge (hmhiR.trans hU)

lemma reciprocalVaughanBlock_eq_zero_of_fourth_cutoff
    (X U V : ℝ) (x y M K : ℕ) (hV : (2 * K : ℕ) ≤ V) :
    reciprocalBilinearBlock X x y M (2 * M) K (2 * K)
      (cutoffMangoldtCoefficient U) (cutoffFourthCoefficient V) = 0 := by
  unfold reciprocalBilinearBlock
  apply Finset.sum_eq_zero
  intro m hm
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro k hk
  apply mul_eq_zero_of_left
  unfold cutoffFourthCoefficient
  rw [if_neg]
  have hkhiR : (k : ℝ) ≤ (2 * K : ℕ) := by
    exact_mod_cast (Finset.mem_Ioc.mp hk).2
  exact not_lt_of_ge (hkhiR.trans hV)

lemma norm_cutoffMangoldtCoefficient_sq_le
    {U : ℝ} {M m : ℕ} (hm : m ∈ Finset.Ioc M (2 * M)) :
    ‖cutoffMangoldtCoefficient U m‖ ^ 2 ≤
      (Real.log (2 * (M : ℝ))) ^ 2 := by
  have hmPos : 0 < m := by
    have hMpos : 0 < M := by
      by_contra h
      simp only [Nat.not_lt] at h
      have : M = 0 := Nat.eq_zero_of_le_zero h
      subst M
      simp at hm
    exact hMpos.trans (Finset.mem_Ioc.mp hm).1
  have hmUpperNat : m ≤ 2 * M := (Finset.mem_Ioc.mp hm).2
  have hmUpper : (m : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast hmUpperNat
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hmPos
  by_cases hU : U < (m : ℝ)
  · rw [cutoffMangoldtCoefficient, if_pos hU, Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact pow_le_pow_left₀ ArithmeticFunction.vonMangoldt_nonneg
      (ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log hmReal hmUpper)) 2
  · simp [cutoffMangoldtCoefficient, hU, sq_nonneg]

theorem sum_norm_sq_cutoffMangoldtCoefficient_Ioc_le
    (U : ℝ) (M : ℕ) :
    (∑ m ∈ Finset.Ioc M (2 * M),
      ‖cutoffMangoldtCoefficient U m‖ ^ 2) ≤
      (M : ℝ) * (Real.log (2 * (M : ℝ))) ^ 2 := by
  have hcard : (Finset.Ioc M (2 * M)).card = M := by
    simp only [Nat.card_Ioc]
    omega
  calc
    (∑ m ∈ Finset.Ioc M (2 * M),
        ‖cutoffMangoldtCoefficient U m‖ ^ 2) ≤
        ∑ _m ∈ Finset.Ioc M (2 * M),
          (Real.log (2 * (M : ℝ))) ^ 2 := by
      apply Finset.sum_le_sum
      intro m hm
      exact norm_cutoffMangoldtCoefficient_sq_le hm
    _ = (M : ℝ) * (Real.log (2 * (M : ℝ))) ^ 2 := by
      rw [Finset.sum_const, hcard]
      simp

theorem sum_norm_sq_cutoffFourthCoefficient_Ioc_le
    {V : ℝ} (hV : 1 ≤ V) (K : ℕ) :
    (∑ k ∈ Finset.Ioc K (2 * K),
      ‖cutoffFourthCoefficient V k‖ ^ 2) ≤
      (8 / 3 : ℝ) * (K : ℝ) * (Real.log V + 3) ^ 2 := by
  have hprefix := sum_sq_vaughanFourthCoefficient_prefix_le hV (2 * K)
  calc
    (∑ k ∈ Finset.Ioc K (2 * K),
        ‖cutoffFourthCoefficient V k‖ ^ 2) ≤
        ∑ k ∈ Finset.Ioc K (2 * K),
          (vaughanFourthCoefficient V k) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hkV : V < (k : ℝ)
      · rw [cutoffFourthCoefficient, if_pos hkV, Complex.norm_real,
          Real.norm_eq_abs, sq_abs]
      · simp [cutoffFourthCoefficient, hkV, sq_nonneg]
    _ ≤
        ∑ k ∈ Finset.Ioc 0 (2 * K),
          (vaughanFourthCoefficient V k) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        exact Finset.mem_Ioc.mpr ⟨Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hk).1,
          (Finset.mem_Ioc.mp hk).2⟩
      · intro k hk _hkNot
        exact sq_nonneg _
    _ ≤ (4 / 3 : ℝ) * ((2 * K : ℕ) : ℝ) *
          (Real.log V + 3) ^ 2 := hprefix
    _ = (8 / 3 : ℝ) * (K : ℝ) * (Real.log V + 3) ^ 2 := by
      push_cast
      ring

lemma sum_norm_cutoffFourthCoefficient_Ioc_sq_le
    {V : ℝ} {K : ℕ} (hV : 1 ≤ V) :
    (∑ k ∈ Finset.Ioc K (2 * K),
      ‖cutoffFourthCoefficient V k‖) ^ 2 ≤
      (K : ℝ) * ((8 / 3 : ℝ) * (K : ℝ) *
        (Real.log V + 3) ^ 2) := by
  have hcs := norm_sum_mul_sq_le (Finset.Ioc K (2 * K))
    (fun _k : ℕ ↦ (1 : ℂ)) (fun k ↦ cutoffFourthCoefficient V k)
  have hcard : (Finset.Ioc K (2 * K)).card = K := by
    simp only [Nat.card_Ioc]
    omega
  have henergy := sum_norm_sq_cutoffFourthCoefficient_Ioc_le hV K
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.Ioc K (2 * K)) (fun _k : ℕ ↦ (1 : ℝ))
      (fun k ↦ ‖cutoffFourthCoefficient V k‖)
  calc
    (∑ k ∈ Finset.Ioc K (2 * K),
        ‖cutoffFourthCoefficient V k‖) ^ 2 ≤
        (K : ℝ) * (∑ k ∈ Finset.Ioc K (2 * K),
          ‖cutoffFourthCoefficient V k‖ ^ 2) := by
      simpa [hcard] using hcauchy
    _ ≤ (K : ℝ) * ((8 / 3 : ℝ) * (K : ℝ) *
          (Real.log V + 3) ^ 2) := by
      gcongr

lemma sum_norm_cutoffMangoldtCoefficient_Ioc_sq_le
    {U : ℝ} {M : ℕ} :
    (∑ m ∈ Finset.Ioc M (2 * M),
      ‖cutoffMangoldtCoefficient U m‖) ^ 2 ≤
      (M : ℝ) * ((M : ℝ) *
        (Real.log (2 * (M : ℝ))) ^ 2) := by
  have hcard : (Finset.Ioc M (2 * M)).card = M := by
    simp only [Nat.card_Ioc]
    omega
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.Ioc M (2 * M)) (fun _m : ℕ ↦ (1 : ℝ))
      (fun m ↦ ‖cutoffMangoldtCoefficient U m‖)
  have henergy := sum_norm_sq_cutoffMangoldtCoefficient_Ioc_le U M
  calc
    (∑ m ∈ Finset.Ioc M (2 * M),
        ‖cutoffMangoldtCoefficient U m‖) ^ 2 ≤
        (M : ℝ) * (∑ m ∈ Finset.Ioc M (2 * M),
          ‖cutoffMangoldtCoefficient U m‖ ^ 2) := by
      simpa [hcard] using hcauchy
    _ ≤ (M : ℝ) * ((M : ℝ) *
          (Real.log (2 * (M : ℝ))) ^ 2) := by
      gcongr

/-- Explicit block majorant when the Mangoldt scale is the longer scale. -/
theorem norm_reciprocalVaughanBlock_sq_le_of_fourth_le_mangoldt
    {X U V : ℝ} {x y M K : ℕ}
    (hV : 1 ≤ V) (hM : 16384 ≤ M) (hK : 0 < K) (hKM : K ≤ M)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 2) (hyx : y ≤ 2 * x) :
    ‖reciprocalBilinearBlock X x y M (2 * M) K (2 * K)
        (cutoffMangoldtCoefficient U) (cutoffFourthCoefficient V)‖ ^ 2 ≤
      (8 / 3 : ℝ) * (M : ℝ) * (K : ℝ) *
        (Real.log (2 * (M : ℝ))) ^ 2 * (Real.log V + 3) ^ 2 *
          ((M : ℝ) + reciprocalCorrelationBound M * (K : ℝ)) := by
  let EA := (M : ℝ) * (Real.log (2 * (M : ℝ))) ^ 2
  let EB := (8 / 3 : ℝ) * (K : ℝ) * (Real.log V + 3) ^ 2
  let B := reciprocalCorrelationBound M
  have hbase := norm_reciprocalBilinearBlock_sq_le_energy
    (cutoffMangoldtCoefficient U) (cutoffFourthCoefficient V)
    hM hK hKM hXlo hXhi hyx
  have hEA : (∑ m ∈ Finset.Ioc M (2 * M),
      ‖cutoffMangoldtCoefficient U m‖ ^ 2) ≤ EA := by
    exact sum_norm_sq_cutoffMangoldtCoefficient_Ioc_le U M
  have hEB : (∑ k ∈ Finset.Ioc K (2 * K),
      ‖cutoffFourthCoefficient V k‖ ^ 2) ≤ EB := by
    exact sum_norm_sq_cutoffFourthCoefficient_Ioc_le hV K
  have hL1 : (∑ k ∈ Finset.Ioc K (2 * K),
      ‖cutoffFourthCoefficient V k‖) ^ 2 ≤ (K : ℝ) * EB := by
    exact sum_norm_cutoffFourthCoefficient_Ioc_sq_le hV
  have hB : 0 ≤ B := reciprocalCorrelationBound_nonneg M
  have hEA0 : 0 ≤ EA := by dsimp only [EA]; positivity
  have hEB0 : 0 ≤ EB := by dsimp only [EB]; positivity
  have hinner :
      (M : ℝ) * (∑ k ∈ Finset.Ioc K (2 * K),
          ‖cutoffFourthCoefficient V k‖ ^ 2) +
        B * (∑ k ∈ Finset.Ioc K (2 * K),
          ‖cutoffFourthCoefficient V k‖) ^ 2 ≤
      EB * ((M : ℝ) + B * (K : ℝ)) := by
    calc
      _ ≤ (M : ℝ) * EB + B * ((K : ℝ) * EB) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hEB (by positivity))
          (mul_le_mul_of_nonneg_left hL1 hB)
      _ = EB * ((M : ℝ) + B * (K : ℝ)) := by ring
  calc
    _ ≤ (∑ m ∈ Finset.Ioc M (2 * M),
        ‖cutoffMangoldtCoefficient U m‖ ^ 2) *
        ((M : ℝ) * (∑ k ∈ Finset.Ioc K (2 * K),
          ‖cutoffFourthCoefficient V k‖ ^ 2) +
        B * (∑ k ∈ Finset.Ioc K (2 * K),
          ‖cutoffFourthCoefficient V k‖) ^ 2) := hbase
    _ ≤ EA * (EB * ((M : ℝ) + B * (K : ℝ))) := by
      apply mul_le_mul hEA hinner
      · positivity
      · exact hEA0
    _ = (8 / 3 : ℝ) * (M : ℝ) * (K : ℝ) *
        (Real.log (2 * (M : ℝ))) ^ 2 * (Real.log V + 3) ^ 2 *
          ((M : ℝ) + reciprocalCorrelationBound M * (K : ℝ)) := by
      simp only [EA, EB, B]
      ring

/-- Explicit block majorant when the fourth-coefficient scale is the longer
scale.  The exact symmetry of the product cutoff is used before applying the
correlation estimate. -/
theorem norm_reciprocalVaughanBlock_sq_le_of_mangoldt_le_fourth
    {X U V : ℝ} {x y M K : ℕ}
    (hV : 1 ≤ V) (hK : 16384 ≤ K) (hM : 0 < M) (hMK : M ≤ K)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 2) (hyx : y ≤ 2 * x) :
    ‖reciprocalBilinearBlock X x y M (2 * M) K (2 * K)
        (cutoffMangoldtCoefficient U) (cutoffFourthCoefficient V)‖ ^ 2 ≤
      (8 / 3 : ℝ) * (M : ℝ) * (K : ℝ) *
        (Real.log (2 * (M : ℝ))) ^ 2 * (Real.log V + 3) ^ 2 *
          ((K : ℝ) + reciprocalCorrelationBound K * (M : ℝ)) := by
  let EA := (M : ℝ) * (Real.log (2 * (M : ℝ))) ^ 2
  let EB := (8 / 3 : ℝ) * (K : ℝ) * (Real.log V + 3) ^ 2
  let B := reciprocalCorrelationBound K
  have hbase := norm_reciprocalBilinearBlock_sq_le_energy
    (cutoffFourthCoefficient V) (cutoffMangoldtCoefficient U)
    hK hM hMK hXlo hXhi hyx
  have hEA : (∑ m ∈ Finset.Ioc M (2 * M),
      ‖cutoffMangoldtCoefficient U m‖ ^ 2) ≤ EA := by
    exact sum_norm_sq_cutoffMangoldtCoefficient_Ioc_le U M
  have hEB : (∑ k ∈ Finset.Ioc K (2 * K),
      ‖cutoffFourthCoefficient V k‖ ^ 2) ≤ EB := by
    exact sum_norm_sq_cutoffFourthCoefficient_Ioc_le hV K
  have hL1 : (∑ m ∈ Finset.Ioc M (2 * M),
      ‖cutoffMangoldtCoefficient U m‖) ^ 2 ≤ (M : ℝ) * EA := by
    exact sum_norm_cutoffMangoldtCoefficient_Ioc_sq_le
  have hB : 0 ≤ B := reciprocalCorrelationBound_nonneg K
  have hEA0 : 0 ≤ EA := by dsimp only [EA]; positivity
  have hEB0 : 0 ≤ EB := by dsimp only [EB]; positivity
  have hinner :
      (K : ℝ) * (∑ m ∈ Finset.Ioc M (2 * M),
          ‖cutoffMangoldtCoefficient U m‖ ^ 2) +
        B * (∑ m ∈ Finset.Ioc M (2 * M),
          ‖cutoffMangoldtCoefficient U m‖) ^ 2 ≤
      EA * ((K : ℝ) + B * (M : ℝ)) := by
    calc
      _ ≤ (K : ℝ) * EA + B * ((M : ℝ) * EA) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hEA (by positivity))
          (mul_le_mul_of_nonneg_left hL1 hB)
      _ = EA * ((K : ℝ) + B * (M : ℝ)) := by ring
  rw [reciprocalBilinearBlock_comm]
  calc
    _ ≤ (∑ k ∈ Finset.Ioc K (2 * K),
        ‖cutoffFourthCoefficient V k‖ ^ 2) *
        ((K : ℝ) * (∑ m ∈ Finset.Ioc M (2 * M),
          ‖cutoffMangoldtCoefficient U m‖ ^ 2) +
        B * (∑ m ∈ Finset.Ioc M (2 * M),
          ‖cutoffMangoldtCoefficient U m‖) ^ 2) := hbase
    _ ≤ EB * (EA * ((K : ℝ) + B * (M : ℝ))) := by
      apply mul_le_mul hEB hinner
      · positivity
      · exact hEB0
    _ = (8 / 3 : ℝ) * (M : ℝ) * (K : ℝ) *
        (Real.log (2 * (M : ℝ))) ^ 2 * (Real.log V + 3) ^ 2 *
          ((K : ℝ) + reciprocalCorrelationBound K * (M : ℝ)) := by
      simp only [EA, EB, B]
      ring

noncomputable def reciprocalVaughanBlockMajorant (V : ℝ) (y T : ℕ) : ℝ :=
  (8 / 3 : ℝ) * (y : ℝ) * (Real.log (2 * (y : ℝ))) ^ 2 *
    (Real.log V + 3) ^ 2 *
      (2 * (y : ℝ) / (T : ℝ) +
        reciprocalCorrelationRootConstant *
          ((y : ℝ) / ((y : ℝ) ^ (1 / 128 : ℝ))))

lemma reciprocalVaughanBlockMajorant_nonneg
    {V : ℝ} {y T : ℕ} (hT : 0 < T) :
  0 ≤ reciprocalVaughanBlockMajorant V y T := by
  unfold reciprocalVaughanBlockMajorant
  have hC := reciprocalCorrelationRootConstant_nonneg
  have hroot : 0 ≤ (y : ℝ) ^ (1 / 128 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hlast : 0 ≤ 2 * (y : ℝ) / (T : ℝ) +
      reciprocalCorrelationRootConstant *
        ((y : ℝ) / ((y : ℝ) ^ (1 / 128 : ℝ))) := by positivity
  positivity

private lemma long_scale_rpow_lower
    {x y M K : ℕ} (hM : 16384 ≤ M) (hKM : K ≤ M)
    (hxprod : x < 4 * M * K) (hyx : y ≤ 2 * x) :
    (y : ℝ) ^ (1 / 128 : ℝ) ≤ (M : ℝ) ^ (1 / 8 : ℝ) := by
  have hMtwo : (2 : ℝ) ≤ M := by exact_mod_cast (hM.trans' (by norm_num))
  have hKMR : (K : ℝ) ≤ M := by exact_mod_cast hKM
  have hxR : (x : ℝ) < 4 * (M : ℝ) * K := by exact_mod_cast hxprod
  have hyxR : (y : ℝ) ≤ 2 * x := by exact_mod_cast hyx
  have hyM2 : (y : ℝ) ≤ 8 * (M : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hKMR (by positivity : (0 : ℝ) ≤ M)]
  have hpow14 : (8 : ℝ) ≤ (M : ℝ) ^ 14 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hMtwo 14
    norm_num at hp ⊢
    exact (by norm_num : (8 : ℝ) ≤ 16384).trans hp
  have hyM16 : (y : ℝ) ≤ (M : ℝ) ^ 16 := by
    calc
      (y : ℝ) ≤ 8 * (M : ℝ) ^ 2 := hyM2
      _ ≤ (M : ℝ) ^ 14 * (M : ℝ) ^ 2 := by gcongr
      _ = (M : ℝ) ^ 16 := by ring
  calc
    (y : ℝ) ^ (1 / 128 : ℝ) ≤
        ((M : ℝ) ^ 16) ^ (1 / 128 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hyM16 (by norm_num)
    _ = (M : ℝ) ^ (1 / 8 : ℝ) := by
      rw [show ((M : ℝ) ^ 16) = (M : ℝ) ^ (16 : ℝ) by
        exact (Real.rpow_natCast (M : ℝ) 16).symm]
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ M)]
      norm_num

private lemma active_long_scale_le
    {y M K T : ℕ} (hM : 0 < M) (hT : 0 < T) (hTK : T < 2 * K)
    (hMK : M * K ≤ y) :
    (M : ℝ) ≤ 2 * (y : ℝ) / (T : ℝ) := by
  have hTM : T * M ≤ 2 * y := by
    have hlt : T * M < (2 * K) * M :=
      Nat.mul_lt_mul_of_pos_right hTK hM
    have hle : (2 * K) * M ≤ 2 * y := by
      nlinarith
    exact hlt.le.trans hle
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  apply (le_div_iff₀ hTreal).2
  have hTMR : (T : ℝ) * (M : ℝ) ≤ 2 * (y : ℝ) := by exact_mod_cast hTM
  nlinarith

private lemma active_correlation_scale_le
    {x y M K : ℕ} (hM : 16384 ≤ M) (hKM : K ≤ M)
    (hxprod : x < 4 * M * K) (hMK : M * K ≤ y)
    (hyx : y ≤ 2 * x) :
    (M : ℝ) ^ (7 / 8 : ℝ) * (K : ℝ) ≤
      (y : ℝ) / ((y : ℝ) ^ (1 / 128 : ℝ)) := by
  have hypos : (0 : ℝ) < y := by
    have hMpos : 0 < M := by omega
    have hKpos : 0 < K := by
      by_contra hK
      simp only [Nat.not_lt] at hK
      have hzero : K = 0 := Nat.eq_zero_of_le_zero hK
      subst K
      simp at hxprod
    exact_mod_cast (Nat.mul_pos hMpos hKpos |>.trans_le hMK)
  have hroot := long_scale_rpow_lower hM hKM hxprod hyx
  have hMposR : (0 : ℝ) < M := by positivity
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have hprodR : (M : ℝ) * K ≤ y := by exact_mod_cast hMK
  have hmul :
      ((M : ℝ) ^ (7 / 8 : ℝ) * (K : ℝ)) *
          ((y : ℝ) ^ (1 / 128 : ℝ)) ≤ (y : ℝ) := by
    calc
      _ ≤ ((M : ℝ) ^ (7 / 8 : ℝ) * (K : ℝ)) *
          ((M : ℝ) ^ (1 / 8 : ℝ)) := by gcongr
      _ = (M : ℝ) * (K : ℝ) := by
        rw [show (M : ℝ) ^ (7 / 8 : ℝ) * (K : ℝ) *
            (M : ℝ) ^ (1 / 8 : ℝ) =
            ((M : ℝ) ^ (7 / 8 : ℝ) *
              (M : ℝ) ^ (1 / 8 : ℝ)) * K by ring,
          ← Real.rpow_add hMposR]
        norm_num
      _ ≤ (y : ℝ) := hprodR
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hypos _)).2 hmul

/-- Every active block with the Mangoldt scale longer is controlled by one
majorant depending only on the ambient endpoint and the common cutoff. -/
theorem norm_reciprocalVaughanBlock_sq_le_majorant_of_fourth_le_mangoldt
    {X U V : ℝ} {x y M K T : ℕ}
    (hV : 1 ≤ V) (hM : 16384 ≤ M) (hK : 0 < K) (hKM : K ≤ M)
    (hT : 0 < T) (hTK : T < 2 * K)
    (hxprod : x < 4 * M * K) (hMK : M * K ≤ y)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 2) (hyx : y ≤ 2 * x) :
    ‖reciprocalBilinearBlock X x y M (2 * M) K (2 * K)
        (cutoffMangoldtCoefficient U) (cutoffFourthCoefficient V)‖ ^ 2 ≤
      reciprocalVaughanBlockMajorant V y T := by
  have hbase := norm_reciprocalVaughanBlock_sq_le_of_fourth_le_mangoldt
    (U := U)
    hV hM hK hKM hXlo hXhi hyx
  have hMKreal : (M : ℝ) * K ≤ y := by exact_mod_cast hMK
  have hlog : Real.log (2 * (M : ℝ)) ≤ Real.log (2 * (y : ℝ)) := by
    have hMleY : M ≤ y := by
      have : 0 < K := hK
      nlinarith
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.mul_le_mul_left 2 hMleY
  have hlogM0 : 0 ≤ Real.log (2 * (M : ℝ)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    nlinarith
  have hlogY0 : 0 ≤ Real.log (2 * (y : ℝ)) := by
    apply Real.log_nonneg
    have hypos : 0 < y := by
      have : 0 < M * K := Nat.mul_pos (by omega) hK
      omega
    have : (1 : ℝ) ≤ y := by exact_mod_cast hypos
    nlinarith
  have hlong := active_long_scale_le (show 0 < M by omega) hT hTK hMK
  have hcorr := active_correlation_scale_le hM hKM hxprod hMK hyx
  rw [reciprocalCorrelationBound_eq_rpow] at hbase
  unfold reciprocalVaughanBlockMajorant
  calc
    _ ≤ (8 / 3 : ℝ) * (M : ℝ) * (K : ℝ) *
        (Real.log (2 * (M : ℝ))) ^ 2 * (Real.log V + 3) ^ 2 *
          ((M : ℝ) + reciprocalCorrelationRootConstant *
            (M : ℝ) ^ (7 / 8 : ℝ) * (K : ℝ)) := hbase
    _ ≤ (8 / 3 : ℝ) * (y : ℝ) *
        (Real.log (2 * (y : ℝ))) ^ 2 * (Real.log V + 3) ^ 2 *
          (2 * (y : ℝ) / (T : ℝ) +
            reciprocalCorrelationRootConstant *
              ((y : ℝ) / ((y : ℝ) ^ (1 / 128 : ℝ)))) := by
      have hlast :
          (M : ℝ) + reciprocalCorrelationRootConstant *
              ((M : ℝ) ^ (7 / 8 : ℝ) * (K : ℝ)) ≤
            2 * (y : ℝ) / (T : ℝ) +
              reciprocalCorrelationRootConstant *
                ((y : ℝ) / ((y : ℝ) ^ (1 / 128 : ℝ))) :=
        add_le_add hlong
          (mul_le_mul_of_nonneg_left hcorr
            reciprocalCorrelationRootConstant_nonneg)
      have hlast0 : 0 ≤ (M : ℝ) + reciprocalCorrelationRootConstant *
          ((M : ℝ) ^ (7 / 8 : ℝ) * (K : ℝ)) := by
        exact add_nonneg (by positivity) (mul_nonneg
          reciprocalCorrelationRootConstant_nonneg (by positivity))
      have hlastRight0 : 0 ≤ 2 * (y : ℝ) / (T : ℝ) +
          reciprocalCorrelationRootConstant *
            ((y : ℝ) / ((y : ℝ) ^ (1 / 128 : ℝ))) := by
        have hypos : 0 < y := by
          exact (Nat.mul_pos (by omega : 0 < M) hK).trans_le hMK
        have hyR : (0 : ℝ) ≤ y := by positivity
        have hroot : (0 : ℝ) < (y : ℝ) ^ (1 / 128 : ℝ) :=
          Real.rpow_pos_of_pos (by exact_mod_cast hypos) _
        exact add_nonneg (div_nonneg (by positivity) (by positivity))
          (mul_nonneg reciprocalCorrelationRootConstant_nonneg
            (div_nonneg hyR hroot.le))
      have hlogSq : (Real.log (2 * (M : ℝ))) ^ 2 ≤
          (Real.log (2 * (y : ℝ))) ^ 2 :=
        pow_le_pow_left₀ hlogM0 hlog 2
      calc
        _ = ((8 / 3 : ℝ) * ((M : ℝ) * (K : ℝ))) *
            (Real.log (2 * (M : ℝ))) ^ 2 * (Real.log V + 3) ^ 2 *
              ((M : ℝ) + reciprocalCorrelationRootConstant *
                ((M : ℝ) ^ (7 / 8 : ℝ) * (K : ℝ))) := by ring
        _ ≤ ((8 / 3 : ℝ) * (y : ℝ)) *
            (Real.log (2 * (M : ℝ))) ^ 2 * (Real.log V + 3) ^ 2 *
              ((M : ℝ) + reciprocalCorrelationRootConstant *
                ((M : ℝ) ^ (7 / 8 : ℝ) * (K : ℝ))) := by
          gcongr
        _ ≤ ((8 / 3 : ℝ) * (y : ℝ)) *
            (Real.log (2 * (y : ℝ))) ^ 2 * (Real.log V + 3) ^ 2 *
              ((M : ℝ) + reciprocalCorrelationRootConstant *
                ((M : ℝ) ^ (7 / 8 : ℝ) * (K : ℝ))) := by
          gcongr
        _ ≤ ((8 / 3 : ℝ) * (y : ℝ)) *
            (Real.log (2 * (y : ℝ))) ^ 2 * (Real.log V + 3) ^ 2 *
              (2 * (y : ℝ) / (T : ℝ) +
                reciprocalCorrelationRootConstant *
                  ((y : ℝ) / ((y : ℝ) ^ (1 / 128 : ℝ)))) := by
          gcongr
        _ = _ := by ring

/-- The same ambient majorant in the opposite scale orientation. -/
theorem norm_reciprocalVaughanBlock_sq_le_majorant_of_mangoldt_le_fourth
    {X U V : ℝ} {x y M K T : ℕ}
    (hV : 1 ≤ V) (hK : 16384 ≤ K) (hM : 0 < M) (hMKle : M ≤ K)
    (hT : 0 < T) (hTM : T < 2 * M)
    (hxprod : x < 4 * M * K) (hMK : M * K ≤ y)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 2) (hyx : y ≤ 2 * x) :
    ‖reciprocalBilinearBlock X x y M (2 * M) K (2 * K)
        (cutoffMangoldtCoefficient U) (cutoffFourthCoefficient V)‖ ^ 2 ≤
      reciprocalVaughanBlockMajorant V y T := by
  have hbase := norm_reciprocalVaughanBlock_sq_le_of_mangoldt_le_fourth
    (U := U) hV hK hM hMKle hXlo hXhi hyx
  have hKM : K * M ≤ y := by simpa [Nat.mul_comm] using hMK
  have hxKM : x < 4 * K * M := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hxprod
  have hlong := active_long_scale_le (show 0 < K by omega) hT hTM hKM
  have hcorr := active_correlation_scale_le hK hMKle hxKM hKM hyx
  have hMleY : M ≤ y := by
    have : 0 < K := by omega
    nlinarith
  have hlog : Real.log (2 * (M : ℝ)) ≤ Real.log (2 * (y : ℝ)) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.mul_le_mul_left 2 hMleY
  have hlogM0 : 0 ≤ Real.log (2 * (M : ℝ)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    nlinarith
  have hlogY0 : 0 ≤ Real.log (2 * (y : ℝ)) := by
    apply Real.log_nonneg
    have hypos : 0 < y := (Nat.mul_pos hM (by omega : 0 < K)).trans_le hMK
    have : (1 : ℝ) ≤ y := by exact_mod_cast hypos
    nlinarith
  have hMKreal : (M : ℝ) * K ≤ y := by exact_mod_cast hMK
  rw [reciprocalCorrelationBound_eq_rpow] at hbase
  unfold reciprocalVaughanBlockMajorant
  calc
    _ ≤ (8 / 3 : ℝ) * (M : ℝ) * (K : ℝ) *
        (Real.log (2 * (M : ℝ))) ^ 2 * (Real.log V + 3) ^ 2 *
          ((K : ℝ) + reciprocalCorrelationRootConstant *
            (K : ℝ) ^ (7 / 8 : ℝ) * (M : ℝ)) := hbase
    _ ≤ (8 / 3 : ℝ) * (y : ℝ) *
        (Real.log (2 * (y : ℝ))) ^ 2 * (Real.log V + 3) ^ 2 *
          (2 * (y : ℝ) / (T : ℝ) +
            reciprocalCorrelationRootConstant *
              ((y : ℝ) / ((y : ℝ) ^ (1 / 128 : ℝ)))) := by
      have hlast :
          (K : ℝ) + reciprocalCorrelationRootConstant *
              ((K : ℝ) ^ (7 / 8 : ℝ) * (M : ℝ)) ≤
            2 * (y : ℝ) / (T : ℝ) +
              reciprocalCorrelationRootConstant *
                ((y : ℝ) / ((y : ℝ) ^ (1 / 128 : ℝ))) :=
        add_le_add hlong
          (mul_le_mul_of_nonneg_left hcorr
            reciprocalCorrelationRootConstant_nonneg)
      have hlast0 : 0 ≤ (K : ℝ) + reciprocalCorrelationRootConstant *
          ((K : ℝ) ^ (7 / 8 : ℝ) * (M : ℝ)) := by
        exact add_nonneg (by positivity) (mul_nonneg
          reciprocalCorrelationRootConstant_nonneg (by positivity))
      have hlastRight0 : 0 ≤ 2 * (y : ℝ) / (T : ℝ) +
          reciprocalCorrelationRootConstant *
            ((y : ℝ) / ((y : ℝ) ^ (1 / 128 : ℝ))) := by
        have hypos : 0 < y := (Nat.mul_pos hM (by omega : 0 < K)).trans_le hMK
        have hyR : (0 : ℝ) ≤ y := by positivity
        have hroot : (0 : ℝ) < (y : ℝ) ^ (1 / 128 : ℝ) :=
          Real.rpow_pos_of_pos (by exact_mod_cast hypos) _
        exact add_nonneg (div_nonneg (by positivity) (by positivity))
          (mul_nonneg reciprocalCorrelationRootConstant_nonneg
            (div_nonneg hyR hroot.le))
      have hlogSq : (Real.log (2 * (M : ℝ))) ^ 2 ≤
          (Real.log (2 * (y : ℝ))) ^ 2 :=
        pow_le_pow_left₀ hlogM0 hlog 2
      calc
        _ = ((8 / 3 : ℝ) * ((M : ℝ) * (K : ℝ))) *
            (Real.log (2 * (M : ℝ))) ^ 2 * (Real.log V + 3) ^ 2 *
              ((K : ℝ) + reciprocalCorrelationRootConstant *
                ((K : ℝ) ^ (7 / 8 : ℝ) * (M : ℝ))) := by ring
        _ ≤ ((8 / 3 : ℝ) * (y : ℝ)) *
            (Real.log (2 * (M : ℝ))) ^ 2 * (Real.log V + 3) ^ 2 *
              ((K : ℝ) + reciprocalCorrelationRootConstant *
                ((K : ℝ) ^ (7 / 8 : ℝ) * (M : ℝ))) := by
          gcongr
        _ ≤ ((8 / 3 : ℝ) * (y : ℝ)) *
            (Real.log (2 * (y : ℝ))) ^ 2 * (Real.log V + 3) ^ 2 *
              ((K : ℝ) + reciprocalCorrelationRootConstant *
                ((K : ℝ) ^ (7 / 8 : ℝ) * (M : ℝ))) := by
          gcongr
        _ ≤ ((8 / 3 : ℝ) * (y : ℝ)) *
            (Real.log (2 * (y : ℝ))) ^ 2 * (Real.log V + 3) ^ 2 *
              (2 * (y : ℝ) / (T : ℝ) +
                reciprocalCorrelationRootConstant *
                  ((y : ℝ) / ((y : ℝ) ^ (1 / 128 : ℝ)))) := by
          gcongr
        _ = _ := by ring

/-- Uniform estimate for every padded dyadic block.  Blocks outside the
product annulus or below either Vaughan cutoff vanish exactly; the remaining
block has a long scale at least `16384` and is covered by one of the two
orientation estimates above. -/
theorem norm_reciprocalVaughanFourthDyadicBlock_sq_le_majorant
    {X : ℝ} {x y T alpha beta : ℕ}
    (hT : 0 < T) (hxlarge : 4 * 16384 ^ 2 ≤ x)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 2) (hyx : y ≤ 2 * x) :
    ‖reciprocalVaughanFourthDyadicBlock X T T x y alpha beta‖ ^ 2 ≤
      reciprocalVaughanBlockMajorant T y T := by
  let M : ℕ := 2 ^ alpha
  let K : ℕ := 2 ^ beta
  have hM : 0 < M := by dsimp only [M]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  rw [reciprocalVaughanFourthDyadicBlock_eq_full]
  simp only [reciprocalVaughanFourthFullDyadicBlock, pow_succ,
    Nat.mul_comm]
  change ‖reciprocalBilinearBlock X x y M (2 * M) K (2 * K)
      (cutoffMangoldtCoefficient T) (cutoffFourthCoefficient T)‖ ^ 2 ≤ _
  by_cases hyprod : y < M * K
  · rw [reciprocalVaughanBlock_eq_zero_of_product_above X T T x y M K hyprod,
      norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    exact reciprocalVaughanBlockMajorant_nonneg hT
  have hMK : M * K ≤ y := Nat.le_of_not_gt hyprod
  by_cases hxprod : 4 * M * K ≤ x
  · rw [reciprocalVaughanBlock_eq_zero_of_product_below X T T x y M K hxprod,
      norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    exact reciprocalVaughanBlockMajorant_nonneg hT
  have hxprod' : x < 4 * M * K := Nat.lt_of_not_ge hxprod
  by_cases hTM : 2 * M ≤ T
  · have hTMR : ((2 * M : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast hTM
    rw [reciprocalVaughanBlock_eq_zero_of_mangoldt_cutoff
      X T T x y M K hTMR, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    exact reciprocalVaughanBlockMajorant_nonneg hT
  have hTM' : T < 2 * M := Nat.lt_of_not_ge hTM
  by_cases hTK : 2 * K ≤ T
  · have hTKR : ((2 * K : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast hTK
    rw [reciprocalVaughanBlock_eq_zero_of_fourth_cutoff
      X T T x y M K hTKR, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    exact reciprocalVaughanBlockMajorant_nonneg hT
  have hTK' : T < 2 * K := Nat.lt_of_not_ge hTK
  have hV : (1 : ℝ) ≤ T := by exact_mod_cast hT
  rcases le_total K M with hKM | hMKle
  · have hMlarge : 16384 ≤ M := by
      by_contra hnot
      have hMsmall : M < 16384 := Nat.lt_of_not_ge hnot
      have hprodSmall : 4 * M * K < 4 * 16384 ^ 2 := by
        calc
          4 * M * K ≤ 4 * M * M := by nlinarith
          _ < 4 * 16384 ^ 2 := by nlinarith
      omega
    exact norm_reciprocalVaughanBlock_sq_le_majorant_of_fourth_le_mangoldt
      hV hMlarge hK hKM hT hTK' hxprod' hMK hXlo hXhi hyx
  · have hKlarge : 16384 ≤ K := by
      by_contra hnot
      have hKsmall : K < 16384 := Nat.lt_of_not_ge hnot
      have hprodSmall : 4 * M * K < 4 * 16384 ^ 2 := by
        calc
          4 * M * K ≤ 4 * K * K := by nlinarith
          _ < 4 * 16384 ^ 2 := by nlinarith
      omega
    exact norm_reciprocalVaughanBlock_sq_le_majorant_of_mangoldt_le_fourth
      hV hKlarge hM hMKle hT hTM' hxprod' hMK hXlo hXhi hyx

/-- Summing the uniform block estimate over the exact two-dimensional dyadic
partition. -/
theorem norm_weightedVaughanIntervalFour_reciprocal_le
    {X : ℝ} {x y T : ℕ}
    (hT : 0 < T) (hxlarge : 4 * 16384 ^ 2 ≤ x)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 2) (hyx : y ≤ 2 * x) :
    ‖weightedVaughanIntervalFour (reciprocalWeight X) T T x y‖ ≤
      ((dyadicExponentRange y).card : ℝ) ^ 2 *
        Real.sqrt (reciprocalVaughanBlockMajorant T y T) := by
  let A := reciprocalVaughanBlockMajorant T y T
  have hA : 0 ≤ A := reciprocalVaughanBlockMajorant_nonneg hT
  have hblock (alpha beta : ℕ) :
      ‖reciprocalVaughanFourthDyadicBlock X T T x y alpha beta‖ ≤
        Real.sqrt A := by
    apply (Real.le_sqrt (norm_nonneg _) hA).2
    exact norm_reciprocalVaughanFourthDyadicBlock_sq_le_majorant
      hT hxlarge hXlo hXhi hyx
  rw [weightedVaughanIntervalFour_reciprocal_eq_neg_sum_dyadicBlocks
    X (by exact_mod_cast hT) (by exact_mod_cast hT) x y, norm_neg]
  calc
    ‖∑ alpha ∈ dyadicExponentRange y,
        ∑ beta ∈ dyadicExponentRange y,
          reciprocalVaughanFourthDyadicBlock X T T x y alpha beta‖ ≤
      ∑ alpha ∈ dyadicExponentRange y,
        ‖∑ beta ∈ dyadicExponentRange y,
          reciprocalVaughanFourthDyadicBlock X T T x y alpha beta‖ :=
      norm_sum_le _ _
    _ ≤ ∑ alpha ∈ dyadicExponentRange y,
        ∑ beta ∈ dyadicExponentRange y,
          ‖reciprocalVaughanFourthDyadicBlock X T T x y alpha beta‖ := by
      apply Finset.sum_le_sum
      intro alpha halpha
      exact norm_sum_le _ _
    _ ≤ ∑ _alpha ∈ dyadicExponentRange y,
        ∑ _beta ∈ dyadicExponentRange y, Real.sqrt A := by
      apply Finset.sum_le_sum
      intro alpha halpha
      apply Finset.sum_le_sum
      intro beta hbeta
      exact hblock alpha beta
    _ = ((dyadicExponentRange y).card : ℝ) ^ 2 * Real.sqrt A := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      push_cast
      ring

end

end VaughanReciprocalEstimate
end Erdos378
