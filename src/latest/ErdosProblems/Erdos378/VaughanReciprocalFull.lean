/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.ReciprocalIntervalEstimate
import BoundedGaps.BombieriVinogradov.Analytic.VaughanThirdTermReindex

/-!
# The complete Vaughan estimate for a reciprocal phase

This file combines the Type-I interval estimate with the dyadic Type-II
estimate.  All four terms of Vaughan's identity are retained explicitly.
-/

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace Erdos378
namespace VaughanReciprocalFull

open BoundedGaps.Maynard
open PrimeReciprocal
open ReciprocalIntervalEstimate
open VaughanReciprocalEstimate
open VaughanReciprocalBlocks

noncomputable section

noncomputable def reciprocalTypeIMajorant (y L : ℕ) : ℝ :=
  (L : ℝ) + Real.sqrt (reciprocalIntervalMajorant y L)

lemma reciprocalTypeIMajorant_nonneg {y L : ℕ} :
    0 ≤ reciprocalTypeIMajorant y L := by
  unfold reciprocalTypeIMajorant
  positivity

theorem weightedVaughanIntervalOne_reciprocal_eq_zero
    {X : ℝ} {x y T : ℕ} (hTx : (T : ℝ) ≤ x) :
    weightedVaughanIntervalOne (reciprocalWeight X) T x y = 0 := by
  unfold weightedVaughanIntervalOne
  apply Finset.sum_eq_zero
  intro n hn
  apply mul_eq_zero_of_left
  have hxn : x < n := (Finset.mem_Ioc.mp hn).1
  have hxnR : (x : ℝ) < (n : ℝ) := by exact_mod_cast hxn
  rw [arithmeticFunctionLowCutoff_apply_of_lt (hTx.trans_lt hxnR)]
  norm_num

theorem norm_weightedVaughanIntervalTwo_reciprocal_le
    {X : ℝ} {x y T L : ℕ}
    (hX : 0 < X) (hT : 0 < T) (hTy : T ≤ y)
    (hL : 2 ≤ L) (hsize : 16 * L * T ^ 2 ≤ x)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 2) (hyx : y ≤ 2 * x) :
    ‖weightedVaughanIntervalTwo (reciprocalWeight X) T x y‖ ≤
      (T : ℝ) * (2 * Real.log (y : ℝ) * reciprocalTypeIMajorant y L) := by
  rw [weightedVaughanIntervalTwo_eq_nested]
  calc
    _ ≤ ∑ d ∈ (Finset.Icc 1 y).filter (fun d : ℕ ↦ (d : ℝ) ≤ T),
        ‖((ArithmeticFunction.moebius d : ℝ) : ℂ) *
          ∑ h ∈ Finset.Ioc (x / d) (y / d),
            (Real.log h : ℂ) * reciprocalWeight X (d * h)‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ (Finset.Icc 1 y).filter (fun d : ℕ ↦ (d : ℝ) ≤ T),
        2 * Real.log (y : ℝ) * reciprocalTypeIMajorant y L := by
      apply Finset.sum_le_sum
      intro d hd
      rcases Finset.mem_filter.mp hd with ⟨hdy, hdT⟩
      have hdpos : 0 < d := (Finset.mem_Icc.mp hdy).1
      have hdleT : d ≤ T := by exact_mod_cast hdT
      have hdsize : 16 * L * d ^ 2 ≤ x := by
        calc
          16 * L * d ^ 2 ≤ 16 * L * T ^ 2 := by gcongr
          _ ≤ x := hsize
      rw [norm_mul]
      have hmu : ‖((ArithmeticFunction.moebius d : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      have hinner := norm_log_weighted_reciprocalProductInterval_le
        hX hdpos (Finset.mem_Icc.mp hdy).2 hL hdsize hXlo hXhi hyx
      exact mul_le_of_le_one_left (norm_nonneg _) hmu |>.trans
        (by simpa only [reciprocalTypeIMajorant] using hinner)
    _ ≤ (T : ℝ) *
        (2 * Real.log (y : ℝ) * reciprocalTypeIMajorant y L) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : ((Finset.Icc 1 y).filter
          (fun d : ℕ ↦ (d : ℝ) ≤ T)).card ≤ T := by
        calc
          _ ≤ (Finset.Icc 1 T).card := Finset.card_le_card (by
            intro d hd
            rcases Finset.mem_filter.mp hd with ⟨_hdy, hdT⟩
            have hdleT : d ≤ T := by exact_mod_cast hdT
            exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp _hdy).1, hdleT⟩)
          _ = T := by simp only [Nat.card_Icc]; omega
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      exact mul_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (by
        exact_mod_cast hT.trans_le hTy))) reciprocalTypeIMajorant_nonneg

private lemma weightedVaughanIntervalThree_eq_supported
    {X : ℝ} {x y T : ℕ} (hT : 0 < T) :
    -weightedVaughanIntervalThree (reciprocalWeight X) T T x y =
      ∑ t ∈ (Finset.Icc 1 y).filter (fun t : ℕ ↦ t ≤ T ^ 2),
        ((vaughanThirdCoefficient T T t : ℝ) : ℂ) *
          ∑ r ∈ Finset.Ioc (x / t) (y / t), reciprocalWeight X (t * r) := by
  rw [neg_weightedVaughanIntervalThree_eq_nested (reciprocalWeight X)
    (by exact_mod_cast hT) (by exact_mod_cast hT)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases htT : t ≤ T ^ 2
  · rw [if_pos htT]
  · rw [if_neg htT]
    apply mul_eq_zero_of_left
    have hltNat : T ^ 2 < t := Nat.lt_of_not_ge htT
    have hltR : (T : ℝ) * (T : ℝ) < (t : ℝ) := by
      exact_mod_cast (show T * T < t by simpa [pow_two] using hltNat)
    rw [vaughanThirdCoefficient_eq_zero_of_cutoffProduct_lt
      (by exact_mod_cast hT.le) (by exact_mod_cast hT.le) hltR]
    norm_num

theorem norm_weightedVaughanIntervalThree_reciprocal_le
    {X : ℝ} {x y T L : ℕ}
    (hX : 0 < X) (hT : 0 < T) (hTy : T ≤ y)
    (hL : 2 ≤ L) (hsize : 16 * L * (T ^ 2) ^ 2 ≤ x)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 2) (hyx : y ≤ 2 * x) :
    ‖weightedVaughanIntervalThree (reciprocalWeight X) T T x y‖ ≤
      ((T ^ 2 : ℕ) : ℝ) *
        (Real.log (y : ℝ) * reciprocalTypeIMajorant y L) := by
  rw [← norm_neg, weightedVaughanIntervalThree_eq_supported hT]
  calc
    _ ≤ ∑ t ∈ (Finset.Icc 1 y).filter (fun t : ℕ ↦ t ≤ T ^ 2),
        ‖((vaughanThirdCoefficient T T t : ℝ) : ℂ) *
          ∑ r ∈ Finset.Ioc (x / t) (y / t),
            reciprocalWeight X (t * r)‖ := norm_sum_le _ _
    _ ≤ ∑ _t ∈ (Finset.Icc 1 y).filter (fun t : ℕ ↦ t ≤ T ^ 2),
        Real.log (y : ℝ) * reciprocalTypeIMajorant y L := by
      apply Finset.sum_le_sum
      intro t ht
      rcases Finset.mem_filter.mp ht with ⟨hty, htT⟩
      have htpos : 0 < t := (Finset.mem_Icc.mp hty).1
      have htsize : 16 * L * t ^ 2 ≤ x := by
        calc
          16 * L * t ^ 2 ≤ 16 * L * (T ^ 2) ^ 2 := by gcongr
          _ ≤ x := hsize
      have hcoeff : ‖((vaughanThirdCoefficient T T t : ℝ) : ℂ)‖ ≤
          Real.log (y : ℝ) :=
        (norm_vaughanThirdCoefficient_le_log T T t).trans
          (Real.log_le_log (by exact_mod_cast htpos)
            (by exact_mod_cast (Finset.mem_Icc.mp hty).2))
      have hinner := norm_reciprocalProductInterval_partial_le
        hX htpos (Finset.mem_Icc.mp hty).2
          (show y / t ≤ y / t from le_rfl) hL htsize hXlo hXhi hyx
      rw [norm_mul]
      exact mul_le_mul hcoeff (by
        simpa only [reciprocalTypeIMajorant, reciprocalProductIntervalSum]
          using hinner) (norm_nonneg _) (Real.log_nonneg (by
            exact_mod_cast (show 1 ≤ y from (Finset.mem_Icc.mp hty).1.trans
              (Finset.mem_Icc.mp hty).2)))
    _ ≤ ((T ^ 2 : ℕ) : ℝ) *
        (Real.log (y : ℝ) * reciprocalTypeIMajorant y L) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : ((Finset.Icc 1 y).filter
          (fun t : ℕ ↦ t ≤ T ^ 2)).card ≤ T ^ 2 := by
        calc
          _ ≤ (Finset.Icc 1 (T ^ 2)).card := Finset.card_le_card (by
            intro t ht
            rcases Finset.mem_filter.mp ht with ⟨hty, htT⟩
            exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hty).1, htT⟩)
          _ = T ^ 2 := by simp only [Nat.card_Icc]; omega
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hT.trans_le hTy))
        reciprocalTypeIMajorant_nonneg

noncomputable def reciprocalChebyshevMajorant (y T L : ℕ) : ℝ :=
  (T : ℝ) * (2 * Real.log (y : ℝ) * reciprocalTypeIMajorant y L) +
    ((T ^ 2 : ℕ) : ℝ) *
      (Real.log (y : ℝ) * reciprocalTypeIMajorant y L) +
    ((dyadicExponentRange y).card : ℝ) ^ 2 *
      Real.sqrt (reciprocalVaughanBlockMajorant T y T)

theorem norm_weightedChebyshevInterval_reciprocal_le
    {X : ℝ} {x y T L : ℕ}
    (hX : 0 < X) (hT : 0 < T) (hTy : T ≤ y) (hTx : T ≤ x)
    (hL : 2 ≤ L) (hsize : 16 * L * (T ^ 2) ^ 2 ≤ x)
    (hxlarge : 4 * 16384 ^ 2 ≤ x)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 2) (hyx : y ≤ 2 * x) :
    ‖weightedChebyshevInterval (reciprocalWeight X) x y‖ ≤
      reciprocalChebyshevMajorant y T L := by
  rw [weightedChebyshevInterval_eq_vaughan,
    weightedVaughanIntervalOne_reciprocal_eq_zero (by exact_mod_cast hTx),
    zero_add]
  have hTpow : T ^ 2 ≤ (T ^ 2) ^ 2 := by
    have hTone : 1 ≤ T ^ 2 := pow_pos hT 2
    nlinarith
  have hsizeTwo : 16 * L * T ^ 2 ≤ x := by
    exact (Nat.mul_le_mul_left (16 * L) hTpow).trans hsize
  have hTwo := norm_weightedVaughanIntervalTwo_reciprocal_le
    hX hT hTy hL hsizeTwo hXlo hXhi hyx
  have hThree := norm_weightedVaughanIntervalThree_reciprocal_le
    hX hT hTy hL hsize hXlo hXhi hyx
  have hFour := norm_weightedVaughanIntervalFour_reciprocal_le
    hT hxlarge hXlo hXhi hyx
  unfold reciprocalChebyshevMajorant
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add hTwo hThree)) hFour)

end

end VaughanReciprocalFull
end Erdos378
