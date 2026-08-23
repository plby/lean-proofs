import ErdosProblems.Erdos1166.Erdos1166HLOZAppendixAFirstMoment
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Quantitative lower order of the HLOZ Appendix-A profile mass

This module turns the exact finite-block Proposition-A.7 factor into the
stretched-exponential estimate used by the disk second moment.  The key
point is to preserve the deterministic drift `2 * N`: normalization and
Abel-boundary terms cost `O(n^(1/5))`, while the denominator mismatch and
sharp local-limit remainder cost `O(n^(3/5))`.  Together with the checked
finite A.8/A.12 block exponent `753/1250` and the finite prefix, this yields

`exp (-2*n - C*n^(753/1250)) ≤ appendixSourceA7 n`

eventually, with an explicit scale-independent constant `C`.
-/

open scoped BigOperators
open Set intervalIntegral

namespace Erdos1166.HLOZAppendixAFirstMoment

open Filter

lemma sum_range_succ_rpow_neg_le (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ) ^ (-a)) ≤
      1 + ((N : ℝ) ^ (1 - a) - 1) / (1 - a) := by
  let f : ℝ → ℝ := fun x ↦ x ^ (-a)
  have hf : AntitoneOn f (Icc ((1 : ℕ) : ℝ) (N : ℝ)) := by
    exact (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (neg_nonpos.mpr ha0)).mono
      (by
        intro x hx
        norm_num at hx ⊢
        exact zero_lt_one.trans_le hx.1)
  have htail := AntitoneOn.sum_le_integral_Ico (f := f) hN hf
  have hsum :
      (∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ) ^ (-a)) =
        1 + ∑ j ∈ Finset.Ico 1 N, ((j + 1 : ℕ) : ℝ) ^ (-a) := by
    obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    rw [Finset.sum_range_succ', Finset.sum_Ico_eq_sum_range]
    rw [add_comm]
    norm_num
    congr 1
    funext j
    congr 1
    ring
  rw [hsum]
  gcongr
  calc
    (∑ j ∈ Finset.Ico 1 N, ((j + 1 : ℕ) : ℝ) ^ (-a))
        ≤ ∫ x in (1 : ℝ)..(N : ℝ), x ^ (-a) := by simpa [f] using htail
    _ = ((N : ℝ) ^ (1 - a) - 1) / (1 - a) := by
      rw [integral_rpow]
      · norm_num
        ring
      · left
        linarith

lemma sum_fin_add_rpow_neg_le (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (start N : ℕ) (hstart : 1 ≤ start) (hN : 1 ≤ N) :
    (∑ i : Fin N, ((start + (i : ℕ) : ℕ) : ℝ) ^ (-a)) ≤
      1 + ((N : ℝ) ^ (1 - a) - 1) / (1 - a) := by
  have hsum :
      (∑ i : Fin N, ((start + (i : ℕ) : ℕ) : ℝ) ^ (-a)) =
        ∑ i ∈ Finset.range N, ((start + i : ℕ) : ℝ) ^ (-a) := by
    exact Fin.sum_univ_eq_sum_range
      (fun i : ℕ ↦ ((start + i : ℕ) : ℝ) ^ (-a)) N
  rw [hsum]
  calc
    (∑ i ∈ Finset.range N, ((start + i : ℕ) : ℝ) ^ (-a)) ≤
        ∑ i ∈ Finset.range N, ((i + 1 : ℕ) : ℝ) ^ (-a) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (neg_nonpos.mpr ha0)
      · simpa only [mem_Ioi] using
          (show (0 : ℝ) < (i + 1 : ℕ) by positivity)
      · simpa only [mem_Ioi] using
          (show (0 : ℝ) < (start + i : ℕ) by positivity)
      · exact_mod_cast (show i + 1 ≤ start + i by omega)
    _ ≤ _ := sum_range_succ_rpow_neg_le a ha0 ha1 N hN

lemma sum_fin_add_rpow_neg_four_fifths_le
    (start N : ℕ) (hstart : 1 ≤ start) :
    (∑ i : Fin N,
      ((start + (i : ℕ) : ℕ) : ℝ) ^ (-(4 / 5 : ℝ))) ≤
        5 * (N : ℝ) ^ (1 / 5 : ℝ) := by
  by_cases hN0 : N = 0
  · subst N
    simp
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
  have h := sum_fin_add_rpow_neg_le (4 / 5 : ℝ)
    (by norm_num) (by norm_num) start N hstart hN
  have hp : 1 ≤ (N : ℝ) ^ (1 / 5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  calc
    _ ≤ 1 + ((N : ℝ) ^ (1 - (4 / 5 : ℝ)) - 1) /
        (1 - (4 / 5 : ℝ)) := h
    _ ≤ 5 * (N : ℝ) ^ (1 / 5 : ℝ) := by
      norm_num at hp ⊢
      linarith

lemma sum_fin_add_rpow_neg_two_fifths_le
    (start N : ℕ) (hstart : 1 ≤ start) :
    (∑ i : Fin N,
      ((start + (i : ℕ) : ℕ) : ℝ) ^ (-(2 / 5 : ℝ))) ≤
        2 * (N : ℝ) ^ (3 / 5 : ℝ) := by
  by_cases hN0 : N = 0
  · subst N
    simp
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
  have h := sum_fin_add_rpow_neg_le (2 / 5 : ℝ)
    (by norm_num) (by norm_num) start N hstart hN
  have hp : 1 ≤ (N : ℝ) ^ (3 / 5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  calc
    _ ≤ 1 + ((N : ℝ) ^ (1 - (2 / 5 : ℝ)) - 1) /
        (1 - (2 / 5 : ℝ)) := h
    _ ≤ 2 * (N : ℝ) ^ (3 / 5 : ℝ) := by
      norm_num at hp ⊢
      linarith

open Erdos1166.HLOZPropositionA7

lemma rpow_six_fifths_mul_two_le_four {ell : ℕ} (hell : 1 ≤ ell) :
    (2 * (ell : ℝ)) ^ (6 / 5 : ℝ) ≤
      4 * (ell : ℝ) ^ (6 / 5 : ℝ) := by
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity)]
  have htwo : (2 : ℝ) ^ (6 / 5 : ℝ) ≤ 2 ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hp : 0 ≤ (ell : ℝ) ^ (6 / 5 : ℝ) := Real.rpow_nonneg (by positivity) _
  calc
    (2 : ℝ) ^ (6 / 5 : ℝ) * (ell : ℝ) ^ (6 / 5 : ℝ) ≤
        2 ^ (2 : ℝ) * (ell : ℝ) ^ (6 / 5 : ℝ) := by gcongr
    _ = 4 * (ell : ℝ) ^ (6 / 5 : ℝ) := by norm_num [Real.rpow_two]

lemma radius_succ_le_four_rpow {ell : ℕ} (hell : 1 ≤ ell) :
    (Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) (ell + 1) : ℝ) ≤
      4 * (ell : ℝ) ^ (6 / 5 : ℝ) := by
  have hr := corridorRadius_cast_le (1 / 5 : ℝ) (ell + 1)
  have hbase : ((ell + 1 : ℕ) : ℝ) ≤ 2 * (ell : ℝ) := by
    norm_num
    exact_mod_cast (show ell + 1 ≤ 2 * ell by omega)
  have hpow : ((ell + 1 : ℕ) : ℝ) ^ (6 / 5 : ℝ) ≤
      (2 * (ell : ℝ)) ^ (6 / 5 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hbase (by norm_num)
  norm_num only [show (1 + (1 / 5 : ℝ)) = 6 / 5 by norm_num] at hr
  exact hr.trans (hpow.trans (rpow_six_fifths_mul_two_le_four hell))

lemma linear_le_six_rpow {ell : ℕ} (hell : 1 ≤ ell) :
    (4 * ell + 2 : ℕ) ≤ 6 * (ell : ℝ) ^ (6 / 5 : ℝ) := by
  have hlin : (4 * ell + 2 : ℕ) ≤ 6 * ell := by omega
  have hbase : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hpow : (ell : ℝ) ≤ (ell : ℝ) ^ (6 / 5 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le
      hbase (by norm_num : (1 : ℝ) ≤ 6 / 5)
    simpa using this
  have hlinR : ((4 * ell + 2 : ℕ) : ℝ) ≤ 6 * (ell : ℝ) := by
    exact_mod_cast hlin
  exact hlinR.trans (by gcongr)

lemma D_le_twelve_rpow {ell : ℕ} (hell : 1 ≤ ell) :
    ((4 * ell + 2 +
      Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) ell +
      Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) (ell + 1) : ℕ) : ℝ) ≤
      12 * (ell : ℝ) ^ (6 / 5 : ℝ) := by
  have hR := corridorRadius_cast_le (1 / 5 : ℝ) ell
  norm_num only [show (1 + (1 / 5 : ℝ)) = 6 / 5 by norm_num] at hR
  have hRs := radius_succ_le_four_rpow hell
  have hlin := linear_le_six_rpow hell
  calc
    ((4 * ell + 2 +
        Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) ell +
        Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) (ell + 1) : ℕ) : ℝ) =
      ((4 * ell + 2 : ℕ) : ℝ) +
        Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) ell +
        Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) (ell + 1) := by
          push_cast
          ring
    _ ≤ 12 * (ell : ℝ) ^ (6 / 5 : ℝ) := by linarith

lemma neg_rpow_id {ell : ℕ} (hell : 1 ≤ ell) :
    (ell : ℝ) ^ (6 / 5 : ℝ) / (ell : ℝ) ^ 2 =
      (ell : ℝ) ^ (-(4 / 5 : ℝ)) := by
  have he : 0 < (ell : ℝ) := by exact_mod_cast (show 0 < ell by omega)
  rw [← Real.rpow_two, ← Real.rpow_sub he]
  congr 2
  ring

lemma neg_two_fifths_id {ell : ℕ} (hell : 1 ≤ ell) :
    (ell : ℝ) ^ (18 / 5 : ℝ) / (ell : ℝ) ^ 4 =
      (ell : ℝ) ^ (-(2 / 5 : ℝ)) := by
  have he : 0 < (ell : ℝ) := by exact_mod_cast (show 0 < ell by omega)
  rw [← Real.rpow_natCast, ← Real.rpow_sub he]
  congr 2
  ring

lemma rpow_six_fifths_cube_div_four {ell : ℕ} (hell : 1 ≤ ell) :
    ((ell : ℝ) ^ (6 / 5 : ℝ)) ^ 3 / (ell : ℝ) ^ 4 =
      (ell : ℝ) ^ (-(2 / 5 : ℝ)) := by
  have he : 0 < (ell : ℝ) := by exact_mod_cast (show 0 < ell by omega)
  rw [← Real.rpow_natCast, ← Real.rpow_mul he.le, ← Real.rpow_natCast,
    ← Real.rpow_sub he]
  congr 2
  ring

lemma rpow_six_fifths_sq_mul_div_four {ell : ℕ} (hell : 1 ≤ ell) :
    ((ell : ℝ) ^ (6 / 5 : ℝ)) ^ 2 *
        (ell : ℝ) ^ (6 / 5 : ℝ) / (ell : ℝ) ^ 4 =
      (ell : ℝ) ^ (-(2 / 5 : ℝ)) := by
  have he : 0 < (ell : ℝ) := by exact_mod_cast (show 0 < ell by omega)
  rw [← Real.rpow_natCast, ← Real.rpow_mul he.le, ← Real.rpow_add he,
    ← Real.rpow_natCast, ← Real.rpow_sub he]
  congr 2
  ring

lemma radius_div_two_sq_le {ell : ℕ} (hell : 1 ≤ ell) :
    (Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) ell : ℝ) /
        (2 * (ell : ℝ) ^ 2) ≤
      (ell : ℝ) ^ (-(4 / 5 : ℝ)) := by
  have hr := corridorRadius_cast_le (1 / 5 : ℝ) ell
  norm_num only [show (1 + (1 / 5 : ℝ)) = 6 / 5 by norm_num] at hr
  calc
    (Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) ell : ℝ) /
        (2 * (ell : ℝ) ^ 2) ≤
      (ell : ℝ) ^ (6 / 5 : ℝ) / (ell : ℝ) ^ 2 := by
        refine div_le_div₀ (by positivity) hr (by positivity) ?_
        nlinarith [sq_nonneg (ell : ℝ)]
    _ = _ := neg_rpow_id hell

lemma sharp_bound {ell : ℕ} (hell : 1 ≤ ell)
    (hbudget :
      Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) ell +
          4 * (4 * ell + 2 +
            Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) ell +
            Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) (ell + 1)) ≤
        2 * ell ^ 2) :
    corridorSharpRemainderBound ell
        (Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) ell)
        (Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) (ell + 1)) ≤
      7000 * (ell : ℝ) ^ (-(2 / 5 : ℝ)) := by
  let R := Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) ell
  let R' := Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) (ell + 1)
  let D : ℕ := 4 * ell + 2 + R + R'
  let B : ℕ := 2 * ell ^ 2 - R
  have hD : (D : ℝ) ≤ 12 * (ell : ℝ) ^ (6 / 5 : ℝ) := by
    simpa [D, R, R'] using D_le_twelve_rpow hell
  have hBnat : ell ^ 2 ≤ B := by
    dsimp [B, D, R, R']
    omega
  have hB : (ell : ℝ) ^ 2 ≤ (B : ℝ) := by exact_mod_cast hBnat
  have hBpos : 0 < (B : ℝ) := lt_of_lt_of_le (by positivity) hB
  have hnegmono : (ell : ℝ) ^ (-(4 / 5 : ℝ)) ≤
      (ell : ℝ) ^ (-(2 / 5 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hell) (by norm_num)
  have h1 : 3 * (D : ℝ) / B ≤
      36 * (ell : ℝ) ^ (-(2 / 5 : ℝ)) := by
    calc
      3 * (D : ℝ) / B ≤
          (36 * (ell : ℝ) ^ (6 / 5 : ℝ)) / (ell : ℝ) ^ 2 := by
        refine div_le_div₀ (by positivity) ?_ (by positivity) hB
        linarith
      _ = 36 * (ell : ℝ) ^ (-(4 / 5 : ℝ)) := by
        rw [mul_div_assoc, neg_rpow_id hell]
      _ ≤ 36 * (ell : ℝ) ^ (-(2 / 5 : ℝ)) := by gcongr
  have h3 : 4 * (D : ℝ) ^ 3 / (B : ℝ) ^ 2 ≤
      6912 * (ell : ℝ) ^ (-(2 / 5 : ℝ)) := by
    have hD3 : (D : ℝ) ^ 3 ≤
        (12 * (ell : ℝ) ^ (6 / 5 : ℝ)) ^ 3 := by gcongr
    have hB2 : (ell : ℝ) ^ 4 ≤ (B : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((B : ℝ) - (ell : ℝ) ^ 2)]
    calc
      4 * (D : ℝ) ^ 3 / (B : ℝ) ^ 2 ≤
          4 * (12 * (ell : ℝ) ^ (6 / 5 : ℝ)) ^ 3 /
            (ell : ℝ) ^ 4 := by
        refine div_le_div₀ (by positivity) (by gcongr) (by positivity) hB2
      _ = 6912 *
          (((ell : ℝ) ^ (6 / 5 : ℝ)) ^ 3 / (ell : ℝ) ^ 4) := by
        ring
      _ = 6912 * (ell : ℝ) ^ (-(2 / 5 : ℝ)) := by
        rw [rpow_six_fifths_cube_div_four hell]
  have hi : 1 / (B : ℝ) ≤
      (ell : ℝ) ^ (-(2 / 5 : ℝ)) := by
    calc
      1 / (B : ℝ) ≤ 1 / (ell : ℝ) ^ 2 := by
        exact one_div_le_one_div_of_le (by positivity) hB
      _ = (ell : ℝ) ^ (-(2 : ℝ)) := by
        have he : 0 < (ell : ℝ) := by positivity
        rw [one_div, ← Real.rpow_two, ← Real.rpow_neg he.le]
      _ ≤ (ell : ℝ) ^ (-(2 / 5 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hell) (by norm_num)
  unfold corridorSharpRemainderBound
  dsimp only [D, B, R, R'] at h1 h3 hi ⊢
  have hp0 : 0 ≤ (ell : ℝ) ^ (-(2 / 5 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  linarith

lemma mismatch_bound {ell : ℕ} (hell : 1 ≤ ell)
    (hbudget :
      Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) ell +
          4 * (4 * ell + 2 +
            Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) ell +
            Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) (ell + 1)) ≤
        2 * ell ^ 2) :
    corridorDenominatorMismatchBound ell
        (Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) ell)
        (Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) (ell + 1)) ≤
      144 * (ell : ℝ) ^ (-(2 / 5 : ℝ)) := by
  let R := Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) ell
  let R' := Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) (ell + 1)
  let D : ℕ := 4 * ell + 2 + R + R'
  let B : ℕ := 2 * ell ^ 2 - R
  have hD : (D : ℝ) ≤ 12 * (ell : ℝ) ^ (6 / 5 : ℝ) := by
    simpa [D, R, R'] using D_le_twelve_rpow hell
  have hR : (R : ℝ) ≤ (ell : ℝ) ^ (6 / 5 : ℝ) := by
    have h := corridorRadius_cast_le (1 / 5 : ℝ) ell
    norm_num only [show (1 + (1 / 5 : ℝ)) = 6 / 5 by norm_num] at h
    simpa [R] using h
  have hBnat : ell ^ 2 ≤ B := by
    dsimp [B, D, R, R']
    omega
  have hB : (ell : ℝ) ^ 2 ≤ (B : ℝ) := by exact_mod_cast hBnat
  have hnum : (D : ℝ) ^ 2 * R ≤
      144 * (((ell : ℝ) ^ (6 / 5 : ℝ)) ^ 2 *
        (ell : ℝ) ^ (6 / 5 : ℝ)) := by
    have hD2 : (D : ℝ) ^ 2 ≤
        144 * ((ell : ℝ) ^ (6 / 5 : ℝ)) ^ 2 := by
      calc
        (D : ℝ) ^ 2 ≤ (12 * (ell : ℝ) ^ (6 / 5 : ℝ)) ^ 2 := by gcongr
        _ = 144 * ((ell : ℝ) ^ (6 / 5 : ℝ)) ^ 2 := by ring
    calc
      (D : ℝ) ^ 2 * R ≤
          (144 * ((ell : ℝ) ^ (6 / 5 : ℝ)) ^ 2) * R := by
        gcongr
      _ ≤ (144 * ((ell : ℝ) ^ (6 / 5 : ℝ)) ^ 2) *
          (ell : ℝ) ^ (6 / 5 : ℝ) := by gcongr
      _ = 144 * (((ell : ℝ) ^ (6 / 5 : ℝ)) ^ 2 *
          (ell : ℝ) ^ (6 / 5 : ℝ)) := by ring
  unfold corridorDenominatorMismatchBound
  dsimp only [D, B, R, R'] at hnum hB ⊢
  calc
    ((4 * ell + 2 +
          Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) ell +
          Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) (ell + 1) : ℕ) : ℝ) ^ 2 *
        Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) ell /
          (8 * (ell : ℝ) ^ 2 *
            ((2 * ell ^ 2 -
              Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) ell : ℕ) : ℝ)) ≤
      144 * (((ell : ℝ) ^ (6 / 5 : ℝ)) ^ 2 *
        (ell : ℝ) ^ (6 / 5 : ℝ)) / (ell : ℝ) ^ 4 := by
      refine div_le_div₀ (by positivity) hnum (by positivity) ?_
      have he2 : 0 ≤ (ell : ℝ) ^ 2 := sq_nonneg _
      nlinarith
    _ = 144 * (ell : ℝ) ^ (-(2 / 5 : ℝ)) := by
      rw [mul_div_assoc, rpow_six_fifths_sq_mul_div_four hell]

lemma one_div_le_neg_four_fifths {ell : ℕ} (hell : 1 ≤ ell) :
    1 / (ell : ℝ) ≤ (ell : ℝ) ^ (-(4 / 5 : ℝ)) := by
  have he : 0 < (ell : ℝ) := by exact_mod_cast (show 0 < ell by omega)
  calc
    1 / (ell : ℝ) = (ell : ℝ) ^ (-(1 : ℝ)) := by
      rw [one_div, Real.rpow_neg_one]
    _ ≤ (ell : ℝ) ^ (-(4 / 5 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hell) (by norm_num)

lemma base_drift_term_le {ell : ℕ} (hell : 1 ≤ ell) :
    2 + 2 / (ell : ℝ) + 1 / (2 * (ell : ℝ) ^ 2) ≤
      2 + 3 * (ell : ℝ) ^ (-(4 / 5 : ℝ)) := by
  have h1 := one_div_le_neg_four_fifths hell
  have h2 : 1 / ((ell : ℝ) ^ 2) ≤
      (ell : ℝ) ^ (-(4 / 5 : ℝ)) := by
    calc
      1 / ((ell : ℝ) ^ 2) ≤ 1 / (ell : ℝ) := by
        exact one_div_le_one_div_of_le (by positivity)
          (by nlinarith [show (1 : ℝ) ≤ ell by exact_mod_cast hell])
      _ ≤ _ := h1
  have hp0 : 0 ≤ (ell : ℝ) ^ (-(4 / 5 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  rw [show 2 / (ell : ℝ) = 2 * (1 / (ell : ℝ)) by ring,
    show 1 / (2 * (ell : ℝ) ^ 2) = (1 / 2) * (1 / (ell : ℝ) ^ 2) by ring]
  nlinarith

lemma radius_div_self_le {ell : ℕ} (hell : 1 ≤ ell) :
    (Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) ell : ℝ) /
        (ell : ℝ) ≤ (ell : ℝ) ^ (1 / 5 : ℝ) := by
  have hr := corridorRadius_cast_le (1 / 5 : ℝ) ell
  norm_num only [show (1 + (1 / 5 : ℝ)) = 6 / 5 by norm_num] at hr
  have he : 0 < (ell : ℝ) := by exact_mod_cast (show 0 < ell by omega)
  calc
    (Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) ell : ℝ) /
        (ell : ℝ) ≤ (ell : ℝ) ^ (6 / 5 : ℝ) / (ell : ℝ) := by
      exact div_le_div_of_nonneg_right hr he.le
    _ = (ell : ℝ) ^ (1 / 5 : ℝ) := by
      calc
        (ell : ℝ) ^ (6 / 5 : ℝ) / (ell : ℝ) =
            (ell : ℝ) ^ (6 / 5 : ℝ) / (ell : ℝ) ^ (1 : ℝ) := by
              rw [Real.rpow_one]
        _ = (ell : ℝ) ^ ((6 / 5 : ℝ) - 1) :=
          (Real.rpow_sub he (6 / 5 : ℝ) 1).symm
        _ = (ell : ℝ) ^ (1 / 5 : ℝ) := by norm_num

lemma radius_succ_div_product_le {ell : ℕ} (hell : 1 ≤ ell) :
    (Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) (ell + 1) : ℝ) /
        ((ell : ℝ) * (ell + 1 : ℕ)) ≤
      4 * (ell : ℝ) ^ (-(4 / 5 : ℝ)) := by
  have hr := radius_succ_le_four_rpow hell
  calc
    (Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) (ell + 1) : ℝ) /
        ((ell : ℝ) * (ell + 1 : ℕ)) ≤
      (4 * (ell : ℝ) ^ (6 / 5 : ℝ)) / (ell : ℝ) ^ 2 := by
      refine div_le_div₀ (by positivity) hr (by positivity) ?_
      exact_mod_cast (show ell ^ 2 ≤ ell * (ell + 1) by nlinarith)
    _ = 4 * (ell : ℝ) ^ (-(4 / 5 : ℝ)) := by
      rw [mul_div_assoc, neg_rpow_id hell]

lemma radius_pair_div_two_sq_le {ell : ℕ} (hell : 1 ≤ ell) :
    ((Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) ell : ℝ) +
        Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) (ell + 1)) /
          (2 * (ell : ℝ) ^ 2) ≤
      3 * (ell : ℝ) ^ (-(4 / 5 : ℝ)) := by
  have hR := corridorRadius_cast_le (1 / 5 : ℝ) ell
  norm_num only [show (1 + (1 / 5 : ℝ)) = 6 / 5 by norm_num] at hR
  have hRs := radius_succ_le_four_rpow hell
  calc
    ((Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) ell : ℝ) +
        Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) (ell + 1)) /
          (2 * (ell : ℝ) ^ 2) ≤
      (6 * (ell : ℝ) ^ (6 / 5 : ℝ)) / (2 * (ell : ℝ) ^ 2) := by
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = 3 * (ell : ℝ) ^ (-(4 / 5 : ℝ)) := by
      rw [show 6 * (ell : ℝ) ^ (6 / 5 : ℝ) / (2 * (ell : ℝ) ^ 2) =
        3 * ((ell : ℝ) ^ (6 / 5 : ℝ) / (ell : ℝ) ^ 2) by ring,
        neg_rpow_id hell]

lemma pathNormalizationCost_le
    {start N : ℕ} (hstart : 1 ≤ start) :
    pathNormalizationCost start N (hlozRadius (1 / 5 : ℝ) start N) ≤
      5 * ((start + N : ℕ) : ℝ) ^ (1 / 5 : ℝ) := by
  unfold pathNormalizationCost hlozRadius
  have hsum := sum_fin_add_rpow_neg_four_fifths_le start N hstart
  have hterms :
      (∑ i : Fin N,
        (Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ)
            (start + (i : ℕ)) : ℝ) /
          (2 * ((start + (i : ℕ) : ℕ) : ℝ) ^ 2)) ≤
        ∑ i : Fin N,
          ((start + (i : ℕ) : ℕ) : ℝ) ^ (-(4 / 5 : ℝ)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact radius_div_two_sq_le (by omega)
  have hNpow : (N : ℝ) ^ (1 / 5 : ℝ) ≤
      ((start + N : ℕ) : ℝ) ^ (1 / 5 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.le_add_left N start)
      (by norm_num)
  exact hterms.trans (hsum.trans (by gcongr))

lemma corridorDriftBound_le
    {start N : ℕ} (hstart : 1 ≤ start) :
    corridorDriftBound start N (hlozRadius (1 / 5 : ℝ) start N) ≤
      2 * (N : ℝ) + 52 * ((start + N : ℕ) : ℝ) ^ (1 / 5 : ℝ) := by
  let S : ℝ := ∑ i : Fin N,
    ((start + (i : ℕ) : ℕ) : ℝ) ^ (-(4 / 5 : ℝ))
  have hS : S ≤ 5 * (N : ℝ) ^ (1 / 5 : ℝ) := by
    exact sum_fin_add_rpow_neg_four_fifths_le start N hstart
  have hbase : baseDriftPathAction start N ≤ 2 * (N : ℝ) + 3 * S := by
    unfold baseDriftPathAction
    calc
      (∑ i : Fin N, (2 + 2 / ((start + (i : ℕ) : ℕ) : ℝ) +
        1 / (2 * ((start + (i : ℕ) : ℕ) : ℝ) ^ 2))) ≤
        ∑ i : Fin N,
          (2 + 3 * ((start + (i : ℕ) : ℕ) : ℝ) ^ (-(4 / 5 : ℝ))) := by
          apply Finset.sum_le_sum
          intro i hi
          exact base_drift_term_le (by omega)
      _ = 2 * (N : ℝ) + 3 * S := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        dsimp [S]
        rw [← Finset.mul_sum]
        ring
  have hend :
      (Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) (start + N) : ℝ) /
          (start + N : ℕ) ≤
        ((start + N : ℕ) : ℝ) ^ (1 / 5 : ℝ) :=
    radius_div_self_le (by omega)
  have hzero :
      (Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ) start : ℝ) / start ≤
        ((start + N : ℕ) : ℝ) ^ (1 / 5 : ℝ) := by
    have h0 := radius_div_self_le hstart
    exact h0.trans (Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast Nat.le_add_right start N) (by norm_num))
  have hprimary :
      (∑ i : Fin N,
        (Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ)
            (start + (i : ℕ) + 1) : ℝ) /
          (((start + (i : ℕ) : ℕ) : ℝ) *
            (start + (i : ℕ) + 1 : ℕ))) ≤ 4 * S := by
    calc
      _ ≤ ∑ i : Fin N,
          4 * ((start + (i : ℕ) : ℕ) : ℝ) ^ (-(4 / 5 : ℝ)) := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [Nat.add_assoc] using
          radius_succ_div_product_le (show 1 ≤ start + (i : ℕ) by omega)
      _ = 4 * S := by
        dsimp [S]
        rw [Finset.mul_sum]
  have hsecondary :
      (∑ i : Fin N,
        ((Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ)
            (start + (i : ℕ)) : ℝ) +
          Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ)
            (start + (i : ℕ) + 1)) /
          (2 * ((start + (i : ℕ) : ℕ) : ℝ) ^ 2)) ≤ 3 * S := by
    calc
      _ ≤ ∑ i : Fin N,
          3 * ((start + (i : ℕ) : ℕ) : ℝ) ^ (-(4 / 5 : ℝ)) := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [Nat.add_assoc] using
          radius_pair_div_two_sq_le (show 1 ≤ start + (i : ℕ) by omega)
      _ = 3 * S := by
        dsimp [S]
        rw [Finset.mul_sum]
  have hNpow : (N : ℝ) ^ (1 / 5 : ℝ) ≤
      ((start + N : ℕ) : ℝ) ^ (1 / 5 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.le_add_left N start)
      (by norm_num)
  simp only [Nat.add_assoc] at hprimary hsecondary
  unfold corridorDriftBound hlozRadius
  simp only [Fin.last, Fin.val_mk, Fin.val_zero, Fin.val_succ,
    Fin.val_castSucc, Nat.add_zero, Nat.add_assoc]
  have hp0 : 0 ≤ ((start + N : ℕ) : ℝ) ^ (1 / 5 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  linarith

lemma corridorDenominatorMismatchPathBound_le
    {start N : ℕ} (hstart : 1 ≤ start)
    (hbudget : ParabolicRadiusBudget start N
      (hlozRadius (1 / 5 : ℝ) start N)) :
    corridorDenominatorMismatchPathBound start N
        (hlozRadius (1 / 5 : ℝ) start N) ≤
      288 * ((start + N : ℕ) : ℝ) ^ (3 / 5 : ℝ) := by
  unfold corridorDenominatorMismatchPathBound hlozRadius
  have hterms :
      (∑ i : Fin N,
        corridorDenominatorMismatchBound (start + (i : ℕ))
          (Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ)
            (start + (i : ℕ)))
          (Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ)
            (start + (i : ℕ) + 1))) ≤
        ∑ i : Fin N,
          144 * ((start + (i : ℕ) : ℕ) : ℝ) ^ (-(2 / 5 : ℝ)) := by
    apply Finset.sum_le_sum
    intro i hi
    apply mismatch_bound (by omega)
    simpa only [hlozRadius, Fin.val_castSucc, Fin.val_succ, Nat.add_assoc] using hbudget i
  have hsum := sum_fin_add_rpow_neg_two_fifths_le start N hstart
  have hNpow : (N : ℝ) ^ (3 / 5 : ℝ) ≤
      ((start + N : ℕ) : ℝ) ^ (3 / 5 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.le_add_left N start)
      (by norm_num)
  calc
    _ ≤ ∑ i : Fin N,
          144 * ((start + (i : ℕ) : ℕ) : ℝ) ^ (-(2 / 5 : ℝ)) := hterms
    _ = 144 * (∑ i : Fin N,
          ((start + (i : ℕ) : ℕ) : ℝ) ^ (-(2 / 5 : ℝ))) := by
      rw [Finset.mul_sum]
    _ ≤ 144 * (2 * (N : ℝ) ^ (3 / 5 : ℝ)) := by gcongr
    _ ≤ 288 * ((start + N : ℕ) : ℝ) ^ (3 / 5 : ℝ) := by
      nlinarith

lemma corridorSharpRemainderPathBound_le
    {start N : ℕ} (hstart : 1 ≤ start)
    (hbudget : ParabolicRadiusBudget start N
      (hlozRadius (1 / 5 : ℝ) start N)) :
    corridorSharpRemainderPathBound start N
        (hlozRadius (1 / 5 : ℝ) start N) ≤
      14000 * ((start + N : ℕ) : ℝ) ^ (3 / 5 : ℝ) := by
  unfold corridorSharpRemainderPathBound hlozRadius
  have hterms :
      (∑ i : Fin N,
        corridorSharpRemainderBound (start + (i : ℕ))
          (Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ)
            (start + (i : ℕ)))
          (Erdos1166.HLOZLemmaA8.corridorRadius (1 / 5 : ℝ)
            (start + (i : ℕ) + 1))) ≤
        ∑ i : Fin N,
          7000 * ((start + (i : ℕ) : ℕ) : ℝ) ^ (-(2 / 5 : ℝ)) := by
    apply Finset.sum_le_sum
    intro i hi
    apply sharp_bound (by omega)
    simpa only [hlozRadius, Fin.val_castSucc, Fin.val_succ, Nat.add_assoc] using hbudget i
  have hsum := sum_fin_add_rpow_neg_two_fifths_le start N hstart
  have hNpow : (N : ℝ) ^ (3 / 5 : ℝ) ≤
      ((start + N : ℕ) : ℝ) ^ (3 / 5 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.le_add_left N start)
      (by norm_num)
  calc
    _ ≤ ∑ i : Fin N,
          7000 * ((start + (i : ℕ) : ℕ) : ℝ) ^ (-(2 / 5 : ℝ)) := hterms
    _ = 7000 * (∑ i : Fin N,
          ((start + (i : ℕ) : ℕ) : ℝ) ^ (-(2 / 5 : ℝ))) := by
      rw [Finset.mul_sum]
    _ ≤ 7000 * (2 * (N : ℝ) ^ (3 / 5 : ℝ)) := by gcongr
    _ ≤ 14000 * ((start + N : ℕ) : ℝ) ^ (3 / 5 : ℝ) := by
      nlinarith

lemma corridorComparisonCostBound_le
    {start N : ℕ} (hstart : 1 ≤ start)
    (hbudget : ParabolicRadiusBudget start N
      (hlozRadius (1 / 5 : ℝ) start N)) :
    corridorComparisonCostBound start N
        (hlozRadius (1 / 5 : ℝ) start N) ≤
      2 * (N : ℝ) +
        15000 * ((start + N : ℕ) : ℝ) ^ (3 / 5 : ℝ) := by
  have hd := corridorDriftBound_le (start := start) (N := N) hstart
  have hm := corridorDenominatorMismatchPathBound_le hstart hbudget
  have hs := corridorSharpRemainderPathBound_le hstart hbudget
  have hbase : (1 : ℝ) ≤ (start + N : ℕ) := by exact_mod_cast (show 1 ≤ start + N by omega)
  have hp : ((start + N : ℕ) : ℝ) ^ (1 / 5 : ℝ) ≤
      ((start + N : ℕ) : ℝ) ^ (3 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)
  unfold corridorComparisonCostBound
  have hp0 : 0 ≤ ((start + N : ℕ) : ℝ) ^ (3 / 5 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  linarith

lemma iteratedRhoStart_cast_le_succ_rpow
    {rho : ℝ} (hrho0 : 0 ≤ rho) (k n : ℕ) :
    (Erdos1166.HLOZLemmaA8.iteratedRhoStart rho k n : ℝ) ≤
      ((n + 1 : ℕ) : ℝ) ^ (rho ^ k) := by
  induction k generalizing n with
  | zero => simp [Erdos1166.HLOZLemmaA8.iteratedRhoStart]
  | succ k ih =>
      let s := Erdos1166.HLOZLemmaA8.rhoBlockStart rho n
      let u := s - 1
      have hih := ih u
      by_cases hs0 : s = 0
      · have hu0 : u = 0 := by simp [u, hs0]
        have hih1 :
            (Erdos1166.HLOZLemmaA8.iteratedRhoStart rho k u : ℝ) ≤ 1 := by
          simpa [hu0] using hih
        have hone : (1 : ℝ) ≤
            ((n + 1 : ℕ) : ℝ) ^ (rho ^ (k + 1)) :=
          Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n + 1 by omega))
            (pow_nonneg hrho0 _)
        change (Erdos1166.HLOZLemmaA8.iteratedRhoStart rho k u : ℝ) ≤ _
        exact hih1.trans hone
      have hus : u + 1 = s := by
        dsimp [u]
        omega
      have hs : (s : ℝ) ≤ (n : ℝ) ^ rho := by
        dsimp [s, Erdos1166.HLOZLemmaA8.rhoBlockStart]
        exact Nat.floor_le (Real.rpow_nonneg (by positivity) _)
      have hk0 : 0 ≤ rho ^ k := pow_nonneg hrho0 _
      have hbase : (s : ℝ) ^ (rho ^ k) ≤
          ((n : ℝ) ^ rho) ^ (rho ^ k) :=
        Real.rpow_le_rpow (by positivity) hs hk0
      have hcombine : ((n : ℝ) ^ rho) ^ (rho ^ k) =
          (n : ℝ) ^ (rho ^ (k + 1)) := by
        rw [← Real.rpow_mul (Nat.cast_nonneg n)]
        congr 1
        rw [pow_succ]
        ring
      have hnbase : (n : ℝ) ^ (rho ^ (k + 1)) ≤
          ((n + 1 : ℕ) : ℝ) ^ (rho ^ (k + 1)) :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.le_succ n)
          (pow_nonneg hrho0 _)
      change (Erdos1166.HLOZLemmaA8.iteratedRhoStart rho k
        (Erdos1166.HLOZLemmaA8.rhoBlockStart rho n - 1) : ℝ) ≤ _
      exact hih.trans (by rw [hus]; exact hbase.trans (hcombine.le.trans hnbase))

lemma succ_rpow_le_two_mul {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) :
    ((n + 1 : ℕ) : ℝ) ^ p ≤ 2 * (n : ℝ) ^ p := by
  have hbase : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    exact_mod_cast (show n + 1 ≤ 2 * n by omega)
  have hpow := Real.rpow_le_rpow (by positivity) hbase hp0
  have htwo : (2 : ℝ) ^ p ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp1
    simpa using this
  calc
    ((n + 1 : ℕ) : ℝ) ^ p ≤ (2 * (n : ℝ)) ^ p := hpow
    _ = (2 : ℝ) ^ p * (n : ℝ) ^ p := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
    _ ≤ 2 * (n : ℝ) ^ p := by gcongr

lemma appendix_iteratedStart_cube_le :
    ∀ n : ℕ, 1 ≤ n →
      (Erdos1166.HLOZLemmaA8.iteratedRhoStart appendixBlockRho
          (appendixBlockIndex + 1) n : ℝ) ^ 3 ≤
        2 * (n : ℝ) ^ (3 / 8 : ℝ) := by
  intro n hn
  let m := Erdos1166.HLOZLemmaA8.iteratedRhoStart appendixBlockRho
    (appendixBlockIndex + 1) n
  change (m : ℝ) ^ 3 ≤ 2 * (n : ℝ) ^ (3 / 8 : ℝ)
  have hm := iteratedRhoStart_cast_le_succ_rpow
    (rho := appendixBlockRho) (by norm_num [appendixBlockRho])
    (appendixBlockIndex + 1) n
  have hbase : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n + 1 by omega)
  have hexp : appendixBlockRho ^ (appendixBlockIndex + 1) ≤ (1 : ℝ) / 8 :=
    appendixBlockRho_pow_succ_index_le_one_eighth
  have hm' : (m : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ (1 / 8 : ℝ) :=
    hm.trans (Real.rpow_le_rpow_of_exponent_le hbase hexp)
  have hm3 : (m : ℝ) ^ 3 ≤
      (((n + 1 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) ^ 3 :=
    pow_le_pow_left₀ (Nat.cast_nonneg m) hm' 3
  have heq : (((n + 1 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) ^ 3 =
      ((n + 1 : ℕ) : ℝ) ^ (3 / 8 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    norm_num
  have hsucc := succ_rpow_le_two_mul
    (p := (3 / 8 : ℝ)) (by norm_num) (by norm_num) hn
  exact hm3.trans (heq.le.trans hsucc)

noncomputable def appendixA7CostConstant : ℝ :=
  15005 + ((appendixBlockIndex + 1 : ℕ) : ℝ) *
    (655360100 + (4 + 64 / (2 * appendixProfileDelta)))

lemma appendixA7CostConstant_nonneg : 0 ≤ appendixA7CostConstant := by
  unfold appendixA7CostConstant appendixProfileDelta
  positivity

lemma appendix_iteratedTailA7_quantitative_lower
    {n : ℕ} (hn : 1 ≤ n)
    (hmpos : 1 ≤ Erdos1166.HLOZLemmaA8.iteratedRhoStart appendixBlockRho
      (appendixBlockIndex + 1) n)
    (hmle : Erdos1166.HLOZLemmaA8.iteratedRhoStart appendixBlockRho
      (appendixBlockIndex + 1) n ≤ n)
    (hbudget : ParabolicRadiusBudget
      (Erdos1166.HLOZLemmaA8.iteratedRhoStart appendixBlockRho
        (appendixBlockIndex + 1) n)
      (n - Erdos1166.HLOZLemmaA8.iteratedRhoStart appendixBlockRho
        (appendixBlockIndex + 1) n)
      (hlozRadius appendixProfileDelta
        (Erdos1166.HLOZLemmaA8.iteratedRhoStart appendixBlockRho
          (appendixBlockIndex + 1) n)
        (n - Erdos1166.HLOZLemmaA8.iteratedRhoStart appendixBlockRho
          (appendixBlockIndex + 1) n))) :
    Real.exp (-2 * (n : ℝ) -
        appendixA7CostConstant * (n : ℝ) ^ (753 / 1250 : ℝ)) ≤
      iteratedTailA7 appendixBlockRho appendixProfileDelta
        appendixBlockIndex n := by
  let m := Erdos1166.HLOZLemmaA8.iteratedRhoStart appendixBlockRho
    (appendixBlockIndex + 1) n
  change 1 ≤ m at hmpos
  change m ≤ n at hmle
  have hsum : m + (n - m) = n := by omega
  have hnorm : pathNormalizationCost m (n - m)
        (hlozRadius appendixProfileDelta m (n - m)) ≤
      5 * ((m + (n - m) : ℕ) : ℝ) ^ (1 / 5 : ℝ) := by
    simpa only [appendixProfileDelta] using
      pathNormalizationCost_le (start := m) (N := n - m) hmpos
  have hcomp : corridorComparisonCostBound m (n - m)
        (hlozRadius appendixProfileDelta m (n - m)) ≤
      2 * ((n - m : ℕ) : ℝ) +
        15000 * ((m + (n - m) : ℕ) : ℝ) ^ (3 / 5 : ℝ) := by
    simpa only [appendixProfileDelta] using
      corridorComparisonCostBound_le (start := m) (N := n - m)
        hmpos hbudget
  rw [hsum] at hnorm hcomp
  have hnbase : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hp15 : (n : ℝ) ^ (1 / 5 : ℝ) ≤
      (n : ℝ) ^ (753 / 1250 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hnbase (by norm_num)
  have hp35 : (n : ℝ) ^ (3 / 5 : ℝ) ≤
      (n : ℝ) ^ (753 / 1250 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hnbase (by norm_num)
  have hN : ((n - m : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n m
  let block : ℝ := ((appendixBlockIndex + 1 : ℕ) : ℝ) *
    (655360100 + (4 + 64 / (2 * appendixProfileDelta))) *
      (n : ℝ) ^ (753 / 1250 : ℝ)
  have hcost :
      pathNormalizationCost m (n - m)
          (hlozRadius appendixProfileDelta m (n - m)) +
        corridorComparisonCostBound m (n - m)
          (hlozRadius appendixProfileDelta m (n - m)) + block ≤
      2 * (n : ℝ) +
        appendixA7CostConstant * (n : ℝ) ^ (753 / 1250 : ℝ) := by
    dsimp [block, appendixA7CostConstant]
    have hp0 : 0 ≤ (n : ℝ) ^ (753 / 1250 : ℝ) :=
      Real.rpow_nonneg (by positivity) _
    linarith
  unfold iteratedTailA7
  rw [appendix_block_exponent_eq]
  change Real.exp _ ≤
    Real.exp (-pathNormalizationCost m (n - m)
      (hlozRadius appendixProfileDelta m (n - m))) *
      Real.exp (-corridorComparisonCostBound m (n - m)
        (hlozRadius appendixProfileDelta m (n - m))) *
      Real.exp (-block)
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

noncomputable def appendixSourceA7CostConstant : ℝ :=
  appendixA7CostConstant + 20

lemma appendixSourceA7CostConstant_nonneg :
    0 ≤ appendixSourceA7CostConstant := by
  unfold appendixSourceA7CostConstant
  positivity [appendixA7CostConstant_nonneg]

lemma appendixSourceA7_quantitative_lower
    {n : ℕ} (hn : 1 ≤ n)
    (hmpos : 3 ≤ Erdos1166.HLOZLemmaA8.iteratedRhoStart appendixBlockRho
      (appendixBlockIndex + 1) n)
    (hmle : Erdos1166.HLOZLemmaA8.iteratedRhoStart appendixBlockRho
      (appendixBlockIndex + 1) n ≤ n)
    (hbudget : ParabolicRadiusBudget
      (Erdos1166.HLOZLemmaA8.iteratedRhoStart appendixBlockRho
        (appendixBlockIndex + 1) n)
      (n - Erdos1166.HLOZLemmaA8.iteratedRhoStart appendixBlockRho
        (appendixBlockIndex + 1) n)
      (hlozRadius appendixProfileDelta
        (Erdos1166.HLOZLemmaA8.iteratedRhoStart appendixBlockRho
          (appendixBlockIndex + 1) n)
        (n - Erdos1166.HLOZLemmaA8.iteratedRhoStart appendixBlockRho
          (appendixBlockIndex + 1) n))) :
    Real.exp (-2 * (n : ℝ) -
        appendixSourceA7CostConstant * (n : ℝ) ^ (753 / 1250 : ℝ)) ≤
      appendixSourceA7 n := by
  let m := Erdos1166.HLOZLemmaA8.iteratedRhoStart appendixBlockRho
    (appendixBlockIndex + 1) n
  change 3 ≤ m at hmpos
  have hm3 := appendix_iteratedStart_cube_le n hn
  change (m : ℝ) ^ 3 ≤ 2 * (n : ℝ) ^ (3 / 8 : ℝ) at hm3
  have hnbase : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (3 / 8 : ℝ) ≤
      (n : ℝ) ^ (753 / 1250 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hnbase (by norm_num)
  have hprefix0 := exp_neg_ten_mul_cube_le_finitePrefixFactor
    (delta := appendixProfileDelta) (by norm_num [appendixProfileDelta]) hmpos
  have hprefix : Real.exp (-20 * (n : ℝ) ^ (753 / 1250 : ℝ)) ≤
      finiteBridgeLower appendixProfileDelta (m - 1) *
        halfNegBinPathWeight (parabolicProfile 2 (m - 3)) := by
    apply (Real.exp_le_exp.mpr ?_).trans hprefix0
    calc
      -20 * (n : ℝ) ^ (753 / 1250 : ℝ) ≤
          -20 * (n : ℝ) ^ (3 / 8 : ℝ) := by linarith only [hpow]
      _ ≤ -10 * (m : ℝ) ^ 3 := by linarith only [hm3]
  have htail := appendix_iteratedTailA7_quantitative_lower hn
    (show 1 ≤ m by omega) hmle hbudget
  change Real.exp _ ≤ iteratedTailA7 appendixBlockRho appendixProfileDelta
    appendixBlockIndex n at htail
  unfold appendixSourceA7 iteratedSourceA7
  change Real.exp _ ≤
    finiteBridgeLower appendixProfileDelta (m - 1) *
      halfNegBinPathWeight (parabolicProfile 2 (m - 3)) *
        iteratedTailA7 appendixBlockRho appendixProfileDelta appendixBlockIndex n
  calc
    Real.exp (-2 * (n : ℝ) -
        appendixSourceA7CostConstant * (n : ℝ) ^ (753 / 1250 : ℝ)) =
      Real.exp (-20 * (n : ℝ) ^ (753 / 1250 : ℝ)) *
        Real.exp (-2 * (n : ℝ) -
          appendixA7CostConstant * (n : ℝ) ^ (753 / 1250 : ℝ)) := by
            rw [← Real.exp_add]
            unfold appendixSourceA7CostConstant
            congr 1
            ring
    _ ≤ (finiteBridgeLower appendixProfileDelta (m - 1) *
        halfNegBinPathWeight (parabolicProfile 2 (m - 3))) *
          iteratedTailA7 appendixBlockRho appendixProfileDelta
            appendixBlockIndex n :=
      mul_le_mul hprefix htail (Real.exp_pos _).le
        (mul_nonneg (finiteBridgeLower_pos _ _).le
          (halfNegBinPathWeight_parabolicProfile_pos (by norm_num)).le)

theorem eventually_appendixSourceA7_quantitative_lower :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-2 * (n : ℝ) -
          appendixSourceA7CostConstant *
            (n : ℝ) ^ (753 / 1250 : ℝ)) ≤
        appendixSourceA7 n := by
  have hmTop := Erdos1166.HLOZLemmaA8.tendsto_iteratedRhoStart_atTop
    (rho := appendixBlockRho) (by norm_num [appendixBlockRho])
    (appendixBlockIndex + 1)
  have hmthree := hmTop.eventually (eventually_ge_atTop (3 : ℕ))
  have hbudget0 := eventually_hlozRadiusBudget
    (show appendixProfileDelta < 1 by norm_num [appendixProfileDelta])
  have hbudget := hmTop.eventually hbudget0
  have hsource := eventually_iteratedTailA7_lower
    (rho := appendixBlockRho) (delta := appendixProfileDelta)
    (by norm_num [appendixBlockRho])
    (by norm_num [appendixBlockRho])
    (by norm_num [appendixProfileDelta])
    (by norm_num [appendixProfileDelta])
    (by norm_num [appendixBlockRho, appendixProfileDelta])
    appendixBlockIndex
  filter_upwards [hmthree, hbudget, hsource, eventually_ge_atTop (1 : ℕ)] with
    n hm3 hbud hsource hn
  exact appendixSourceA7_quantitative_lower hn hm3 hsource.2.1
    (hbud (n - Erdos1166.HLOZLemmaA8.iteratedRhoStart appendixBlockRho
      (appendixBlockIndex + 1) n))

end Erdos1166.HLOZAppendixAFirstMoment
