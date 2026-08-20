/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos733.Defs
import ErdosProblems.Erdos733.Counting
import ErdosProblems.Erdos733.RichLines
import ErdosProblems.Erdos733.Analytic

/-!
# Erdős Problem 733: geometric bounds for the dyadic buckets

The witnessing lines form a finset, so filtering them by their number of
incident points counts multiplicities of equal line sizes correctly.  Each
such filtered finset injects into the finset of all rich lines supplied by
Szemerédi--Trotter.
-/

namespace Erdos733

noncomputable section

open Classical

/-- Filtering the multiset of line sizes is the same as filtering the
finset of distinct witnessing lines and then taking its cardinality. -/
lemma card_dyadicBucket_lineSizeSequence
    (P : Finset Point) (L : Finset Line) (i : ℕ) :
    (dyadicBucket i (lineSizeSequence P L : Multiset ℕ)).card =
      (L.filter fun ℓ ↦ InDyadicBucket i (lineCount P ℓ)).card := by
  rw [lineSizeSequence_toMultiset]
  rw [dyadicBucket, lineSizeMultiset, Multiset.filter_map, Multiset.card_map]
  rfl

/-- A bucket whose left endpoint exceeds `n` is empty in every compatible
sequence on `n` points. -/
lemma LineCompatible.dyadicBucket_eq_zero_of_lt_scale
    {n : ℕ} {X : List ℕ} (hX : LineCompatible n X) (i : ℕ)
    (hnq : n < dyadicScale i) :
    dyadicBucket i (X : Multiset ℕ) = 0 := by
  rw [dyadicBucket, Multiset.filter_eq_nil]
  intro x hxX hxBucket
  have hxList : x ∈ X := Multiset.mem_coe.mp hxX
  have hxn := (hX.mem_bounds hxList).2
  exact (not_le_of_gt hnq) ((show dyadicScale i ≤ x from hxBucket.1).trans hxn)

/-- The rich-line estimate implies a single integral cap for every dyadic
bucket.  This is stated with the estimate as an argument so the geometric
and arithmetic parts remain separately reusable. -/
theorem exists_compatible_bucketBounds_of_globalRichLinesBound
    (hglobal : ∃ C : ℝ, 0 < C ∧
      ∀ (P : Finset Point) (k : ℕ), 2 ≤ k →
        ∃ R : Finset Line,
          (∀ ℓ, ℓ ∈ R ↔ k ≤ lineCount P ℓ) ∧
          (R.card : ℝ) ≤ C *
            ((P.card : ℝ) ^ 2 / (k : ℝ) ^ 3 +
              (P.card : ℝ) / (k : ℝ))) :
    ∃ A : ℕ, 0 < A ∧
      ∀ (n : ℕ) (X : List ℕ), LineCompatible n X →
        ∀ i : Fin n,
          (dyadicBucket i (X : Multiset ℕ)).card ≤
            dyadicAnalyticCap A n i := by
  obtain ⟨C, hC, hrich⟩ := hglobal
  obtain ⟨A, hCA⟩ := exists_nat_gt (2 * C)
  have hApos : 0 < A := by
    have hAreal : (0 : ℝ) < A := lt_trans (by positivity : (0 : ℝ) < 2 * C) hCA
    exact_mod_cast hAreal
  refine ⟨A, hApos, ?_⟩
  intro n X hX i
  by_cases hqn : dyadicScale i ≤ n
  · obtain ⟨P, hPn, L, hL, rfl⟩ := hX
    let B := L.filter fun ℓ ↦ InDyadicBucket i (lineCount P ℓ)
    have hqpos : 0 < dyadicScale i := dyadicScale_pos i
    have hq2 : 2 ≤ dyadicScale i := by
      rw [dyadicScale, pow_succ]
      have hp : 0 < 2 ^ (i : ℕ) := pow_pos (by omega) _
      omega
    obtain ⟨R, hRmem, hRcard⟩ := hrich P (dyadicScale i) hq2
    have hBR : B ⊆ R := by
      intro ℓ hℓ
      rw [hRmem]
      exact (Finset.mem_filter.mp hℓ).2.1
    have hBcard : B.card ≤ R.card := Finset.card_le_card hBR
    have hBcardR : (B.card : ℝ) ≤ (R.card : ℝ) := by
      exact_mod_cast hBcard
    have hglobalB : (B.card : ℝ) ≤ C *
        ((n : ℝ) ^ 2 / (dyadicScale i : ℝ) ^ 3 +
          (n : ℝ) / (dyadicScale i : ℝ)) := by
      apply hBcardR.trans
      simpa only [hPn] using hRcard
    have hqR : (0 : ℝ) < (dyadicScale i : ℝ) := by exact_mod_cast hqpos
    have hnR : (0 : ℝ) ≤ (n : ℝ) := by positivity
    by_cases hsq : dyadicScale i ^ 2 ≤ n
    · have hsqR : (dyadicScale i : ℝ) ^ 2 ≤ (n : ℝ) := by
        exact_mod_cast hsq
      have hbase : (n : ℝ) * (dyadicScale i : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
        calc
          (n : ℝ) * (dyadicScale i : ℝ) ^ 2 ≤ (n : ℝ) * n :=
            mul_le_mul_of_nonneg_left hsqR hnR
          _ = (n : ℝ) ^ 2 := by ring
      have hterm : (n : ℝ) / (dyadicScale i : ℝ) ≤
          (n : ℝ) ^ 2 / (dyadicScale i : ℝ) ^ 3 := by
        apply (div_le_div_iff₀ hqR (pow_pos hqR 3)).2
        have hm := mul_le_mul_of_nonneg_right hbase hqR.le
        convert hm using 1 <;> ring
      have hpre : (B.card : ℝ) ≤
          2 * C * ((n : ℝ) ^ 2 / (dyadicScale i : ℝ) ^ 3) := by
        calc
          (B.card : ℝ) ≤ C *
              ((n : ℝ) ^ 2 / (dyadicScale i : ℝ) ^ 3 +
                (n : ℝ) / (dyadicScale i : ℝ)) := hglobalB
          _ ≤ C * (2 * ((n : ℝ) ^ 2 / (dyadicScale i : ℝ) ^ 3)) := by
            exact mul_le_mul_of_nonneg_left (by linarith) hC.le
          _ = 2 * C * ((n : ℝ) ^ 2 / (dyadicScale i : ℝ) ^ 3) := by ring
      have hdiv : (B.card : ℝ) ≤
          (2 * C * (n : ℝ) ^ 2) / (dyadicScale i : ℝ) ^ 3 := by
        convert hpre using 1 <;> ring
      have hmul := (le_div_iff₀ (pow_pos hqR 3)).mp hdiv
      have hmulA : (B.card : ℝ) * (dyadicScale i : ℝ) ^ 3 ≤
          (A : ℝ) * (n : ℝ) ^ 2 := by
        calc
          (B.card : ℝ) * (dyadicScale i : ℝ) ^ 3 ≤
              (2 * C) * (n : ℝ) ^ 2 := by
            convert hmul using 1 <;> ring
          _ ≤ (A : ℝ) * (n : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hCA.le (sq_nonneg (n : ℝ))
      have hmulNat : B.card * dyadicScale i ^ 3 ≤ A * n ^ 2 := by
        exact_mod_cast hmulA
      rw [card_dyadicBucket_lineSizeSequence]
      rw [dyadicAnalyticCap_of_sq_le hsq]
      exact (Nat.le_div_iff_mul_le (pow_pos hqpos 3)).2 hmulNat
    · have hnsq : n < dyadicScale i ^ 2 := Nat.lt_of_not_ge hsq
      have hsqR : (n : ℝ) ≤ (dyadicScale i : ℝ) ^ 2 := by
        exact_mod_cast hnsq.le
      have hbase : (n : ℝ) ^ 2 ≤
          (n : ℝ) * (dyadicScale i : ℝ) ^ 2 := by
        calc
          (n : ℝ) ^ 2 = (n : ℝ) * n := by ring
          _ ≤ (n : ℝ) * (dyadicScale i : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left hsqR hnR
      have hterm : (n : ℝ) ^ 2 / (dyadicScale i : ℝ) ^ 3 ≤
          (n : ℝ) / (dyadicScale i : ℝ) := by
        apply (div_le_div_iff₀ (pow_pos hqR 3) hqR).2
        have hm := mul_le_mul_of_nonneg_right hbase hqR.le
        convert hm using 1 <;> ring
      have hpre : (B.card : ℝ) ≤
          2 * C * ((n : ℝ) / (dyadicScale i : ℝ)) := by
        calc
          (B.card : ℝ) ≤ C *
              ((n : ℝ) ^ 2 / (dyadicScale i : ℝ) ^ 3 +
                (n : ℝ) / (dyadicScale i : ℝ)) := hglobalB
          _ ≤ C * (2 * ((n : ℝ) / (dyadicScale i : ℝ))) := by
            exact mul_le_mul_of_nonneg_left (by linarith) hC.le
          _ = 2 * C * ((n : ℝ) / (dyadicScale i : ℝ)) := by ring
      have hdiv : (B.card : ℝ) ≤
          (2 * C * (n : ℝ)) / (dyadicScale i : ℝ) := by
        convert hpre using 1 <;> ring
      have hmul := (le_div_iff₀ hqR).mp hdiv
      have hmulA : (B.card : ℝ) * (dyadicScale i : ℝ) ≤
          (A : ℝ) * n := by
        calc
          (B.card : ℝ) * (dyadicScale i : ℝ) ≤ (2 * C) * n := by
            convert hmul using 1 <;> ring
          _ ≤ (A : ℝ) * n :=
            mul_le_mul_of_nonneg_right hCA.le hnR
      have hmulNat : B.card * dyadicScale i ≤ A * n := by
        exact_mod_cast hmulA
      rw [card_dyadicBucket_lineSizeSequence]
      rw [dyadicAnalyticCap_of_lt_sq hnsq]
      exact (Nat.le_div_iff_mul_le hqpos).2 hmulNat
  · rw [hX.dyadicBucket_eq_zero_of_lt_scale i (Nat.lt_of_not_ge hqn)]
    exact Nat.zero_le _

/-- The unconditional bucket bound obtained from Szemerédi--Trotter. -/
theorem exists_compatible_bucketBounds :
    ∃ A : ℕ, 0 < A ∧
      ∀ (n : ℕ) (X : List ℕ), LineCompatible n X →
        ∀ i : Fin n,
          (dyadicBucket i (X : Multiset ℕ)).card ≤
            dyadicAnalyticCap A n i := by
  apply exists_compatible_bucketBounds_of_globalRichLinesBound
  simpa only [lineCount] using globalRichLinesBound

end

end Erdos733
