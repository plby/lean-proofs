/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The coarse divisor-profile bound for covers with small Simpson weight.
Informal source: BBMST Lemma 6.3 and the initial split in Section 7.2.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.FrameCodeBound

namespace Erdos1189

open Finset

lemma largeCoordinates_zero (N : ℕ) : largeCoordinates N 0 = univ := by
  apply filter_eq_self.mpr
  intro i _
  exact coordinateSize_pos i

lemma largeCoordinateWeight_zero (N : ℕ) : largeCoordinateWeight N 0 = simpsonWeight N := by
  rw [largeCoordinateWeight, largeCoordinates_zero, sum_coordinateSize]

lemma powersetCard_card_le_exp {α : Type*} (S : Finset α) (k : ℕ) (hS : 0 < S.card) :
    ((S.powersetCard k).card : ℝ) ≤ Real.exp ((k : ℝ) * Real.log S.card) := by
  rw [card_powersetCard, Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hS)]
  exact_mod_cast Nat.choose_le_pow S.card k

lemma sqrt_le_half_sqrt {u n : ℝ} (hu : 0 ≤ u) (hn : 0 ≤ n) (h : 4 * u ≤ n) :
    Real.sqrt u ≤ Real.sqrt n / 2 := by
  have hu2 := Real.sq_sqrt hu
  have hn2 := Real.sq_sqrt hn
  have hun := Real.sqrt_nonneg u
  have hnn := Real.sqrt_nonneg n
  nlinarith

lemma sparse_entropy_le_frameCodeBound {a b E n : ℝ} {u : ℕ} (ha : 0 < a)
    (hb : 0 ≤ b) (hn : 1 < n) (hsmall : 4 * (u : ℝ) ≤ n) :
    n * (b * rootLog u + E) ≤ frameCodeBound a b E n n := by
  have hroot := rootLog_cutoff ha hn u
  have hsqrt := sqrt_le_half_sqrt (Nat.cast_nonneg u) (by linarith) hsmall
  have hcoef : Real.sqrt u ≤ (2 / 3 : ℝ) * Real.sqrt n := by
    have := Real.sqrt_nonneg n
    linarith
  have hdiv := div_le_div_of_nonneg_right hcoef
    (show 0 ≤ Real.sqrt a * Real.sqrt (Real.log n) by positivity)
  have hupper : rootLog u ≤
      (2 / (3 * Real.sqrt a)) * Real.sqrt n / Real.sqrt (Real.log n) +
        Real.sqrt (n ^ a) / Real.sqrt (Real.log 2) := by
    apply hroot.trans
    apply add_le_add _ le_rfl
    convert hdiv using 1
    ring
  have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hupper hb)
    (show 0 ≤ n by linarith)
  unfold frameCodeBound
  calc
    _ = n * (b * rootLog u) + n * E := by ring
    _ ≤ n * (b * ((2 / (3 * Real.sqrt a)) * Real.sqrt n / Real.sqrt (Real.log n) +
        Real.sqrt (n ^ a) / Real.sqrt (Real.log 2))) + n * E := add_le_add h le_rfl
    _ = _ := by ring

lemma sparse_profile_count {N k : ℕ} {a b E η : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hE : 0 ≤ E) (hη : 0 ≤ η) (hk : 1 < k) (hsmall : 4 * simpsonWeight N ≤ k)
    (hprofile : Real.log (boundedProfileModuli N N.factorization).card ≤
      b * rootLog (simpsonWeight N) + E) :
    (((boundedProfileModuli N N.factorization).powersetCard k).card : ℝ) ≤
      Real.exp (frameCodeBound a b E k ((1 + η) * k)) := by
  apply (powersetCard_card_le_exp _ k (boundedProfileModuli_card_pos _ _)).trans
  apply Real.exp_le_exp.mpr
  apply (mul_le_mul_of_nonneg_left hprofile (Nat.cast_nonneg k)).trans
  apply (sparse_entropy_le_frameCodeBound ha hb (by exact_mod_cast hk)
    (by exact_mod_cast hsmall)).trans
  exact frameCodeBound_mono hb hE (Nat.cast_nonneg _) (by nlinarith [Nat.cast_nonneg k (α := ℝ)])

end Erdos1189
