/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Finite logarithmic lower bounds for distinct-modulus arithmetic frames.
Informal source: the profile selection estimate in Section 8.3 of the selected writeup.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.FrameCount
import ErdosProblems.Erdos1189.ArithmeticProfiles
import ErdosProblems.Erdos1189.BinomialEntropy

namespace Erdos1189

open Finset

lemma coordinate_weight_pos {N : ℕ} (c : PrimeCoordinate N) : 1 ≤ coordinateSize c - 1 := by
  have := (Nat.prime_of_mem_primeFactors c.1.2).two_le
  change 1 ≤ c.1.val - 1
  omega

lemma coordinate_weight_le {N : ℕ} (c : PrimeCoordinate N) :
    coordinateSize c - 1 ≤ simpsonWeight N := by
  rw [← sum_coordinateSize]
  exact single_le_sum (fun i _ => Nat.zero_le (coordinateSize i - 1)) (mem_univ c)

lemma sum_coordinate_weight_log_le (N : ℕ) :
    (∑ c : PrimeCoordinate N, ((coordinateSize c - 1 : ℕ) : ℝ) *
      Real.log (coordinateSize c - 1 : ℕ)) ≤
        (simpsonWeight N : ℝ) * Real.log (simpsonWeight N + 1 : ℕ) := by
  calc
    _ ≤ ∑ c : PrimeCoordinate N, ((coordinateSize c - 1 : ℕ) : ℝ) *
        Real.log (simpsonWeight N + 1 : ℕ) := by
      apply sum_le_sum
      intro c _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.log_le_log
      · exact_mod_cast (show 0 < coordinateSize c - 1 from coordinate_weight_pos c)
      · exact_mod_cast (coordinate_weight_le c).trans (Nat.le_succ _)
    _ = _ := by rw [← sum_mul, ← Nat.cast_sum, sum_coordinateSize]

theorem log_frameCount_lower {N : ℕ} (hN : 1 < N)
    (rank : PrimeCoordinate N → ℕ)
    (hstock : ∀ c, coordinateSize c - 1 ≤ (admissibleFrameModuli rank c).card) :
    (∑ c : PrimeCoordinate N, ((coordinateSize c - 1 : ℕ) : ℝ) *
      Real.log (admissibleFrameModuli rank c).card) -
        2 * simpsonWeight N * Real.log (simpsonWeight N + 1 : ℕ) ≤
      Real.log (irreducibleCount (simpsonWeight N + 1)) := by
  have hchoose : ∀ c : PrimeCoordinate N,
      0 < (admissibleFrameModuli rank c).card.choose (coordinateSize c - 1) :=
    fun c => Nat.choose_pos (hstock c)
  have hcount := frameCount_le_irreducibleCount hN rank
  have hlog := Real.log_le_log
    (show (0 : ℝ) <
      (∏ c : PrimeCoordinate N,
        (admissibleFrameModuli rank c).card.choose (coordinateSize c - 1) : ℕ) by
      exact_mod_cast prod_pos (fun c _ => hchoose c))
    (show ((∏ c : PrimeCoordinate N,
        (admissibleFrameModuli rank c).card.choose (coordinateSize c - 1) : ℕ) : ℝ) ≤
      irreducibleCount (simpsonWeight N + 1) by exact_mod_cast hcount)
  rw [Nat.cast_prod, Real.log_prod (fun c _ => by exact_mod_cast (hchoose c).ne')] at hlog
  have hsum := sum_le_sum (s := (univ : Finset (PrimeCoordinate N)))
    (fun c _ => log_choose_lower (coordinate_weight_pos c) (hstock c))
  simp only [sum_sub_distrib] at hsum
  have herror := sum_coordinate_weight_log_le N
  have hdouble : (∑ c : PrimeCoordinate N,
      2 * ((coordinateSize c - 1 : ℕ) : ℝ) * Real.log (coordinateSize c - 1 : ℕ)) =
        2 * ∑ c : PrimeCoordinate N,
          ((coordinateSize c - 1 : ℕ) : ℝ) * Real.log (coordinateSize c - 1 : ℕ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro c _
    ring
  rw [hdouble] at hsum
  linarith

noncomputable def frameEntropy {N : ℕ} (rank : PrimeCoordinate N → ℕ) : ℝ :=
  ∑ c : PrimeCoordinate N, ((coordinateSize c - 1 : ℕ) : ℝ) *
    Real.log (profileModuli rank c).card

theorem frameEntropy_lower_count {N : ℕ} (hN : 1 < N)
    (rank : PrimeCoordinate N → ℕ)
    (hstock : ∀ c, coordinateSize c - 1 ≤ (admissibleFrameModuli rank c).card)
    (hprofile : ∀ c, (profileModuli rank c).card ≤ 2 * (admissibleFrameModuli rank c).card) :
    frameEntropy rank - (simpsonWeight N : ℝ) *
      (Real.log 2 + 2 * Real.log (simpsonWeight N + 1 : ℕ)) ≤
        Real.log (irreducibleCount (simpsonWeight N + 1)) := by
  have hbase := log_frameCount_lower hN rank hstock
  have hsum : frameEntropy rank ≤
      (∑ c : PrimeCoordinate N, ((coordinateSize c - 1 : ℕ) : ℝ) *
        Real.log (admissibleFrameModuli rank c).card) + simpsonWeight N * Real.log 2 := by
    have hp : ∀ c, (0 : ℝ) < (profileModuli rank c).card := by
      intro c
      rw [card_profileModuli]
      exact_mod_cast prod_pos (fun _ _ => Nat.succ_pos _)
    have ha : ∀ c, (0 : ℝ) < (admissibleFrameModuli rank c).card := by
      intro c
      exact_mod_cast (coordinate_weight_pos c).trans (hstock c)
    have hh := sum_le_sum (s := (univ : Finset (PrimeCoordinate N))) (fun c _ =>
      mul_le_mul_of_nonneg_left
        (Real.log_le_log (hp c) (show ((profileModuli rank c).card : ℝ) ≤
          2 * (admissibleFrameModuli rank c).card by exact_mod_cast hprofile c))
        (show (0 : ℝ) ≤ (coordinateSize c - 1 : ℕ) by positivity))
    simp only [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ha _).ne', mul_add,
      sum_add_distrib, ← sum_mul, ← Nat.cast_sum, sum_coordinateSize] at hh
    dsimp [frameEntropy]
    linarith
  linarith

end Erdos1189
