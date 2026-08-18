/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Lightweight restricted Weyl differencing

This file isolates the purely finite, complex-valued restricted-interval
Weyl machinery used by the proof of Erdős Problem 1149.  In contrast with
the corresponding development for Problem 387, it has no rational-function,
`ZMod`, conductor-elimination, or Waring-theory dependencies.

The sequence is only assumed to take values in the closed complex unit ball.
The exact cost of translating a prefix is retained, and the one-step estimate
is iterated over a finite tree of prescribed off-diagonal shifts.
-/

namespace Erdos1149

open scoped BigOperators ComplexConjugate

namespace RestrictedWeyl

/-- A correlation between two translates by multiples of one step. -/
def translatedPairCorrelation
    (z : ℕ → ℂ) (d k l x : ℕ) : ℂ :=
  z (x + k * d) * conj (z (x + l * d))

/-- Successive prescribed pair correlations.  A record `(d,k,l)` applies
the two translates `k*d` and `l*d` to the correlation constructed from the
tail of the history. -/
def iteratedPairCorrelation
    (z : ℕ → ℂ) : List (ℕ × ℕ × ℕ) → ℕ → ℂ
  | [], x => z x
  | (d, k, l) :: hs, x =>
      translatedPairCorrelation (iteratedPairCorrelation z hs) d k l x

/-- Pair correlation preserves the pointwise unit-ball condition. -/
theorem norm_iteratedPairCorrelation_le_one
    (z : ℕ → ℂ) (hz : ∀ x, ‖z x‖ ≤ 1)
    (hs : List (ℕ × ℕ × ℕ)) (x : ℕ) :
    ‖iteratedPairCorrelation z hs x‖ ≤ 1 := by
  induction hs generalizing x with
  | nil => exact hz x
  | cons h hs ih =>
      rcases h with ⟨d, k, l⟩
      simp only [iteratedPairCorrelation, translatedPairCorrelation,
        norm_mul, Complex.norm_conj]
      calc
        ‖iteratedPairCorrelation z hs (x + k * d)‖ *
            ‖iteratedPairCorrelation z hs (x + l * d)‖ ≤ 1 * 1 :=
          mul_le_mul (ih _) (ih _) (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num

/-- Exact difference between an interval sum and its translate.  Only the
initial and terminal boundary pieces remain. -/
theorem sum_range_sub_sum_range_translate
    (z : ℕ → ℂ) (P s : ℕ) :
    (∑ x ∈ Finset.range P, z x) -
        (∑ x ∈ Finset.range P, z (x + s)) =
      (∑ x ∈ Finset.range s, z x) -
        ∑ x ∈ Finset.range s, z (P + x) := by
  have hleft := Finset.sum_range_add z P s
  have hright :
      (∑ x ∈ Finset.range (P + s), z x) =
        (∑ x ∈ Finset.range s, z x) +
          ∑ x ∈ Finset.range P, z (x + s) := by
    simpa [add_comm] using Finset.sum_range_add z s P
  linear_combination -hleft + hright

/-- Translating an interval by `s` changes a sum of unit-ball terms by at
most `2s`. -/
theorem norm_sum_range_sub_translate_le
    (z : ℕ → ℂ) (hz : ∀ x, ‖z x‖ ≤ 1) (P s : ℕ) :
    ‖(∑ x ∈ Finset.range P, z x) -
        ∑ x ∈ Finset.range P, z (x + s)‖ ≤ 2 * s := by
  rw [sum_range_sub_sum_range_translate]
  calc
    ‖(∑ x ∈ Finset.range s, z x) -
        ∑ x ∈ Finset.range s, z (P + x)‖ ≤
      ‖∑ x ∈ Finset.range s, z x‖ +
        ‖∑ x ∈ Finset.range s, z (P + x)‖ := norm_sub_le _ _
    _ ≤ (∑ _x ∈ Finset.range s, (1 : ℝ)) +
        ∑ _x ∈ Finset.range s, (1 : ℝ) := by
      gcongr
      · exact (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun x _hx ↦ hz x)
      · exact (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun x _hx ↦ hz (P + x))
    _ = 2 * s := by simp; ring

/-- Exact boundary budget for averaging the translates `k*d`, `k<K`. -/
def boundaryBudget (K d : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K, 2 * ((k * d : ℕ) : ℝ)

theorem boundaryBudget_nonneg (K d : ℕ) :
    0 ≤ boundaryBudget K d := by
  unfold boundaryBudget
  positivity

/-- The averaged translated interval sum differs from `K` copies of the
original sum by at most the explicit boundary budget. -/
theorem norm_card_mul_sum_sub_shiftAverage_le
    (z : ℕ → ℂ) (hz : ∀ x, ‖z x‖ ≤ 1) (P K d : ℕ) :
    ‖(K : ℂ) * (∑ x ∈ Finset.range P, z x) -
        ∑ x ∈ Finset.range P, ∑ k ∈ Finset.range K,
          z (x + k * d)‖ ≤ boundaryBudget K d := by
  rw [Finset.sum_comm]
  have heq :
      (K : ℂ) * (∑ x ∈ Finset.range P, z x) -
          ∑ k ∈ Finset.range K, ∑ x ∈ Finset.range P,
            z (x + k * d) =
        ∑ k ∈ Finset.range K,
          ((∑ x ∈ Finset.range P, z x) -
            ∑ x ∈ Finset.range P, z (x + k * d)) := by
    simp_rw [Finset.sum_sub_distrib]
    simp
  rw [heq]
  calc
    ‖∑ k ∈ Finset.range K,
        ((∑ x ∈ Finset.range P, z x) -
          ∑ x ∈ Finset.range P, z (x + k * d))‖ ≤
      ∑ k ∈ Finset.range K,
        ‖(∑ x ∈ Finset.range P, z x) -
          ∑ x ∈ Finset.range P, z (x + k * d)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range K, 2 * ((k * d : ℕ) : ℝ) := by
      exact Finset.sum_le_sum fun k _hk ↦
        norm_sum_range_sub_translate_le z hz P (k * d)
    _ = boundaryBudget K d := rfl

/-- A convenient upper bound for the boundary budget. -/
theorem boundaryBudget_le (K d : ℕ) :
    boundaryBudget K d ≤ 2 * K ^ 2 * d := by
  unfold boundaryBudget
  calc
    (∑ k ∈ Finset.range K, 2 * ((k * d : ℕ) : ℝ)) ≤
        ∑ _k ∈ Finset.range K, 2 * ((K * d : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      exact_mod_cast Nat.mul_le_mul_left 2
        (Nat.mul_le_mul_right d (Finset.mem_range.mp hk).le)
    _ = 2 * K ^ 2 * d := by
      simp
      ring

/-- Expansion of the energy of the restricted shift average. -/
theorem sum_shiftAverage_mul_conj_eq_pairCorrelations
    (z : ℕ → ℂ) (P K d : ℕ) :
    (∑ x ∈ Finset.range P,
        (∑ k ∈ Finset.range K, z (x + k * d)) *
          conj (∑ k ∈ Finset.range K, z (x + k * d))) =
      ∑ k ∈ Finset.range K, ∑ l ∈ Finset.range K,
        ∑ x ∈ Finset.range P,
          translatedPairCorrelation z d k l x := by
  simp_rw [map_sum, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _hl
  rfl

/-- Cauchy--Schwarz and the energy expansion for the restricted shift
average. -/
theorem norm_shiftAverage_sq_le_pairCorrelations
    (z : ℕ → ℂ) (P K d : ℕ) :
    ‖∑ x ∈ Finset.range P, ∑ k ∈ Finset.range K,
        z (x + k * d)‖ ^ 2 ≤
      P * ∑ k ∈ Finset.range K, ∑ l ∈ Finset.range K,
        ‖∑ x ∈ Finset.range P,
          translatedPairCorrelation z d k l x‖ := by
  let w : ℕ → ℂ := fun x ↦ ∑ k ∈ Finset.range K, z (x + k * d)
  have htriangle :
      ‖∑ x ∈ Finset.range P, w x‖ ≤
        ∑ x ∈ Finset.range P, ‖w x‖ := norm_sum_le _ _
  have hcauchy :
      (∑ x ∈ Finset.range P, ‖w x‖) ^ 2 ≤
        (P : ℝ) * ∑ x ∈ Finset.range P, ‖w x‖ ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := Finset.range P) (f := fun x ↦ ‖w x‖))
  have henergy :
      (∑ x ∈ Finset.range P, ‖w x‖ ^ 2) ≤
        ∑ k ∈ Finset.range K, ∑ l ∈ Finset.range K,
          ‖∑ x ∈ Finset.range P,
            translatedPairCorrelation z d k l x‖ := by
    have hexpand := sum_shiftAverage_mul_conj_eq_pairCorrelations z P K d
    have hreal :
        ‖∑ x ∈ Finset.range P, w x * conj (w x)‖ =
          ∑ x ∈ Finset.range P, ‖w x‖ ^ 2 := by
      have heq :
          (∑ x ∈ Finset.range P, w x * conj (w x)) =
            (((∑ x ∈ Finset.range P, ‖w x‖ ^ 2 : ℝ) : ℂ)) := by
        calc
          (∑ x ∈ Finset.range P, w x * conj (w x)) =
              ∑ x ∈ Finset.range P,
                (((‖w x‖ ^ 2 : ℝ) : ℂ)) := by
            apply Finset.sum_congr rfl
            intro x _hx
            rw [Complex.mul_conj']
            norm_num
          _ = (((∑ x ∈ Finset.range P, ‖w x‖ ^ 2 : ℝ) : ℂ)) := by
            push_cast
            apply Finset.sum_congr rfl
            intro x _hx
            norm_num
      rw [heq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg fun _x _hx ↦ sq_nonneg _)]
    rw [← hreal]
    calc
      ‖∑ x ∈ Finset.range P, w x * conj (w x)‖ =
          ‖∑ k ∈ Finset.range K, ∑ l ∈ Finset.range K,
            ∑ x ∈ Finset.range P,
              translatedPairCorrelation z d k l x‖ := by
        rw [hexpand]
      _ ≤ ∑ k ∈ Finset.range K,
          ‖∑ l ∈ Finset.range K, ∑ x ∈ Finset.range P,
            translatedPairCorrelation z d k l x‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range K, ∑ l ∈ Finset.range K,
          ‖∑ x ∈ Finset.range P,
            translatedPairCorrelation z d k l x‖ := by
        apply Finset.sum_le_sum
        intro k _hk
        exact norm_sum_le _ _
  calc
    ‖∑ x ∈ Finset.range P, ∑ k ∈ Finset.range K,
        z (x + k * d)‖ ^ 2 ≤
      (∑ x ∈ Finset.range P, ‖w x‖) ^ 2 := by
        simpa only [w] using
          (pow_le_pow_left₀ (norm_nonneg _) htriangle 2)
    _ ≤ (P : ℝ) * ∑ x ∈ Finset.range P, ‖w x‖ ^ 2 := hcauchy
    _ ≤ (P : ℝ) *
        ∑ k ∈ Finset.range K, ∑ l ∈ Finset.range K,
          ‖∑ x ∈ Finset.range P,
            translatedPairCorrelation z d k l x‖ := by gcongr

/-- Sum of all genuinely off-diagonal restricted correlations. -/
noncomputable def offDiagonalCorrelationSum
    (z : ℕ → ℂ) (P K d : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K,
    ∑ l ∈ (Finset.range K).erase k,
      ‖∑ x ∈ Finset.range P,
        translatedPairCorrelation z d k l x‖

/-- A diagonal correlation of unit-ball terms has the trivial interval
bound. -/
theorem norm_diagonalCorrelation_le
    (z : ℕ → ℂ) (hz : ∀ x, ‖z x‖ ≤ 1)
    (P d k : ℕ) :
    ‖∑ x ∈ Finset.range P,
        translatedPairCorrelation z d k k x‖ ≤ P := by
  calc
    ‖∑ x ∈ Finset.range P,
        translatedPairCorrelation z d k k x‖ ≤
      ∑ x ∈ Finset.range P,
        ‖translatedPairCorrelation z d k k x‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ Finset.range P, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _hx
      unfold translatedPairCorrelation
      rw [norm_mul, Complex.norm_conj]
      calc
        ‖z (x + k * d)‖ * ‖z (x + k * d)‖ ≤ 1 * 1 :=
          mul_le_mul (hz _) (hz _) (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    _ = P := by simp

/-- Separate the diagonal pairs from the pair-correlation energy. -/
theorem sum_pairCorrelations_le_diagonal_add_offDiagonal
    (z : ℕ → ℂ) (hz : ∀ x, ‖z x‖ ≤ 1)
    (P K d : ℕ) :
    (∑ k ∈ Finset.range K, ∑ l ∈ Finset.range K,
        ‖∑ x ∈ Finset.range P,
          translatedPairCorrelation z d k l x‖) ≤
      (K : ℝ) * P + offDiagonalCorrelationSum z P K d := by
  calc
    (∑ k ∈ Finset.range K, ∑ l ∈ Finset.range K,
        ‖∑ x ∈ Finset.range P,
          translatedPairCorrelation z d k l x‖) =
      ∑ k ∈ Finset.range K,
        (‖∑ x ∈ Finset.range P,
            translatedPairCorrelation z d k k x‖ +
          ∑ l ∈ (Finset.range K).erase k,
            ‖∑ x ∈ Finset.range P,
              translatedPairCorrelation z d k l x‖) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.add_sum_erase _ _ hk]
    _ ≤ ∑ k ∈ Finset.range K,
        ((P : ℝ) +
          ∑ l ∈ (Finset.range K).erase k,
            ‖∑ x ∈ Finset.range P,
              translatedPairCorrelation z d k l x‖) := by
      apply Finset.sum_le_sum
      intro k _hk
      gcongr
      exact norm_diagonalCorrelation_le z hz P d k
    _ = (K : ℝ) * P + offDiagonalCorrelationSum z P K d := by
      unfold offDiagonalCorrelationSum
      simp_rw [Finset.sum_add_distrib]
      simp

/-- One exact restricted interval Weyl step, including the full translation
boundary loss. -/
theorem card_sq_mul_norm_sum_sq_le
    (z : ℕ → ℂ) (hz : ∀ x, ‖z x‖ ≤ 1) (P K d : ℕ) :
    (K : ℝ) ^ 2 * ‖∑ x ∈ Finset.range P, z x‖ ^ 2 ≤
      2 * ((P : ℝ) *
          ∑ k ∈ Finset.range K, ∑ l ∈ Finset.range K,
            ‖∑ x ∈ Finset.range P,
              translatedPairCorrelation z d k l x‖ +
        boundaryBudget K d ^ 2) := by
  let S : ℂ := ∑ x ∈ Finset.range P, z x
  let A : ℂ := ∑ x ∈ Finset.range P, ∑ k ∈ Finset.range K,
    z (x + k * d)
  let B : ℝ := boundaryBudget K d
  have hboundary : ‖(K : ℂ) * S - A‖ ≤ B := by
    simpa only [S, A, B] using
      norm_card_mul_sum_sub_shiftAverage_le z hz P K d
  have hlinear : (K : ℝ) * ‖S‖ ≤ ‖A‖ + B := by
    calc
      (K : ℝ) * ‖S‖ = ‖(K : ℂ) * S‖ := by
        rw [norm_mul, Complex.norm_natCast]
      _ ≤ ‖(K : ℂ) * S - A‖ + ‖A‖ := by
        have h := norm_add_le ((K : ℂ) * S - A) A
        simpa only [sub_add_cancel] using h
      _ ≤ ‖A‖ + B := by linarith
  have hsquare :
      ((K : ℝ) * ‖S‖) ^ 2 ≤ (‖A‖ + B) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlinear 2
  have hA :
      ‖A‖ ^ 2 ≤ (P : ℝ) *
        ∑ k ∈ Finset.range K, ∑ l ∈ Finset.range K,
          ‖∑ x ∈ Finset.range P,
            translatedPairCorrelation z d k l x‖ := by
    simpa only [A] using norm_shiftAverage_sq_le_pairCorrelations z P K d
  calc
    (K : ℝ) ^ 2 * ‖∑ x ∈ Finset.range P, z x‖ ^ 2 =
        ((K : ℝ) * ‖S‖) ^ 2 := by simp only [S]; ring
    _ ≤ (‖A‖ + B) ^ 2 := hsquare
    _ ≤ 2 * (‖A‖ ^ 2 + B ^ 2) := add_sq_le
    _ ≤ 2 * ((P : ℝ) *
          ∑ k ∈ Finset.range K, ∑ l ∈ Finset.range K,
            ‖∑ x ∈ Finset.range P,
              translatedPairCorrelation z d k l x‖ + B ^ 2) := by
      gcongr
    _ = _ := rfl

/-- Diagonal/off-diagonal form of the exact restricted interval step. -/
theorem card_sq_mul_norm_sum_sq_le_offDiagonal
    (z : ℕ → ℂ) (hz : ∀ x, ‖z x‖ ≤ 1) (P K d : ℕ) :
    (K : ℝ) ^ 2 * ‖∑ x ∈ Finset.range P, z x‖ ^ 2 ≤
      2 * ((P : ℝ) *
          ((K : ℝ) * P + offDiagonalCorrelationSum z P K d) +
        boundaryBudget K d ^ 2) := by
  calc
    (K : ℝ) ^ 2 * ‖∑ x ∈ Finset.range P, z x‖ ^ 2 ≤
      2 * ((P : ℝ) *
          ∑ k ∈ Finset.range K, ∑ l ∈ Finset.range K,
            ‖∑ x ∈ Finset.range P,
              translatedPairCorrelation z d k l x‖ +
        boundaryBudget K d ^ 2) :=
      card_sq_mul_norm_sum_sq_le z hz P K d
    _ ≤ 2 * ((P : ℝ) *
          ((K : ℝ) * P + offDiagonalCorrelationSum z P K d) +
        boundaryBudget K d ^ 2) := by
      gcongr
      exact sum_pairCorrelations_le_diagonal_add_offDiagonal z hz P K d

/-- Iteratable diagonal/off-diagonal recurrence. -/
theorem card_sq_mul_norm_iterated_sum_sq_le_offDiagonal
    (z : ℕ → ℂ) (hz : ∀ x, ‖z x‖ ≤ 1)
    (hs : List (ℕ × ℕ × ℕ)) (P K d : ℕ) :
    (K : ℝ) ^ 2 *
        ‖∑ x ∈ Finset.range P, iteratedPairCorrelation z hs x‖ ^ 2 ≤
      2 * ((P : ℝ) *
          ((K : ℝ) * P +
            offDiagonalCorrelationSum
              (iteratedPairCorrelation z hs) P K d) +
        boundaryBudget K d ^ 2) := by
  exact card_sq_mul_norm_sum_sq_le_offDiagonal
    (iteratedPairCorrelation z hs)
    (norm_iteratedPairCorrelation_le_one z hz hs) P K d

/-- A prescribed differencing step. -/
structure ConductorStep where
  shiftCount : ℕ
  stepSize : ℕ
  shiftCount_pos : 0 < shiftCount

/-- Histories are listed in the same order as `iteratedPairCorrelation`:
the most recently chosen step is prepended. -/
abbrev History := List (ℕ × ℕ × ℕ)

/-- All ordered genuinely off-diagonal pairs of shifts below `K`. -/
def offDiagonalPairs (K : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range K).product (Finset.range K)).filter fun kl ↦ kl.1 ≠ kl.2

@[simp] theorem mem_offDiagonalPairs_iff {K k l : ℕ} :
    (k, l) ∈ offDiagonalPairs K ↔ k < K ∧ l < K ∧ k ≠ l := by
  simp [offDiagonalPairs, and_assoc]

/-- The immediate children of a history at one conductor step. -/
def offDiagonalChildren (s : ConductorStep) (hs : History) :
    Finset History :=
  (offDiagonalPairs s.shiftCount).image fun kl ↦
    (s.stepSize, kl.1, kl.2) :: hs

theorem cons_mem_offDiagonalChildren
    (s : ConductorStep) (hs : History) {k l : ℕ}
    (hk : k < s.shiftCount) (hl : l < s.shiftCount) (hne : k ≠ l) :
    (s.stepSize, k, l) :: hs ∈ offDiagonalChildren s hs := by
  apply Finset.mem_image.mpr
  exact ⟨(k, l), mem_offDiagonalPairs_iff.mpr ⟨hk, hl, hne⟩, rfl⟩

/-- The leaves obtained after applying every prescribed step. -/
def offDiagonalHistoryLeaves :
    List ConductorStep → History → Finset History
  | [], hs => {hs}
  | s :: ss, hs =>
      (offDiagonalChildren s hs).biUnion fun hs' ↦
        offDiagonalHistoryLeaves ss hs'

/-- The right-hand side of one restricted Weyl step after every child norm
has been bounded by `next`. -/
def stepRadicand (P : ℕ) (s : ConductorStep) (next : ℝ) : ℝ :=
  2 * ((P : ℝ) *
      ((s.shiftCount : ℝ) * P +
        (s.shiftCount : ℝ) * (s.shiftCount - 1 : ℕ) * next) +
    boundaryBudget s.shiftCount s.stepSize ^ 2)

theorem stepRadicand_nonneg
    (P : ℕ) (s : ConductorStep) {next : ℝ} (hnext : 0 ≤ next) :
    0 ≤ stepRadicand P s next := by
  unfold stepRadicand
  positivity

/-- The recursive real envelope for a complete finite history tree. -/
noncomputable def finiteHistoryEnvelope (P : ℕ) (terminal : ℝ) :
    List ConductorStep → ℝ
  | [] => terminal
  | s :: ss =>
      Real.sqrt (stepRadicand P s (finiteHistoryEnvelope P terminal ss)) /
        s.shiftCount

theorem finiteHistoryEnvelope_nonneg
    (P : ℕ) {terminal : ℝ} (hterminal : 0 ≤ terminal)
    (steps : List ConductorStep) :
    0 ≤ finiteHistoryEnvelope P terminal steps := by
  induction steps with
  | nil => simpa [finiteHistoryEnvelope] using hterminal
  | cons s ss ih =>
      simp only [finiteHistoryEnvelope]
      positivity

/-- The off-diagonal correlation sum at a node is bounded by the number of
ordered off-diagonal children times a common child bound. -/
theorem offDiagonalCorrelationSum_le_children
    (z : ℕ → ℂ) (P : ℕ) (s : ConductorStep) (hs : History) {E : ℝ}
    (hchild : ∀ k ∈ Finset.range s.shiftCount,
      ∀ l ∈ (Finset.range s.shiftCount).erase k,
        ‖∑ x ∈ Finset.range P,
          iteratedPairCorrelation z ((s.stepSize, k, l) :: hs) x‖ ≤ E) :
    offDiagonalCorrelationSum (iteratedPairCorrelation z hs)
        P s.shiftCount s.stepSize ≤
      (s.shiftCount : ℝ) * (s.shiftCount - 1 : ℕ) * E := by
  unfold offDiagonalCorrelationSum
  calc
    (∑ k ∈ Finset.range s.shiftCount,
        ∑ l ∈ (Finset.range s.shiftCount).erase k,
          ‖∑ x ∈ Finset.range P,
            translatedPairCorrelation
              (iteratedPairCorrelation z hs) s.stepSize k l x‖) ≤
        ∑ k ∈ Finset.range s.shiftCount,
          ∑ _l ∈ (Finset.range s.shiftCount).erase k, E := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      simpa only [iteratedPairCorrelation, translatedPairCorrelation] using
        hchild k hk l hl
    _ = (s.shiftCount : ℝ) * (s.shiftCount - 1 : ℕ) * E := by
      simp_rw [Finset.sum_const, nsmul_eq_mul]
      calc
        (∑ k ∈ Finset.range s.shiftCount,
            (((Finset.range s.shiftCount).erase k).card : ℝ) * E) =
            ∑ _k ∈ Finset.range s.shiftCount,
              ((s.shiftCount - 1 : ℕ) : ℝ) * E := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.card_erase_of_mem hk, Finset.card_range]
        _ = _ := by simp; ring

/-- Honest finite iteration of the exact one-step inequality. -/
theorem norm_iteratedPrefix_le_finiteHistoryEnvelope
    (z : ℕ → ℂ) (hz : ∀ x, ‖z x‖ ≤ 1)
    (P : ℕ) (steps : List ConductorStep) (hs : History)
    {terminal : ℝ} (hterminal_nonneg : 0 ≤ terminal)
    (hterminal : ∀ leaf ∈ offDiagonalHistoryLeaves steps hs,
      ‖∑ x ∈ Finset.range P,
        iteratedPairCorrelation z leaf x‖ ≤ terminal) :
    ‖∑ x ∈ Finset.range P,
      iteratedPairCorrelation z hs x‖ ≤
      finiteHistoryEnvelope P terminal steps := by
  induction steps generalizing hs with
  | nil =>
      simpa only [iteratedPairCorrelation, finiteHistoryEnvelope] using
        hterminal hs (by simp [offDiagonalHistoryLeaves])
  | cons s ss ih =>
      let E : ℝ := finiteHistoryEnvelope P terminal ss
      have hE : 0 ≤ E := finiteHistoryEnvelope_nonneg P hterminal_nonneg ss
      have hchildren : ∀ k ∈ Finset.range s.shiftCount,
          ∀ l ∈ (Finset.range s.shiftCount).erase k,
            ‖∑ x ∈ Finset.range P,
              iteratedPairCorrelation z
                ((s.stepSize, k, l) :: hs) x‖ ≤ E := by
        intro k hk l hl
        apply ih ((s.stepSize, k, l) :: hs)
        intro leaf hleaf
        apply hterminal leaf
        simp only [offDiagonalHistoryLeaves, Finset.mem_biUnion]
        refine ⟨(s.stepSize, k, l) :: hs, ?_, hleaf⟩
        obtain ⟨hlne, hlrange⟩ := Finset.mem_erase.mp hl
        exact cons_mem_offDiagonalChildren s hs
          (Finset.mem_range.mp hk) (Finset.mem_range.mp hlrange) hlne.symm
      have hoff :
          offDiagonalCorrelationSum (iteratedPairCorrelation z hs)
              P s.shiftCount s.stepSize ≤
            (s.shiftCount : ℝ) * (s.shiftCount - 1 : ℕ) * E :=
        offDiagonalCorrelationSum_le_children z P s hs hchildren
      have hstep :=
        card_sq_mul_norm_iterated_sum_sq_le_offDiagonal
          z hz hs P s.shiftCount s.stepSize
      have hrec :
          (s.shiftCount : ℝ) ^ 2 *
              ‖∑ x ∈ Finset.range P,
                iteratedPairCorrelation z hs x‖ ^ 2 ≤
            stepRadicand P s E := by
        calc
          _ ≤ 2 * ((P : ℝ) *
                ((s.shiftCount : ℝ) * P +
                  offDiagonalCorrelationSum
                    (iteratedPairCorrelation z hs)
                    P s.shiftCount s.stepSize) +
              boundaryBudget s.shiftCount s.stepSize ^ 2) := hstep
          _ ≤ stepRadicand P s E := by
            unfold stepRadicand
            gcongr
      have hK : 0 < (s.shiftCount : ℝ) := by
        exact_mod_cast s.shiftCount_pos
      have hrad : 0 ≤ stepRadicand P s E :=
        stepRadicand_nonneg P s hE
      have hsqrt :
          Real.sqrt (stepRadicand P s E) ^ 2 = stepRadicand P s E :=
        Real.sq_sqrt hrad
      rw [finiteHistoryEnvelope]
      apply (le_div_iff₀ hK).2
      have hnorm : 0 ≤ ‖∑ x ∈ Finset.range P,
          iteratedPairCorrelation z hs x‖ := norm_nonneg _
      have hsqrtnonneg : 0 ≤ Real.sqrt (stepRadicand P s E) :=
        Real.sqrt_nonneg _
      nlinarith

/-- Root-history form: the raw prefix of the original unit-ball sequence is
bounded by the finite recursive envelope. -/
theorem norm_rawPrefix_le_finiteHistoryEnvelope
    (z : ℕ → ℂ) (hz : ∀ x, ‖z x‖ ≤ 1)
    (P : ℕ) (steps : List ConductorStep)
    {terminal : ℝ} (hterminal_nonneg : 0 ≤ terminal)
    (hterminal : ∀ leaf ∈ offDiagonalHistoryLeaves steps [],
      ‖∑ x ∈ Finset.range P,
        iteratedPairCorrelation z leaf x‖ ≤ terminal) :
    ‖∑ x ∈ Finset.range P, z x‖ ≤
      finiteHistoryEnvelope P terminal steps := by
  simpa only [iteratedPairCorrelation] using
    norm_iteratedPrefix_le_finiteHistoryEnvelope z hz P steps []
      hterminal_nonneg hterminal

end RestrictedWeyl

end Erdos1149
