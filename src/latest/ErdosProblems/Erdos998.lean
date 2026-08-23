/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 998.
https://www.erdosproblems.com/forum/thread/998

Informal authors:
- Harry Kesten

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos998.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 998

The endpoint formulation copied in the problem statement is false.  Kesten's actual theorem
characterizes bounded-remainder intervals by their *length*, not by requiring each endpoint to
belong to the orbit of the irrational rotation.

This file gives an explicit counterexample.  For

`α = √2 / 10`, `u = 1 / 4`, and `v = u + α`,

the discrepancy is bounded by `1` for every `n`, by a telescoping fractional-part identity, while
`u` is not the fractional part of any integer multiple of `α`.
-/

open scoped BigOperators
open Finset Real

namespace Erdos998

/-- The number of integers `m` with `1 ≤ m ≤ n` for which `{mα} ∈ [u,v)`.  The index `j` in
`range n` represents `m = j + 1`. -/
noncomputable def countInIco (α u v : ℝ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun j ↦
    u ≤ Int.fract (α * (j + 1 : ℕ)) ∧ Int.fract (α * (j + 1 : ℕ)) < v).card

/-- The literal eventual-`O(1)` condition in the displayed problem. -/
def HasBoundedRemainder (α u v : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    |(countInIco α u v n : ℝ) - (n : ℝ) * (v - u)| ≤ C

/-- The endpoint implication asked for in the copied formulation of Erdős Problem 998. -/
def Erdos998Statement : Prop :=
  ∀ α u v : ℝ, Irrational α → 0 ≤ u → u < v → v ≤ 1 →
    HasBoundedRemainder α u v →
      (∃ k : ℤ, u = Int.fract (α * (k : ℝ))) ∧
      (∃ l : ℤ, v = Int.fract (α * (l : ℝ)))

/-! ## The transfer and telescoping identities -/

/-- Subtracting before or after taking a fractional part gives the same fractional part. -/
lemma fract_sub_eq_fract_fract_sub (x u : ℝ) :
    Int.fract (x - u) = Int.fract (Int.fract x - u) := by
  rw [Int.fract_eq_fract]
  refine ⟨⌊x⌋, ?_⟩
  rw [Int.fract]
  ring

/-- A translated interval of length `α` is detected by the fractional part after translation. -/
lemma mem_translated_Ico_iff {α u x : ℝ} (hα : 0 < α) (hu : 0 ≤ u)
    (huα : u + α < 1) :
    (u ≤ Int.fract x ∧ Int.fract x < u + α) ↔ Int.fract (x - u) < α := by
  have hx0 : 0 ≤ Int.fract x := Int.fract_nonneg x
  have hx1 : Int.fract x < 1 := Int.fract_lt_one x
  rw [fract_sub_eq_fract_fract_sub]
  by_cases hux : u ≤ Int.fract x
  · have hsub0 : 0 ≤ Int.fract x - u := sub_nonneg.mpr hux
    have hsub1 : Int.fract x - u < 1 := by linarith
    rw [Int.fract_eq_self.mpr ⟨hsub0, hsub1⟩]
    constructor <;> intro h
    · linarith
    · exact ⟨hux, by linarith⟩
  · have hxu : Int.fract x < u := lt_of_not_ge hux
    have hneg : Int.fract (Int.fract x - u) = Int.fract x - u + 1 := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, -1, ?_⟩
      norm_num
    rw [hneg]
    constructor
    · rintro ⟨h, _⟩
      exact (hux h).elim
    · intro h
      exfalso
      linarith

/-- The indicator of a translated interval of length `α`, minus its length, is a one-step
coboundary. -/
lemma indicator_sub_length {α u x : ℝ} (hα : 0 < α) (hu : 0 ≤ u)
    (huα : u + α < 1) :
    (if u ≤ Int.fract x ∧ Int.fract x < u + α then (1 : ℝ) else 0) - α =
      Int.fract (x - u - α) - Int.fract (x - u) := by
  have hα1 : α < 1 := by linarith
  have htranslate :
      Int.fract (x - u - α) = Int.fract (Int.fract (x - u) - α) := by
    rw [Int.fract_eq_fract]
    refine ⟨⌊x - u⌋, ?_⟩
    rw [Int.fract]
    ring
  rw [htranslate]
  simp only [mem_translated_Ico_iff hα hu huα]
  by_cases ht : Int.fract (x - u) < α
  · have ht0 : 0 ≤ Int.fract (x - u) := Int.fract_nonneg _
    have htneg : Int.fract (x - u) - α < 0 := sub_neg.mpr ht
    have htgt : -1 < Int.fract (x - u) - α := by linarith
    have hfract : Int.fract (Int.fract (x - u) - α) =
        Int.fract (x - u) - α + 1 := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, -1, ?_⟩
      norm_num
    rw [if_pos ht, hfract]
    ring
  · have htge : α ≤ Int.fract (x - u) := le_of_not_gt ht
    have htlt : Int.fract (x - u) - α < 1 := by
      linarith [Int.fract_lt_one (x - u)]
    have hfract : Int.fract (Int.fract (x - u) - α) =
        Int.fract (x - u) - α :=
      Int.fract_eq_self.mpr ⟨sub_nonneg.mpr htge, htlt⟩
    rw [if_neg ht, hfract]
    ring

/-- Cast the filtered cardinality to a sum of real-valued indicators. -/
lemma countInIco_cast_eq_sum (α u v : ℝ) (n : ℕ) :
    (countInIco α u v n : ℝ) =
      ∑ j ∈ Finset.range n,
        if u ≤ Int.fract (α * (j + 1 : ℕ)) ∧
            Int.fract (α * (j + 1 : ℕ)) < v then (1 : ℝ) else 0 := by
  classical
  rw [countInIco, Finset.card_filter]
  push_cast
  rfl

/-- The elementary telescoping sum used by the counterexample. -/
lemma sum_fract_diff (α u : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n,
      (Int.fract (α * (j : ℕ) - u) - Int.fract (α * (j + 1 : ℕ) - u))) =
      Int.fract (-u) - Int.fract (α * (n : ℕ) - u) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Exact discrepancy formula for an arbitrary translate of an interval of length `α`. -/
theorem discrepancy_eq_fract_sub {α u : ℝ} (hα : 0 < α) (hu : 0 ≤ u)
    (huα : u + α < 1) (n : ℕ) :
    (countInIco α u (u + α) n : ℝ) - (n : ℝ) * α =
      Int.fract (-u) - Int.fract (α * (n : ℕ) - u) := by
  rw [countInIco_cast_eq_sum]
  calc
    (∑ j ∈ Finset.range n,
        if u ≤ Int.fract (α * (j + 1 : ℕ)) ∧
            Int.fract (α * (j + 1 : ℕ)) < u + α then (1 : ℝ) else 0) -
          (n : ℝ) * α =
        ∑ j ∈ Finset.range n,
          ((if u ≤ Int.fract (α * (j + 1 : ℕ)) ∧
              Int.fract (α * (j + 1 : ℕ)) < u + α then (1 : ℝ) else 0) - α) := by
            simp [Finset.sum_sub_distrib]
    _ = ∑ j ∈ Finset.range n,
          (Int.fract (α * (j : ℕ) - u) -
            Int.fract (α * (j + 1 : ℕ) - u)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [indicator_sub_length hα hu huα]
          congr 2
          push_cast
          ring
    _ = Int.fract (-u) - Int.fract (α * (n : ℕ) - u) :=
      sum_fract_diff α u n

/-- The discrepancy in the preceding theorem has absolute value at most one. -/
theorem abs_discrepancy_le_one {α u : ℝ} (hα : 0 < α) (hu : 0 ≤ u)
    (huα : u + α < 1) (n : ℕ) :
    |(countInIco α u (u + α) n : ℝ) - (n : ℝ) * α| ≤ 1 := by
  rw [discrepancy_eq_fract_sub hα hu huα]
  rw [abs_le]
  constructor <;>
    linarith [Int.fract_nonneg (-u), Int.fract_lt_one (-u),
      Int.fract_nonneg (α * (n : ℕ) - u), Int.fract_lt_one (α * (n : ℕ) - u)]

/-! ## The explicit counterexample -/

noncomputable def counterexampleAlpha : ℝ := Real.sqrt 2 / 10
noncomputable def counterexampleU : ℝ := 1 / 4
noncomputable def counterexampleV : ℝ := counterexampleU + counterexampleAlpha

lemma counterexampleAlpha_irrational : Irrational counterexampleAlpha := by
  exact irrational_sqrt_two.div_natCast (by norm_num)

lemma counterexampleAlpha_pos : 0 < counterexampleAlpha := by
  dsimp [counterexampleAlpha]
  positivity

lemma sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

lemma counterexampleAlpha_lt_quarter : counterexampleAlpha < 1 / 4 := by
  rw [counterexampleAlpha]
  calc
    Real.sqrt 2 / 10 < 2 / 10 := by
      exact (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 10)).2 sqrt_two_lt_two
    _ < 1 / 4 := by norm_num

lemma counterexample_bounds :
    0 ≤ counterexampleU ∧ counterexampleU < counterexampleV ∧ counterexampleV ≤ 1 := by
  dsimp [counterexampleU, counterexampleV]
  constructor
  · norm_num
  constructor
  · linarith [counterexampleAlpha_pos]
  · linarith [counterexampleAlpha_lt_quarter]

lemma counterexample_bounded_remainder :
    HasBoundedRemainder counterexampleAlpha counterexampleU counterexampleV := by
  refine ⟨1, by norm_num, 0, ?_⟩
  intro n hn
  have hbound := abs_discrepancy_le_one counterexampleAlpha_pos
    (show 0 ≤ counterexampleU by norm_num [counterexampleU])
    (show counterexampleU + counterexampleAlpha < 1 by
      rw [counterexampleU]
      linarith [counterexampleAlpha_lt_quarter]) n
  simpa [counterexampleV] using hbound

/-- The left endpoint `1/4` is not in the orbit of `√2/10`. -/
lemma counterexampleU_not_orbit (k : ℤ) :
    counterexampleU ≠ Int.fract (counterexampleAlpha * (k : ℝ)) := by
  intro hk
  have hfract : Int.fract (counterexampleAlpha * (k : ℝ)) = counterexampleU := hk.symm
  rcases Int.fract_eq_iff.mp hfract with ⟨_, _, z, hz⟩
  by_cases hk0 : k = 0
  · subst k
    norm_num [counterexampleU] at hfract
  · have hirr : Irrational (counterexampleAlpha * (k : ℝ)) :=
      counterexampleAlpha_irrational.mul_intCast hk0
    have heq : counterexampleAlpha * (k : ℝ) = (z : ℝ) + counterexampleU := by
      linarith
    apply hirr.ne_rat ((z : ℚ) + 1 / 4)
    simpa [counterexampleU] using heq

/-- The exact endpoint implication in the supplied Problem 998 statement is false. -/
theorem erdos_problem_998 : ¬ Erdos998Statement := by
  intro h
  obtain ⟨⟨k, hk⟩, _⟩ := h counterexampleAlpha counterexampleU counterexampleV
    counterexampleAlpha_irrational counterexample_bounds.1 counterexample_bounds.2.1
    counterexample_bounds.2.2 counterexample_bounded_remainder
  exact counterexampleU_not_orbit k hk

#print axioms erdos_problem_998

end Erdos998
