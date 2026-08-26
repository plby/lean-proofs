/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Bad-shift equations for Erdős Problem 477.
Formal author: Codex.

This file proves the elementary witness bound. Counting/BadShiftCount.lean
uses it to prove the sublinear bad-shift estimate for the construction.
-/

import ErdosProblems.Erdos477.PowerValues
import ErdosProblems.Erdos477.Tiling

namespace Erdos477

/-- The shifted sixth power is a difference of two nonnegative sixth powers. -/
def IsBadShift (c : ℤ) (t : ℕ) : Prop :=
  ∃ u v : ℕ, (t : ℤ) ^ 6 - c = (u : ℤ) ^ 6 - (v : ℤ) ^ 6

lemma mem_difference_iff_isBadShift (c : ℤ) (t : ℕ) :
    c - (t : ℤ) ^ 6 ∈ DifferenceSet (PowerValues 6) ↔ IsBadShift c t := by
  constructor
  · rintro ⟨x, ⟨u, rfl⟩, y, ⟨v, rfl⟩, heq⟩
    exact ⟨v, u, by dsimp at heq; omega⟩
  · rintro ⟨u, v, heq⟩
    exact ⟨(v : ℤ) ^ 6, ⟨v, rfl⟩, (u : ℤ) ^ 6, ⟨u, rfl⟩, by omega⟩

/-- The fifth power of either witness is bounded in terms of the shift.
This controls the range in which a counting argument must work. -/
lemma badShift_witness_bound {c : ℤ} {t : ℕ} (hc : c ∉ PowerValues 6)
    (hbad : IsBadShift c t) :
    ∃ u v : ℕ, (t : ℤ) ^ 6 - c = (u : ℤ) ^ 6 - (v : ℤ) ^ 6 ∧
      ((max u v : ℕ) : ℤ) ^ 5 ≤ (t : ℤ) ^ 6 + |c| := by
  obtain ⟨u, v, heq⟩ := hbad
  have hne : u ≠ v := by
    intro huv
    subst v
    apply hc
    exact ⟨t, by dsimp; omega⟩
  have hsep := sixth_power_separation u v hne
  rw [← heq] at hsep
  refine ⟨u, v, heq, hsep.trans ?_⟩
  calc
    |(t : ℤ) ^ 6 - c| ≤ |(t : ℤ) ^ 6| + |c| := abs_sub _ _
    _ = (t : ℤ) ^ 6 + |c| := by rw [abs_of_nonneg (by positivity)]

#print axioms badShift_witness_bound
-- 'Erdos477.badShift_witness_bound' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos477
