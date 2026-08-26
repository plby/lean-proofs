/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Erdős Problem 1189: the nontrivial divisors of 12 are an irreducible covering set.

Informal source: the example recorded at https://www.erdosproblems.com/1189.
Formal author: OpenAI Codex.
The finite obstructions below quantify over every new residue assignment.
-/

import ErdosProblems.Erdos1189.Density

namespace Erdos1189

open Finset

private lemma not_cover_four_of_obstruction {u v w t N : ℕ}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (ht : 0 < t)
    (h : ∀ b : Fin u, ∀ c : Fin v, ∀ d : Fin w, ∀ e : Fin t,
      ∃ x : Fin N, x.val % u ≠ b.val ∧ x.val % v ≠ c.val ∧
        x.val % w ≠ d.val ∧ x.val % t ≠ e.val) :
    ¬ IsCoveringSet {u, v, w, t} := by
  rintro ⟨_, a, ha⟩
  obtain ⟨x, hxu, hxv, hxw, hxt⟩ := h
    ⟨canonicalResidue a u, canonicalResidue_lt a hu⟩
    ⟨canonicalResidue a v, canonicalResidue_lt a hv⟩
    ⟨canonicalResidue a w, canonicalResidue_lt a hw⟩
    ⟨canonicalResidue a t, canonicalResidue_lt a ht⟩
  obtain ⟨m, hm, hxm⟩ := ha (x : ℕ)
  simp only [mem_insert, mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · apply hxu
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (canonicalResidue_lt a hu)] using
      (nat_modEq_canonicalResidue_iff a hu x).mpr hxm
  · apply hxv
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (canonicalResidue_lt a hv)] using
      (nat_modEq_canonicalResidue_iff a hv x).mpr hxm
  · apply hxw
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (canonicalResidue_lt a hw)] using
      (nat_modEq_canonicalResidue_iff a hw x).mpr hxm
  · apply hxt
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (canonicalResidue_lt a ht)] using
      (nat_modEq_canonicalResidue_iff a ht x).mpr hxm

private lemma not_cover_without_two : ¬ IsCoveringSet {3, 4, 6, 12} := by
  apply not_isCoveringSet_of_reciprocalSum_lt_one
  norm_num [reciprocalSum]

private lemma not_cover_without_three : ¬ IsCoveringSet {2, 4, 6, 12} := by
  apply not_cover_four_of_obstruction (N := 12) (by decide) (by decide)
    (by decide) (by decide)
  decide

private lemma not_cover_without_four : ¬ IsCoveringSet {2, 3, 6, 12} := by
  apply not_cover_four_of_obstruction (N := 12) (by decide) (by decide)
    (by decide) (by decide)
  decide

private lemma not_cover_without_six : ¬ IsCoveringSet {2, 3, 4, 12} := by
  apply not_cover_four_of_obstruction (N := 12) (by decide) (by decide)
    (by decide) (by decide)
  decide

private lemma not_cover_without_twelve : ¬ IsCoveringSet {2, 3, 4, 6} := by
  apply not_cover_four_of_obstruction (N := 12) (by decide) (by decide)
    (by decide) (by decide)
  decide

/-- The classical five-class covering assignment. -/
def twelveAssignment : ℕ → ℤ
  | 2 => 0
  | 3 => 0
  | 4 => 1
  | 6 => 5
  | 12 => 7
  | _ => 0

lemma covers_twelve : Covers {2, 3, 4, 6, 12} twelveAssignment := by
  apply (covers_iff_finite_period (N := 12) (by decide) (by
    intro d hd
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> decide)).mpr
  intro x
  fin_cases x <;> norm_num [twelveAssignment, Int.ModEq]

lemma nontrivialDivisors_twelve : nontrivialDivisors 12 = {2, 3, 4, 6, 12} := by
  decide

/-- A genuine irreducible modulus set: deleting a modulus cannot be repaired
by changing the remaining residue classes. -/
theorem irreducible_twelve : IsIrreducibleCoveringSet (nontrivialDivisors 12) := by
  rw [nontrivialDivisors_twelve, isIrreducibleCoveringSet_iff_erase]
  refine ⟨⟨?_, twelveAssignment, covers_twelve⟩, ?_⟩
  · intro d hd
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro d hd
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · simpa using not_cover_without_two
    · rw [show ({2, 3, 4, 6, 12} : Finset ℕ).erase 3 = {2, 4, 6, 12} by decide]
      exact not_cover_without_three
    · rw [show ({2, 3, 4, 6, 12} : Finset ℕ).erase 4 = {2, 3, 6, 12} by decide]
      exact not_cover_without_four
    · rw [show ({2, 3, 4, 6, 12} : Finset ℕ).erase 6 = {2, 3, 4, 12} by decide]
      exact not_cover_without_six
    · rw [show ({2, 3, 4, 6, 12} : Finset ℕ).erase 12 = {2, 3, 4, 6} by decide]
      exact not_cover_without_twelve

end Erdos1189
