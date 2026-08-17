/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib

/-!
# Erdős Problem 185: definitions and the finite extremal problem

This file gives the literal geometric formulation of the Moser problem in the
ternary cube.  In particular, `IsMoserSet` uses Euclidean collinearity after
embedding the entries `0`, `1`, and `2` in `ℝ`; it is not the weaker
condition of containing no Hales--Jewett combinatorial line.
-/

namespace Erdos185

open Finset

noncomputable section

/-- A word of length `n` in the alphabet `{0, 1, 2}`. -/
abbrev Word (n : ℕ) := Fin n → Fin 3

/-- The literal coordinatewise embedding of the ternary cube in `ℝ^n`. -/
def toRealPoint {n : ℕ} (x : Word n) : Fin n → ℝ :=
  fun i ↦ ((x i : ℕ) : ℝ)

/--
A subset of the ternary cube is a Moser set if it contains no three distinct
points which are collinear in the ordinary real affine space.
-/
def IsMoserSet {n : ℕ} (A : Finset (Word n)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
    x ≠ y → x ≠ z → y ≠ z →
      ¬ Collinear ℝ
        ({toRealPoint x, toRealPoint y, toRealPoint z} : Set (Fin n → ℝ))

/-- The empty subset of a ternary cube is a Moser set. -/
@[simp] theorem isMoserSet_empty (n : ℕ) :
    IsMoserSet (∅ : Finset (Word n)) := by
  simp [IsMoserSet]

/-- The Moser property is inherited by subsets. -/
theorem IsMoserSet.mono {n : ℕ} {A B : Finset (Word n)}
    (hA : IsMoserSet A) (hBA : B ⊆ A) : IsMoserSet B := by
  intro x hx y hy z hz hxy hxz hyz
  exact hA x (hBA hx) y (hBA hy) z (hBA hz) hxy hxz hyz

/-- The ternary cube has exactly `3 ^ n` words. -/
@[simp] theorem cube_card (n : ℕ) :
    (Finset.univ : Finset (Word n)).card = 3 ^ n := by
  simp [Word]

/-- All admissible subsets of the `n`-dimensional ternary cube. -/
noncomputable def candidates (n : ℕ) : Finset (Finset (Word n)) := by
  classical
  exact (Finset.univ : Finset (Word n)).powerset.filter IsMoserSet

/-- Membership in `candidates` is exactly the geometric Moser property. -/
@[simp] theorem mem_candidates_iff {n : ℕ} {A : Finset (Word n)} :
    A ∈ candidates n ↔ IsMoserSet A := by
  simp [candidates]

/-- Every candidate is, tautologically, a subset of the finite cube. -/
theorem candidate_subset_cube {n : ℕ} {A : Finset (Word n)}
    (_hA : A ∈ candidates n) : A ⊆ (Finset.univ : Finset (Word n)) := by
  exact fun _ _ ↦ Finset.mem_univ _

/-- The candidate family is nonempty. -/
theorem candidates_nonempty (n : ℕ) : (candidates n).Nonempty := by
  exact ⟨∅, mem_candidates_iff.mpr (isMoserSet_empty n)⟩

/--
`f3 n` is the maximum cardinality of a subset of `{0,1,2}^n` containing no
three distinct geometrically collinear points.
-/
noncomputable def f3 (n : ℕ) : ℕ :=
  (candidates n).sup Finset.card

/-- Every geometrically line-free set has cardinality at most `f3 n`. -/
theorem card_le_f3 {n : ℕ} {A : Finset (Word n)}
    (hA : IsMoserSet A) : A.card ≤ f3 n := by
  exact Finset.le_sup (f := Finset.card) (mem_candidates_iff.mpr hA)

/-- There is a geometrically line-free set whose cardinality is `f3 n`. -/
theorem exists_isMoserSet_card_eq_f3 (n : ℕ) :
    ∃ A : Finset (Word n), IsMoserSet A ∧ A.card = f3 n := by
  obtain ⟨A, hA, hmax⟩ :=
    (candidates n).exists_max_image Finset.card (candidates_nonempty n)
  refine ⟨A, mem_candidates_iff.mp hA, le_antisymm ?_ ?_⟩
  · exact card_le_f3 (mem_candidates_iff.mp hA)
  · exact Finset.sup_le fun B hB ↦ hmax B hB

/-- The extremal number cannot exceed the cardinality of the whole cube. -/
theorem f3_le_cube_card (n : ℕ) : f3 n ≤ 3 ^ n := by
  rw [← cube_card n]
  exact Finset.sup_le fun A hA ↦
    Finset.card_le_card (candidate_subset_cube hA)

/-- An exact specification of which natural numbers lie below `f3 n`. -/
theorem le_f3_iff {n m : ℕ} :
    m ≤ f3 n ↔ ∃ A : Finset (Word n), IsMoserSet A ∧ m ≤ A.card := by
  constructor
  · intro hm
    obtain ⟨A, hA, hcard⟩ := exists_isMoserSet_card_eq_f3 n
    exact ⟨A, hA, hm.trans_eq hcard.symm⟩
  · rintro ⟨A, hA, hm⟩
    exact hm.trans (card_le_f3 hA)

end

end Erdos185
