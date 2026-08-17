/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos185.Definitions

/-!
# Combinatorial lines in the ternary cube are geometric lines

This file supplies the elementary bridge from Mathlib's Hales--Jewett
`Combinatorics.Line` to the literal Euclidean collinearity used in the
definition of a Moser set.  The wildcard coordinate required by a proper
combinatorial line also shows that its three ternary words are distinct.
-/

namespace Combinatorics.Line

/-- A proper combinatorial line over a nontrivial alphabet is injective. -/
theorem injective {α ι : Type*} [Nontrivial α]
    (l : Combinatorics.Line α ι) : Function.Injective l := by
  intro x y hxy
  obtain ⟨i, hi⟩ := l.proper
  have hcoord := congrFun hxy i
  simpa only [apply_none l x i hi, apply_none l y i hi] using hcoord

end Combinatorics.Line

namespace Erdos185

open Finset

noncomputable section

/-- The words at parameters `0` and `1` of a ternary combinatorial line are distinct. -/
theorem combinatorialLine_zero_ne_one {n : ℕ}
    (l : Combinatorics.Line (Fin 3) (Fin n)) : l 0 ≠ l 1 :=
  l.injective.ne (by decide)

/-- The words at parameters `0` and `2` of a ternary combinatorial line are distinct. -/
theorem combinatorialLine_zero_ne_two {n : ℕ}
    (l : Combinatorics.Line (Fin 3) (Fin n)) : l 0 ≠ l 2 :=
  l.injective.ne (by decide)

/-- The words at parameters `1` and `2` of a ternary combinatorial line are distinct. -/
theorem combinatorialLine_one_ne_two {n : ℕ}
    (l : Combinatorics.Line (Fin 3) (Fin n)) : l 1 ≠ l 2 :=
  l.injective.ne (by decide)

/-- After the coordinatewise embedding into real space, the entire range of
a ternary combinatorial line is collinear. -/
theorem combinatorialLine_realRange_collinear {n : ℕ}
    (l : Combinatorics.Line (Fin 3) (Fin n)) :
    Collinear ℝ (Set.range fun t : Fin 3 ↦ toRealPoint (l t)) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨toRealPoint (l 0),
    toRealPoint (l 1) - toRealPoint (l 0), ?_⟩
  rintro _ ⟨t, rfl⟩
  refine ⟨((t : ℕ) : ℝ), ?_⟩
  ext i
  cases h : l.idxFun i <;>
    simp [toRealPoint, Combinatorics.Line.coe_apply, h]

/-- In particular, the three real points obtained at parameters `0`, `1`,
and `2` form a geometrically collinear triple. -/
theorem combinatorialLine_realPoints_collinear {n : ℕ}
    (l : Combinatorics.Line (Fin 3) (Fin n)) :
    Collinear ℝ
      ({toRealPoint (l 0), toRealPoint (l 1), toRealPoint (l 2)} :
        Set (Fin n → ℝ)) := by
  apply Collinear.subset _ (combinatorialLine_realRange_collinear l)
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

/-- A finite set contains a combinatorial line if it contains the full range
of some proper Mathlib combinatorial line. -/
def ContainsCombinatorialLine {n : ℕ} (A : Finset (Word n)) : Prop :=
  ∃ l : Combinatorics.Line (Fin 3) (Fin n),
    Set.range l ⊆ (A : Set (Word n))

/-- A geometric Moser set cannot contain a Hales--Jewett combinatorial line. -/
theorem IsMoserSet.not_containsCombinatorialLine {n : ℕ}
    {A : Finset (Word n)} (hA : IsMoserSet A) :
    ¬ ContainsCombinatorialLine A := by
  rintro ⟨l, hl⟩
  have h0 : l 0 ∈ A := hl ⟨0, rfl⟩
  have h1 : l 1 ∈ A := hl ⟨1, rfl⟩
  have h2 : l 2 ∈ A := hl ⟨2, rfl⟩
  exact hA (l 0) h0 (l 1) h1 (l 2) h2
    (combinatorialLine_zero_ne_one l)
    (combinatorialLine_zero_ne_two l)
    (combinatorialLine_one_ne_two l)
    (combinatorialLine_realPoints_collinear l)

end

end Erdos185
