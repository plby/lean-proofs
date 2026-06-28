/-
Copyright (c) 2025 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import Mathlib

/-!
# Density Utilities

Original license: Apache 2.0. This file has been modified.

Definitions and elementary facts for upper, lower, and natural density relative to
locally finite ordered intervals.
-/

open Filter

open scoped Topology

namespace Set

/--
Given a set `S` and an element `b` in an order `β`, where all intervals bounded above are finite,
we define the partial density of `S` (relative to a set `A`) to be the proportion of elements in
`{x ∈ A | x < b}` that lie in `S ∩ A`.

This definition was inspired from https://github.com/b-mehta/unit-fractions
-/
@[inline]
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

theorem partialDensity_le_one {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : S.partialDensity A b ≤ 1 := by
  apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
  exact mod_cast Set.ncard_le_ncard <| Set.inter_subset_inter_left _ inter_subset_right

/--
Given a set `S` in an order `β`, where all intervals bounded above are finite, we define the upper
density of `S` (relative to a set `A`) to be the limsup of the partial densities of `S`
(relative to `A`) for `b → ∞`.
-/
noncomputable def upperDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.limsup fun (b : β) ↦ S.partialDensity A b

/--
Given a set `S` in an order `β`, where all intervals bounded above are finite, we define the lower
density of `S` (relative to a set `A`) to be the liminf of the partial densities of `S`
(relative to `A`) for `b → ∞`.
-/
noncomputable def lowerDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.liminf fun (b : β) ↦ S.partialDensity A b

theorem lowerDensity_le_one {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : S.lowerDensity A ≤ 1 := by
  by_cases h : atTop (α := β) = ⊥
  · simp [h, Set.lowerDensity, Filter.liminf_eq]
  · have : (atTop (α := β)).NeBot := ⟨h⟩
    apply Real.sSup_le (fun x hx ↦ ?_) one_pos.le
    simpa using hx.mono fun y hy ↦ hy.trans (Set.partialDensity_le_one _ _ y)

theorem lowerDensity_nonneg {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : 0 ≤ S.lowerDensity A := by
  rw [Set.lowerDensity, Filter.liminf_eq]
  exact (em _).elim (le_csSup · <| .of_forall fun _ ↦ by positivity)
    (Real.sSup_of_not_bddAbove · |>.ge)

/--
A set `S` in an order `β` where all intervals bounded above are finite is said to have
density `α : ℝ` (relative to a set `A`) if the proportion of `x ∈ S` such that `x < n`
in `A` tends to `α` as `n → ∞`.

When `β = ℕ` this by default defines the natural density of a set
(i.e., relative to all of `ℕ`).
-/
def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

/--
A set `S` in an order `β` where all intervals bounded above are finite is said to have
positive density (relative to a set `A`) if there exists a positive `α : ℝ` such that
`S` has density `α` (relative to a set `A`).
-/
def HasPosDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : Prop :=
  ∃ α > 0, S.HasDensity α A

namespace HasDensity

/-- In a non-trivial partial order with a least element, the set of all
elements has density one. -/
@[simp]
theorem univ {β : Type*} [PartialOrder β] [LocallyFiniteOrder β] [OrderBot β] [Nontrivial β] :
    (@Set.univ β).HasDensity 1 := by
  by_cases h : atTop (α := β) = ⊥
  · simp [h, HasDensity]
  · simp only [HasDensity, partialDensity, univ_inter, inter_univ]
    obtain ⟨b, hb⟩ : ∃ b : β, ⊥ < b := by
      obtain ⟨x, hx⟩ := exists_ne (⊥ : β)
      exact ⟨x, bot_lt_iff_ne_bot.mpr hx⟩
    refine tendsto_const_nhds.congr' ?_
    exact (eventually_ge_atTop b).mono fun n hn ↦ by
      have hbot : (⊥ : β) ∈ Iio n := hb.trans_le hn
      have hncard : (Iio n).ncard ≠ 0 := by
        exact Set.ncard_ne_zero_of_mem hbot
      exact (div_self <| mod_cast hncard).symm

end HasDensity

end Set
