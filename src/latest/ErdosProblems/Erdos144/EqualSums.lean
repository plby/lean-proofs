/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

/-!
# Deterministic equal-subset-sum lemmas for Erdős Problem 144

This file isolates the finite combinatorial argument used by the random-set
part of the proof.  If a finite set has more subsets than the number of
possible values of their sums, two subsets have the same sum.  Cancelling
their intersection produces disjoint, nonempty subsets with the same sum.
-/

open scoped BigOperators

namespace Erdos144.EqualSums

section Cancellation

variable {α : Type*} [DecidableEq α]

/-- Cancelling the common intersection of two equal subset sums preserves
the equality. -/
theorem sum_sdiff_eq_sum_sdiff_of_sum_eq (f : α → ℕ) {U V : Finset α}
    (hsum : ∑ x ∈ U, f x = ∑ x ∈ V, f x) :
    ∑ x ∈ U \ V, f x = ∑ x ∈ V \ U, f x := by
  have hU := Finset.sum_sdiff (f := f) (Finset.inter_subset_left : U ∩ V ⊆ U)
  have hV := Finset.sum_sdiff (f := f) (Finset.inter_subset_right : U ∩ V ⊆ V)
  have hUdiff : U \ (U ∩ V) = U \ V := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    aesop
  have hVdiff : V \ (U ∩ V) = V \ U := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    aesop
  rw [hUdiff] at hU
  rw [hVdiff] at hV
  exact Nat.add_right_cancel (hU.trans (hsum.trans hV.symm))

/-- The two asymmetric differences of distinct finite sets cannot both be
empty. -/
theorem sdiff_nonempty_or_sdiff_nonempty {U V : Finset α} (hne : U ≠ V) :
    (U \ V).Nonempty ∨ (V \ U).Nonempty := by
  by_contra h
  push Not at h
  exact hne (Finset.Subset.antisymm
    (Finset.sdiff_eq_empty_iff_subset.mp h.1)
    (Finset.sdiff_eq_empty_iff_subset.mp h.2))

/-- If all weights are positive, equality of sums and inequality of the
original sets imply that both asymmetric differences are nonempty. -/
theorem sdiff_nonempty_of_ne_of_sum_eq_of_pos (f : α → ℕ) {U V : Finset α}
    (hposU : ∀ x ∈ U, 0 < f x) (hposV : ∀ x ∈ V, 0 < f x)
    (hne : U ≠ V)
    (hsum : ∑ x ∈ U, f x = ∑ x ∈ V, f x) :
    (U \ V).Nonempty ∧ (V \ U).Nonempty := by
  have hcancel := sum_sdiff_eq_sum_sdiff_of_sum_eq f hsum
  rcases sdiff_nonempty_or_sdiff_nonempty hne with hU | hV
  · refine ⟨hU, ?_⟩
    by_contra h
    have hzero : ∑ x ∈ V \ U, f x = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp h]
      simp
    have hpositive : 0 < ∑ x ∈ U \ V, f x :=
      Finset.sum_pos (fun x hx ↦ hposU x (Finset.mem_sdiff.mp hx).1) hU
    omega
  · refine ⟨?_, hV⟩
    by_contra h
    have hzero : ∑ x ∈ U \ V, f x = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp h]
      simp
    have hpositive : 0 < ∑ x ∈ V \ U, f x :=
      Finset.sum_pos (fun x hx ↦ hposV x (Finset.mem_sdiff.mp hx).1) hV
    omega

/-- Distinct equal-sum subsets yield disjoint, nonempty equal-sum subsets
after their intersection is removed. -/
theorem disjoint_nonempty_equal_sums_of_ne (f : α → ℕ)
    {U V : Finset α} (hposU : ∀ x ∈ U, 0 < f x)
    (hposV : ∀ x ∈ V, 0 < f x) (hne : U ≠ V)
    (hsum : ∑ x ∈ U, f x = ∑ x ∈ V, f x) :
    ∃ A B : Finset α,
      A ⊆ U ∧ B ⊆ V ∧ Disjoint A B ∧ A.Nonempty ∧ B.Nonempty ∧
        ∑ x ∈ A, f x = ∑ x ∈ B, f x := by
  have hne' := sdiff_nonempty_of_ne_of_sum_eq_of_pos f hposU hposV hne hsum
  exact ⟨U \ V, V \ U, Finset.sdiff_subset, Finset.sdiff_subset,
    Finset.disjoint_left.mpr (fun x hxU hxV ↦ by simp_all), hne'.1, hne'.2,
    sum_sdiff_eq_sum_sdiff_of_sum_eq f hsum⟩

end Cancellation

section Pigeonhole

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
/-- Every subset sum lies in the interval from zero to the sum over the
ambient finite set. -/
theorem subsetSum_mem_Icc (S U : Finset α) (f : α → ℕ) (hUS : U ⊆ S) :
    (∑ x ∈ U, f x) ∈ Finset.Icc 0 (∑ x ∈ S, f x) := by
  exact Finset.mem_Icc.mpr
    ⟨Nat.zero_le _, Finset.sum_le_sum_of_subset hUS⟩

omit [DecidableEq α] in
/-- Pigeonhole principle for an arbitrary finite family and an arbitrary
finite set of possible subset sums.  This is the form used when a
probabilistic argument first extracts a large structured family. -/
theorem exists_ne_members_with_equal_sum (family : Finset (Finset α))
    (values : Finset ℕ) (f : α → ℕ)
    (hmaps : ∀ U ∈ family, (∑ x ∈ U, f x) ∈ values)
    (hcard : values.card < family.card) :
    ∃ U ∈ family, ∃ V ∈ family,
      U ≠ V ∧ ∑ x ∈ U, f x = ∑ x ∈ V, f x := by
  exact Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
    (fun U hU ↦ hmaps U hU)

/-- Arbitrary-family version of the cancellation argument. -/
theorem exists_disjoint_nonempty_equal_sum_of_family
    (S : Finset α) (family : Finset (Finset α)) (values : Finset ℕ)
    (f : α → ℕ) (hfamily : ∀ U ∈ family, U ⊆ S)
    (hmaps : ∀ U ∈ family, (∑ x ∈ U, f x) ∈ values)
    (hpos : ∀ x ∈ S, 0 < f x)
    (hcard : values.card < family.card) :
    ∃ U V : Finset α,
      U ⊆ S ∧ V ⊆ S ∧ Disjoint U V ∧ U.Nonempty ∧ V.Nonempty ∧
        ∑ x ∈ U, f x = ∑ x ∈ V, f x := by
  obtain ⟨U', hU'family, V', hV'family, hne, hsum⟩ :=
    exists_ne_members_with_equal_sum family values f hmaps hcard
  have hU'S := hfamily U' hU'family
  have hV'S := hfamily V' hV'family
  obtain ⟨U, V, hUU', hVV', hdisj, hUne, hVne, hsums⟩ :=
    disjoint_nonempty_equal_sums_of_ne f
      (fun x hx ↦ hpos x (hU'S hx))
      (fun x hx ↦ hpos x (hV'S hx)) hne hsum
  exact ⟨U, V, hUU'.trans hU'S, hVV'.trans hV'S, hdisj,
    hUne, hVne, hsums⟩

omit [DecidableEq α] in
/-- Pigeonhole principle for subset sums, with the sharp elementary count
of possible sums. -/
theorem exists_ne_subsets_with_equal_sum (S : Finset α) (f : α → ℕ)
    (hcard : ∑ x ∈ S, f x + 1 < 2 ^ S.card) :
    ∃ U V : Finset α,
      U ⊆ S ∧ V ⊆ S ∧ U ≠ V ∧
        ∑ x ∈ U, f x = ∑ x ∈ V, f x := by
  let total := ∑ x ∈ S, f x
  let subsetSum : Finset α → ℕ := fun U ↦ ∑ x ∈ U, f x
  have hmaps : Set.MapsTo subsetSum (S.powerset : Set (Finset α))
      (Finset.Icc 0 total : Set ℕ) := by
    intro U hU
    exact subsetSum_mem_Icc S U f (Finset.mem_powerset.mp hU)
  have hlt : (Finset.Icc 0 total).card < S.powerset.card := by
    simpa [total] using hcard
  obtain ⟨U, hU, V, hV, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  exact ⟨U, V, Finset.mem_powerset.mp hU, Finset.mem_powerset.mp hV,
    hne, heq⟩

/-- A directly usable form: sufficiently many subsets of a positive-weight
finite set force two disjoint nonempty subsets with equal sum. -/
theorem exists_disjoint_nonempty_equal_sum (S : Finset α) (f : α → ℕ)
    (hpos : ∀ x ∈ S, 0 < f x)
    (hcard : ∑ x ∈ S, f x + 1 < 2 ^ S.card) :
    ∃ U V : Finset α,
      U ⊆ S ∧ V ⊆ S ∧ Disjoint U V ∧ U.Nonempty ∧ V.Nonempty ∧
        ∑ x ∈ U, f x = ∑ x ∈ V, f x := by
  obtain ⟨U', V', hU'S, hV'S, hne, hsum⟩ :=
    exists_ne_subsets_with_equal_sum S f hcard
  obtain ⟨U, V, hUU', hVV', hdisj, hUne, hVne, hsums⟩ :=
    disjoint_nonempty_equal_sums_of_ne f
      (fun x hx ↦ hpos x (hU'S hx))
      (fun x hx ↦ hpos x (hV'S hx)) hne hsum
  exact ⟨U, V, hUU'.trans hU'S, hVV'.trans hV'S, hdisj,
    hUne, hVne, hsums⟩

end Pigeonhole

end Erdos144.EqualSums
