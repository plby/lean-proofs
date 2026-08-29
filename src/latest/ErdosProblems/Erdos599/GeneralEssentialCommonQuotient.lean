/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.QuotientMaximal

/-!
# Essential common quotients without source disjointness

The statement of Aharoni--Berger Corollary 2.28 does not require the two
commitment sets to avoid the source.  The earlier common-quotient interface
in `QuotientAssociativity` imposed that extra hypothesis only because it used
the disjoint-set version of the quotient-source formula.

Here we use the general source formula from `QuotientMaximal`.  If
`C ⊆ D` and `essential D ⊆ C`, then `C` and `D` have the same roof,
essential frontier, and strict roof.  Every point of `D \ C` is already in
that common strict roof, so deleting it explicitly has no further effect on
either the quotient graph or its normalized source.  Applying this with
`C = essential (X₁ ∪ X₂)` gives the assumption-free form of Corollary
2.28 needed in the singular construction.
-/

namespace Erdos599

open Set

universe u

namespace DWeb

variable {V : Type u}

/-- Quotient sets with the same essential core define the same normalized
quotient.  Unlike `quotient_eq_of_essential_subset`, this version does not
assume that the larger set is disjoint from the old source. -/
theorem quotient_eq_of_essential_subset_general
    (G : DWeb V) {C D : Set V}
    (hCD : C ⊆ D) (hEss : G.essential D ⊆ C)
    (hNoEnter : G.NoEdgeEnters G.source) :
    G.quotient C = G.quotient D := by
  have hRoof : G.roof C = G.roof D := by
    apply Set.Subset.antisymm
    · exact G.roof_mono hCD
    · rw [← G.roof_essential D]
      exact G.roof_mono hEss
  have hEssential : G.essential C = G.essential D :=
    G.essential_eq_of_essential_subset_of_subset hEss hCD
  have hStrict : G.strictRoof C = G.strictRoof D := by
    rw [strictRoof, strictRoof, hRoof, hEssential]
  have hDCStrict : D \ C ⊆ G.strictRoof D := by
    intro x hx
    exact ⟨G.subset_roof D hx.1, fun hxEss ↦ hx.2 (hEss hxEss)⟩
  rw [DWeb.mk.injEq]
  refine ⟨?_, ?_, rfl⟩
  · ext a b
    change
      (G.graph.Adj a b ∧ a ∉ G.strictRoof C ∧
          b ∉ G.strictRoof C ∧ b ∉ C) ↔
        (G.graph.Adj a b ∧ a ∉ G.strictRoof D ∧
          b ∉ G.strictRoof D ∧ b ∉ D)
    rw [hStrict]
    constructor
    · rintro ⟨e, ha, hb, hbC⟩
      refine ⟨e, ha, hb, ?_⟩
      intro hbD
      exact hb (hDCStrict ⟨hbD, hbC⟩)
    · rintro ⟨e, ha, hb, hbD⟩
      exact ⟨e, ha, hb, fun hbC ↦ hbD (hCD hbC)⟩
  · rw [G.quotient_source_eq_union_sdiff_strictRoof_of_noEdgeEnters_general
        hNoEnter,
      G.quotient_source_eq_union_sdiff_strictRoof_of_noEdgeEnters_general
        hNoEnter,
      hStrict]
    ext x
    constructor
    · rintro ⟨hxA | hxC, hxNotStrict⟩
      · exact ⟨Or.inl hxA, hxNotStrict⟩
      · exact ⟨Or.inr (hCD hxC), hxNotStrict⟩
    · rintro ⟨hxA | hxD, hxNotStrict⟩
      · exact ⟨Or.inl hxA, hxNotStrict⟩
      · by_cases hxC : x ∈ C
        · exact ⟨Or.inr hxC, hxNotStrict⟩
        · exact False.elim (hxNotStrict (hDCStrict ⟨hxD, hxC⟩))

/-- Aharoni--Berger Corollary 2.28, left-hand identity, with exactly its
source-level hypotheses: no disjointness between the source and either
commitment set is needed. -/
theorem quotient_quotient_essential_union_left_general
    (G : DWeb V) (X₁ X₂ : Set V)
    (hNoEnter : G.NoEdgeEnters G.source) :
    (G.quotient X₁).quotient (G.essential (X₁ ∪ X₂)) =
      G.quotient (G.essential (X₁ ∪ X₂)) := by
  let U := X₁ ∪ X₂
  let Y := G.essential U
  have hX₁U : X₁ ⊆ U := Set.subset_union_left
  have hYU : Y ⊆ U := G.essential_subset U
  have hX₁Y_U : X₁ ∪ Y ⊆ U := Set.union_subset hX₁U hYU
  have hY_X₁Y : G.essential U ⊆ X₁ ∪ Y := Set.subset_union_right
  have hQU : G.quotient (X₁ ∪ Y) = G.quotient U :=
    G.quotient_eq_of_essential_subset_general hX₁Y_U hY_X₁Y hNoEnter
  have hQY : G.quotient Y = G.quotient U :=
    G.quotient_eq_of_essential_subset_general hYU Set.Subset.rfl hNoEnter
  calc
    (G.quotient X₁).quotient (G.essential (X₁ ∪ X₂)) =
        G.quotient (X₁ ∪ Y) := by
          simpa only [U, Y] using
            G.quotient_quotient_eq_union X₁ Y hNoEnter
    _ = G.quotient U := hQU
    _ = G.quotient Y := hQY.symm
    _ = G.quotient (G.essential (X₁ ∪ X₂)) := rfl

/-- Symmetric right-hand identity in the general form of Corollary 2.28. -/
theorem quotient_quotient_essential_union_right_general
    (G : DWeb V) (X₁ X₂ : Set V)
    (hNoEnter : G.NoEdgeEnters G.source) :
    (G.quotient X₂).quotient (G.essential (X₁ ∪ X₂)) =
      G.quotient (G.essential (X₁ ∪ X₂)) := by
  simpa only [Set.union_comm X₂ X₁] using
    G.quotient_quotient_essential_union_left_general X₂ X₁ hNoEnter

end DWeb

end Erdos599
