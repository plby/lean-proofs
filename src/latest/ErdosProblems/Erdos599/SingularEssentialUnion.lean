/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CardinalInduction
import ErdosProblems.Erdos599.QuotientAssociativity

/-!
# Essential unions of successive singular stopovers

In the singular construction a first stopover `C` is chosen in a web `G`,
and a second stopover `D` is chosen in the quotient `G / C`.  The ambient
stopover which records both choices is

`G.essential (C ∪ D)`.

This file collects the set and quotient identities needed to pass from the
two-stage construction back to the original web.  In particular, trimming
`D` in `G / C` ensures that no point of `D` is discarded by ambient
essentialization.  Quotient associativity then identifies the quotient by
the combined stopover with the iterated quotient.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularEssentialUnion

universe u

variable {V : Type u}

/-- The ambient stopover obtained by composing `C` with a stopover `D` in
the quotient by `C`. -/
def composedStopover (G : DWeb V) (C D : Set V) : Set V :=
  G.essential (C ∪ D)

/-- Ambient essentialization makes the composed stopover trimmed. -/
theorem composedStopover_isTrimmed (G : DWeb V) (C D : Set V) :
    IsTrimmedSeparator G (composedStopover G C D) := by
  exact G.essential_idem (C ∪ D)

/-- A point which is essential in the second-stage stopover remains
essential in the ambient union.  This is the set-theoretic content of the
strict-roof identity for an iterated quotient. -/
theorem right_subset_composedStopover
    (G : DWeb V) (C : Set V) {D : Set V}
    (hD : IsTrimmedSeparator (G.quotient C) D) :
    D ⊆ composedStopover G C D := by
  intro x hxD
  rw [composedStopover, G.mem_essential_iff]
  refine ⟨Or.inr hxD, ?_⟩
  intro hxRoof
  have hxQEssential : x ∈ (G.quotient C).essential D := by
    rw [hD]
    exact hxD
  have hxStrictG : x ∈ G.strictRoof (C ∪ D) := by
    refine ⟨G.subset_roof (C ∪ D) (Or.inr hxD), ?_⟩
    intro hxEssential
    exact hxEssential.2 hxRoof
  have hxStrictQ : x ∈ (G.quotient C).strictRoof D := by
    rw [G.strictRoof_quotient_eq_strictRoof_union C D]
    exact hxStrictG
  exact hxStrictQ.2 hxQEssential

/-- If `C` separates the original source, then the composed stopover does
as well.  Essentialization does not change a roof. -/
theorem source_subset_roof_composedStopover
    (G : DWeb V) {C : Set V} (D : Set V)
    (hC : IsSeparatorFrom G G.source C) :
    IsSeparatorFrom G G.source (composedStopover G C D) := by
  unfold IsSeparatorFrom composedStopover
  rw [G.roof_essential]
  exact hC.trans (G.roof_mono Set.subset_union_left)

/-- Quotienting by the composed essential stopover is the same as first
quotienting by `C` and then by `D`.  Normalized singular constructions
supply `hNoEnter` directly. -/
theorem quotient_composedStopover_eq_iterated
    (G : DWeb V) {C : Set V} (D : Set V)
    (hC : IsSeparatorFrom G G.source C)
    (hNoEnter : G.NoEdgeEnters G.source) :
    G.quotient (composedStopover G C D) =
      (G.quotient C).quotient D := by
  have hsourceUnion : G.source ⊆ G.roof (C ∪ D) :=
    hC.trans (G.roof_mono Set.subset_union_left)
  calc
    G.quotient (composedStopover G C D) =
        G.quotient (C ∪ D) :=
      G.quotient_essential_eq_of_subset_roof (C ∪ D) hsourceUnion
    _ = (G.quotient C).quotient D :=
      (G.quotient_quotient_eq_union C D hNoEnter).symm

/-- Unhinderedness of the second-stage quotient transports to the single
ambient quotient by the composed stopover. -/
theorem composedStopover_quotient_isUnhindered
    (G : DWeb V) {C : Set V} (D : Set V)
    (hC : IsSeparatorFrom G G.source C)
    (hNoEnter : G.NoEdgeEnters G.source)
    (hIterated : ((G.quotient C).quotient D).IsUnhindered) :
    (G.quotient (composedStopover G C D)).IsUnhindered := by
  rw [quotient_composedStopover_eq_iterated G D hC hNoEnter]
  exact hIterated

/-- The four composition facts in the form most convenient for a singular
successor step.  The second-stage separator premise is recorded explicitly
because it is part of the construction certificate, although only its
trimmedness is needed for the inclusion `D ⊆ E`. -/
theorem composedStopover_facts
    (G : DWeb V) {C D : Set V}
    (hCsep : IsSeparatorFrom G G.source C)
    (_hDsep : IsSeparatorFrom (G.quotient C) (G.quotient C).source D)
    (hDtrim : IsTrimmedSeparator (G.quotient C) D)
    (hNoEnter : G.NoEdgeEnters G.source)
    (hIterated : ((G.quotient C).quotient D).IsUnhindered) :
    IsTrimmedSeparator G (composedStopover G C D) ∧
      D ⊆ composedStopover G C D ∧
      IsSeparatorFrom G G.source (composedStopover G C D) ∧
      (G.quotient (composedStopover G C D)).IsUnhindered := by
  exact ⟨composedStopover_isTrimmed G C D,
    right_subset_composedStopover G C hDtrim,
    source_subset_roof_composedStopover G D hCsep,
    composedStopover_quotient_isUnhindered G D hCsep hNoEnter hIterated⟩

end SingularEssentialUnion
end CardinalInduction
end Erdos599

