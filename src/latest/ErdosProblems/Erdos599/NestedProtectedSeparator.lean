/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.QuotientRoofTransport
import ErdosProblems.Erdos599.QuotientAssociativity
import ErdosProblems.Erdos599.SingularContinuation
import ErdosProblems.Erdos599.RoofedDeletionQuotient
import ErdosProblems.Erdos599.LadderFrontierInvariants

/-!
# Nested separating boundaries and protected deletion

These are boundary calculations, not half-way linkage assertions. A trimmed
source separator in the first quotient is again a trimmed source separator
in the ambient web. Its quotient is exactly the iterated quotient. Deleting
a carrier roofed by the new boundary preserves the unhindered quotient at
the surviving boundary, without asserting that the deleted ambient web is
unhindered.

The proof is Lemma `nested-protected-boundary` of `tex/599.tex`.
-/

namespace Erdos599.CardinalInduction.NestedProtectedSeparator

open Set

universe u

variable {V : Type u} (G : DWeb V) {C D X : Set V}

/-- The suffix after the last old-boundary hit is a quotient target path.
Consequently the new quotient separator roofs the entire old boundary. -/
theorem old_subset_roof_new
    (hCsep : IsSeparatorFrom G G.source C)
    (hCtrim : IsTrimmedSeparator G C)
    (hDsep : IsSeparatorFrom (G.quotient C) (G.quotient C).source D) :
    C ⊆ G.roof D := by
  intro c hc p hp
  have hmeet : G.Meets p C :=
    ⟨p.start, p.start_mem_support, hp.1 ▸ hc⟩
  let hm : p.walk.Meets C :=
    ⟨hmeet.choose, hmeet.choose_spec.1, hmeet.choose_spec.2⟩
  let L := p.walk.lastHit C hm
  have hLEss : L.startpoint ∈ G.essential C :=
    G.lastHit_mem_essential C p hp hmeet
  have hLSource : L.startpoint ∈ (G.quotient C).source := by
    rw [SingularContinuation.quotient_source_eq_stopover G hCsep hCtrim]
    exact (Set.ext_iff.mp hCtrim L.startpoint).mp hLEss
  obtain ⟨q, hqStart, hqFinish, hqSupport⟩ :=
    G.exists_quotientPath_from_lastHit C p hp hmeet
  obtain ⟨d, hdq, hdD⟩ := hDsep hLSource q
    ⟨hqStart, hqFinish ▸ hp.2⟩
  have hdL : d ∈ L.walk.support := by
    rw [hqSupport] at hdq
    exact hdq
  exact ⟨d, L.support_subset hdL, hdD⟩

/-- Source separation also lifts from the nested quotient. -/
theorem new_isSeparator
    (hCsep : IsSeparatorFrom G G.source C)
    (hCtrim : IsTrimmedSeparator G C)
    (hDsep : IsSeparatorFrom (G.quotient C) (G.quotient C).source D) :
    IsSeparatorFrom G G.source D :=
  hCsep.trans (G.roof_cut (old_subset_roof_new G hCsep hCtrim hDsep))

/-- Essentializing the union and then quotienting is precisely the nested
quotient; only the no-incoming-source condition is needed. -/
theorem quotient_essential_union_eq_iterated
    (hNoEnter : G.NoEdgeEnters G.source)
    (hCsep : IsSeparatorFrom G G.source C) :
    G.quotient (G.essential (C ∪ D)) = (G.quotient C).quotient D := by
  calc
    G.quotient (G.essential (C ∪ D)) = G.quotient (C ∪ D) :=
      G.quotient_essential_eq_of_subset_roof (C ∪ D)
        (hCsep.trans (G.roof_mono Set.subset_union_left))
    _ = (G.quotient C).quotient D :=
      (G.quotient_quotient_eq_union C D hNoEnter).symm

/-- Comparing the sources of the two identical quotient webs identifies
the ambient essential union with the second boundary. -/
theorem essential_union_eq_new
    (hNoEnter : G.NoEdgeEnters G.source)
    (hCsep : IsSeparatorFrom G G.source C)
    (hDsep : IsSeparatorFrom (G.quotient C) (G.quotient C).source D)
    (hDtrim : IsTrimmedSeparator (G.quotient C) D) :
    G.essential (C ∪ D) = D := by
  have hsep : IsSeparatorFrom G G.source (G.essential (C ∪ D)) := by
    rw [IsSeparatorFrom, G.roof_essential]
    exact hCsep.trans (G.roof_mono Set.subset_union_left)
  calc
    G.essential (C ∪ D) = (G.quotient (G.essential (C ∪ D))).source :=
      (SingularContinuation.quotient_source_eq_stopover G hsep
        (G.essential_idem (C ∪ D))).symm
    _ = ((G.quotient C).quotient D).source := by
      rw [quotient_essential_union_eq_iterated G hNoEnter hCsep]
    _ = D := SingularContinuation.quotient_source_eq_stopover
      (G.quotient C) hDsep hDtrim

/-- A trimmed nested separator is trimmed in the ambient web. -/
theorem new_isTrimmed
    (hNoEnter : G.NoEdgeEnters G.source)
    (hCsep : IsSeparatorFrom G G.source C)
    (hDsep : IsSeparatorFrom (G.quotient C) (G.quotient C).source D)
    (hDtrim : IsTrimmedSeparator (G.quotient C) D) :
    IsTrimmedSeparator G D := by
  rw [IsTrimmedSeparator,
    ← essential_union_eq_new G hNoEnter hCsep hDsep hDtrim]
  exact G.essential_idem (C ∪ D)

/-- The nested quotient is exactly the ambient quotient by the new set. -/
theorem quotient_new_eq_iterated
    (hNoEnter : G.NoEdgeEnters G.source)
    (hCsep : IsSeparatorFrom G G.source C)
    (hDsep : IsSeparatorFrom (G.quotient C) (G.quotient C).source D)
    (hDtrim : IsTrimmedSeparator (G.quotient C) D) :
    G.quotient D = (G.quotient C).quotient D := by
  conv_lhs => rw [← essential_union_eq_new G hNoEnter hCsep hDsep hDtrim]
  exact quotient_essential_union_eq_iterated G hNoEnter hCsep

/-- The new boundary cannot meet the old strict roof. -/
theorem disjoint_new_strictRoof_old
    (hNoEnter : G.NoEdgeEnters G.source)
    (hCsep : IsSeparatorFrom G G.source C)
    (hDsep : IsSeparatorFrom (G.quotient C) (G.quotient C).source D)
    (hDtrim : IsTrimmedSeparator (G.quotient C) D) :
    Disjoint D (G.strictRoof C) := by
  have h := G.disjoint_essential_union_strictRoof_left C D
  rwa [essential_union_eq_new G hNoEnter hCsep hDsep hDtrim] at h

/-- The whole new quotient roof lifts, including the isolated vertices
which belong to the old strict roof. -/
theorem quotient_roof_subset_original
    (hCsep : IsSeparatorFrom G G.source C)
    (hCtrim : IsTrimmedSeparator G C)
    (hDsep : IsSeparatorFrom (G.quotient C) (G.quotient C).source D) :
    (G.quotient C).roof D ⊆ G.roof D := by
  have hCD := old_subset_roof_new G hCsep hCtrim hDsep
  intro x hx
  by_cases hxStrict : x ∈ G.strictRoof C
  · exact G.roof_cut hCD hxStrict.1
  · exact G.quotient_roof_subset_original_roof_of_essential C D
      ((G.essential_subset C).trans hCD) ⟨hx, hxStrict⟩

/-- All boundary invariants needed by a finite protected successor. -/
theorem protected_new_boundary
    (hNoEnter : G.NoEdgeEnters G.source)
    (hCsep : IsSeparatorFrom G G.source C)
    (hCtrim : IsTrimmedSeparator G C)
    (hDsep : IsSeparatorFrom (G.quotient C) (G.quotient C).source D)
    (hDtrim : IsTrimmedSeparator (G.quotient C) D)
    (hQ : ((G.quotient C).quotient D).IsUnhindered)
    (hX : X ⊆ G.roof D) :
    IsTrimmedSeparator (G.delete X) (D \ X) ∧
      IsSeparatorFrom (G.delete X) (G.delete X).source (D \ X) ∧
      ((G.delete X).quotient (D \ X)).IsUnhindered := by
  have htrim := new_isTrimmed G hNoEnter hCsep hDsep hDtrim
  have hsep := new_isSeparator G hCsep hCtrim hDsep
  have hquot : (G.quotient D).IsUnhindered := by
    rw [quotient_new_eq_iterated G hNoEnter hCsep hDsep hDtrim]
    exact hQ
  refine ⟨G.delete_essential_sdiff_eq_of_subset_roof hX htrim, ?_, ?_⟩
  · change (G.delete X).source ⊆ (G.delete X).roof (D \ X)
    rw [G.delete_roof_sdiff_eq_of_subset_roof hX htrim]
    exact Set.sdiff_subset.trans hsep
  · have h := G.delete_quotient_isUnhindered_of_subset_roof hX htrim hsep hquot
    rw [G.delete_quotient_eq_quotient_delete_inter_of_subset_roof
      hX htrim hsep] at h
    rw [G.delete_quotient_sdiff_eq_quotient_delete_inter_of_subset_roof
      hX htrim hsep]
    exact h

#print axioms essential_union_eq_new
#print axioms quotient_roof_subset_original
#print axioms protected_new_boundary

end Erdos599.CardinalInduction.NestedProtectedSeparator
