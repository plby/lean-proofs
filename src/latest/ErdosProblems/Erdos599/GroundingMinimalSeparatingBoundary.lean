/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CardinalInduction
import ErdosProblems.Erdos599.Popular

/-!
# Minimal separating sub-boundaries for the grounding construction

The literal set `BB` in Assertion 8.18 must be retained while proving
separation, but the switched relation may meet it more than once on one raw
component.  This file supplies the first global normalization step: every
separator contains an inclusion-minimal separating subset.

The only compactness input is that all paths tested by `Popular.IsSeparator`
are finite.  Hence the intersection of a nonempty descending chain of
separators is again a separator.  Zorn's lemma then gives a minimal member.
Every point of the resulting boundary has a private source--target path
meeting the boundary at that point alone.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingMinimalSeparatingBoundary

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- The finite-path separator predicate is exactly source containment in the
roof. -/
theorem isSeparator_iff_source_subset_roof (C : Set V) :
    Popular.IsSeparator Gamma C ↔ Gamma.source ⊆ Gamma.roof C := by
  constructor
  · intro hC a ha p hp
    exact hC p (by simpa only [hp.1] using ha) hp.2
  · intro hC p hpSource hpTarget
    exact hC hpSource p ⟨rfl, hpTarget⟩

/-- A finite set of vertices can be simultaneously avoided by one member of
a nonempty inclusion-chain, provided every vertex is avoided by some member
of the chain. -/
private theorem exists_chain_member_disjoint_finite
    {c : Set (Set V)} (hchain : IsChain (· ⊆ ·) c) (hc : c.Nonempty)
    {F : Set V} (hF : F.Finite)
    (havoid : ∀ x ∈ F, ∃ S ∈ c, x ∉ S) :
    ∃ S ∈ c, Disjoint F S := by
  induction F, hF using Set.Finite.induction_on with
  | empty =>
      obtain ⟨S, hSc⟩ := hc
      exact ⟨S, hSc, Set.empty_disjoint S⟩
  | @insert x F hx hF ih =>
      have havoidF : ∀ y ∈ F, ∃ S ∈ c, y ∉ S := by
        intro y hy
        exact havoid y (Set.mem_insert_of_mem x hy)
      obtain ⟨S, hSc, hFS⟩ := ih havoidF
      obtain ⟨R, hRc, hxR⟩ := havoid x (Set.mem_insert x F)
      rcases hchain.total hSc hRc with hSR | hRS
      · refine ⟨S, hSc, ?_⟩
        rw [Set.disjoint_left]
        intro y hy hys
        rcases hy with rfl | hyF
        · exact hxR (hSR hys)
        · exact Set.disjoint_left.1 hFS hyF hys
      · refine ⟨R, hRc, ?_⟩
        rw [Set.disjoint_left]
        intro y hy hyr
        rcases hy with rfl | hyF
        · exact hxR hyr
        · exact Set.disjoint_left.1 hFS hyF (hRS hyr)

/-- The intersection of a nonempty inclusion-chain of finite-path separators
is again a separator. -/
theorem isSeparator_sInter_of_chain
    {c : Set (Set V)} (hc : c.Nonempty) (hchain : IsChain (· ⊆ ·) c)
    (hsep : ∀ S ∈ c, Popular.IsSeparator Gamma S) :
    Popular.IsSeparator Gamma (⋂₀ c) := by
  intro p hpSource hpTarget
  by_contra hmeet
  have havoidPoint : ∀ x ∈ p.support, ∃ S ∈ c, x ∉ S := by
    intro x hxp
    have hx : ¬ ∀ S ∈ c, x ∈ S := by
      intro hxall
      apply hmeet
      exact ⟨x, hxp, (Set.mem_sInter).2 hxall⟩
    push_neg at hx
    exact hx
  obtain ⟨S, hSc, hdisj⟩ :=
    exists_chain_member_disjoint_finite hchain hc p.support_finite havoidPoint
  obtain ⟨x, hxp, hxS⟩ := hsep S hSc p hpSource hpTarget
  exact Set.disjoint_left.1 hdisj hxp hxS

/-- Every finite-path separator `B` contains an inclusion-minimal separator
`T`.  Minimality is stated in the existing source-relative form used by the
cardinal-induction development. -/
theorem exists_minimalSeparatingSubset (B : Set V)
    (hB : Popular.IsSeparator Gamma B) :
    ∃ T : Set V, T ⊆ B ∧ Popular.IsSeparator Gamma T ∧
      CardinalInduction.IsMinimalSeparatorFrom Gamma Gamma.source T := by
  let S : Set (Set V) :=
    {T | T ⊆ B ∧ Popular.IsSeparator Gamma T}
  obtain ⟨T, hTB, hTmin⟩ := zorn_superset_nonempty S (fun c hcS hchain hc ↦ by
    refine ⟨⋂₀ c, ⟨?_, ?_⟩, ?_⟩
    · obtain ⟨U, hUc⟩ := hc
      exact (Set.sInter_subset_of_mem hUc).trans (hcS hUc).1
    · exact isSeparator_sInter_of_chain hc hchain
        (fun U hUc ↦ (hcS hUc).2)
    · intro U hUc
      exact Set.sInter_subset_of_mem hUc) B ⟨Set.Subset.rfl, hB⟩
  refine ⟨T, hTB, hTmin.1.2, ?_⟩
  have hTsepFrom : CardinalInduction.IsSeparatorFrom
      Gamma Gamma.source T :=
    (isSeparator_iff_source_subset_roof T).1 hTmin.1.2
  refine ⟨hTsepFrom, ?_⟩
  intro U hUsep hUT
  apply hTmin.2
  · exact ⟨hUT.trans hTB,
      (isSeparator_iff_source_subset_roof U).2 hUsep⟩
  · exact hUT

/-- Every point of the selected minimal boundary has a private original
source--target path meeting that boundary exactly at the displayed point. -/
theorem exists_privatePath_of_minimalSeparatingSubset
    {T : Set V}
    (hT : CardinalInduction.IsMinimalSeparatorFrom Gamma Gamma.source T)
    {t : V} (ht : t ∈ T) :
    ∃ a ∈ Gamma.source, ∃ p : FinitePath Gamma.graph,
      Gamma.IsTargetPathFrom a p ∧ p.support ∩ T = {t} :=
by
  have hnotSeparator :
      ¬ CardinalInduction.IsSeparatorFrom Gamma Gamma.source (T \ {t}) := by
    intro hseparator
    have hsubset : T ⊆ T \ {t} := hT.2 hseparator Set.diff_subset
    exact (hsubset ht).2 rfl
  change ¬ Gamma.source ⊆ Gamma.roof (T \ {t}) at hnotSeparator
  obtain ⟨a, haSource, haNotRoof⟩ := Set.not_subset.mp hnotSeparator
  obtain ⟨p, hpTarget, hpAvoid⟩ :=
    (Gamma.not_mem_roof_iff (T \ {t}) a).1 haNotRoof
  obtain ⟨x, hxp, hxT⟩ := hT.1 haSource p hpTarget
  have hxt : x = t := by
    by_contra hne
    exact Set.disjoint_left.1 hpAvoid hxp ⟨hxT, hne⟩
  subst x
  refine ⟨a, haSource, p, hpTarget, Set.Subset.antisymm ?_ ?_⟩
  · rintro x ⟨hxp, hxT⟩
    have hxt : x = t := by
      by_contra hne
      exact Set.disjoint_left.1 hpAvoid hxp ⟨hxT, hne⟩
    simpa only [Set.mem_singleton_iff] using hxt
  · intro x hx
    have hxt : x = t := Set.mem_singleton_iff.1 hx
    subst x
    exact ⟨hxp, ht⟩

end GroundingMinimalSeparatingBoundary
end Erdos599

#print axioms Erdos599.GroundingMinimalSeparatingBoundary.exists_minimalSeparatingSubset
#print axioms Erdos599.GroundingMinimalSeparatingBoundary.exists_privatePath_of_minimalSeparatingSubset
