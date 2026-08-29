/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayNormalization
import ErdosProblems.Erdos599.WaveLimits

/-!
# Normalization at a source-separating frontier

For an arbitrary set, normalization can enlarge its roof: a path witnessing
failure of roofing may use an edge entering the source.  This obstruction
disappears once the set already roofs the source in the normalized web.  An
original target path which enters the source then has a source--target suffix,
while one which does not enter the source can itself be normalized after its
first target hit.

Consequently a trimmed source-separating frontier has the same roof and
strict roof before and after normalization.  At such a frontier quotienting
commutes with normalization.  This is the precise transport fact needed by
the half-way construction; unlike a global commutation premise, it follows
from the frontier geometry produced by the construction.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {C : Set V}

/-- If `C` roofs the source after normalization, then it already roofs the
source in the original web. -/
theorem source_subset_roof_of_normalized
    (hsource : Gamma.normalized.source ⊆ Gamma.normalized.roof C) :
    Gamma.source ⊆ Gamma.roof C := by
  intro a ha p hp
  have hpA : p.start ∈ Gamma.source := hp.1 ▸ ha
  let q := Gamma.normalizeFinitePath p hpA hp.2
  have hqTarget : Gamma.normalized.IsTargetPathFrom q.start q := by
    exact ⟨rfl, Gamma.normalizeFinitePath_finish_mem p hpA hp.2⟩
  obtain ⟨x, hxq, hxC⟩ := hsource
    (Gamma.normalizeFinitePath_start_mem p hpA hp.2) q hqTarget
  exact ⟨x, Gamma.normalizeFinitePath_support_subset p hpA hp.2 hxq, hxC⟩

/-- Once `C` roofs the normalized source, normalization does not change its
roof. -/
theorem normalized_roof_eq_of_source_subset_roof
    (hsource : Gamma.normalized.source ⊆ Gamma.normalized.roof C) :
    Gamma.normalized.roof C = Gamma.roof C := by
  apply Set.Subset.antisymm
  · intro x hx p hp
    have hsourceOriginal : Gamma.source ⊆ Gamma.roof C :=
      source_subset_roof_of_normalized hsource
    by_cases hmeetsSource : ∃ y, y ∈ p.support ∧ y ∈ Gamma.source
    · obtain ⟨y, hyp, hySource⟩ := hmeetsSource
      let s := p.suffixFromAux y hyp
      have hsTarget : Gamma.IsTargetPathFrom y s := by
        exact ⟨rfl, by simpa [s] using hp.2⟩
      obtain ⟨z, hzs, hzC⟩ := hsourceOriginal hySource s hsTarget
      exact ⟨z, p.suffixFromAux_support_subset y hyp hzs, hzC⟩
    · have htargetMeet : p.walk.Meets Gamma.target :=
        ⟨p.finish, p.finish_mem_support, hp.2⟩
      let f := p.firstHit Gamma.target htargetMeet
      have hfSource : ∀ {z}, z ∈ f.walk.support.tail →
          z ∉ Gamma.source := by
        intro z hz hzSource
        apply hmeetsSource
        exact ⟨z, p.firstHit_support_subset Gamma.target htargetMeet
          (List.mem_of_mem_tail hz), hzSource⟩
      have hfTarget : ∀ {z}, z ∈ f.walk.support.dropLast →
          z ∉ Gamma.target := by
        intro z hz
        exact p.firstHit_no_mem_before Gamma.target htargetMeet hz
      let q : FinitePath Gamma.normalized.graph :=
        { start := f.start
          finish := f.finish
          walk := Gamma.normalizeWalk f.walk hfSource hfTarget
          isPath := by
            change (Gamma.normalizeWalk f.walk hfSource hfTarget).support.Nodup
            rw [Gamma.support_normalizeWalk]
            exact f.isPath }
      have hqTarget : Gamma.normalized.IsTargetPathFrom x q := by
        refine ⟨?_, ?_⟩
        · exact hp.1
        · exact p.firstHit_finish_mem Gamma.target htargetMeet
      obtain ⟨z, hzq, hzC⟩ := hx q hqTarget
      refine ⟨z, ?_, hzC⟩
      apply p.firstHit_support_subset Gamma.target htargetMeet
      change z ∈ (Gamma.normalizeWalk f.walk hfSource hfTarget).support at hzq
      change z ∈ (p.firstHit Gamma.target htargetMeet).walk.support
      simpa only [f, Gamma.support_normalizeWalk] using hzq
  · exact Gamma.roof_subset_normalized_roof C

/-- A trimmed source-separating frontier has the same strict roof before and
after normalization. -/
theorem normalized_strictRoof_eq_of_trimmed_source_roof
    (hsource : Gamma.normalized.source ⊆ Gamma.normalized.roof C)
    (htrim : IsTrimmedSeparator Gamma.normalized C) :
    Gamma.normalized.strictRoof C = Gamma.strictRoof C := by
  have htrimOriginal : IsTrimmedSeparator Gamma C := htrim.of_normalized
  change Gamma.normalized.roof C \ Gamma.normalized.essential C =
    Gamma.roof C \ Gamma.essential C
  rw [normalized_roof_eq_of_source_subset_roof hsource, htrim, htrimOriginal]

/-- At a trimmed frontier roofing the source, quotienting commutes with
normalization. -/
theorem normalized_quotient_eq_of_trimmed_source_roof
    (hsource : Gamma.normalized.source ⊆ Gamma.normalized.roof C)
    (htrim : IsTrimmedSeparator Gamma.normalized C) :
    (Gamma.quotient C).normalized = Gamma.normalized.quotient C := by
  have hsourceOriginal : Gamma.source ⊆ Gamma.roof C :=
    source_subset_roof_of_normalized hsource
  have htrimOriginal : IsTrimmedSeparator Gamma C := htrim.of_normalized
  have hstrict : Gamma.normalized.strictRoof C = Gamma.strictRoof C :=
    normalized_strictRoof_eq_of_trimmed_source_roof hsource htrim
  have hleftSource : (Gamma.quotient C).source = C := by
    rw [DWeb.quotient_source, Set.union_comm]
    calc
      Gamma.essential (C ∪ Gamma.source) = Gamma.essential C :=
        RelationalRoof.essential_union_eq_of_subset_roof
          Gamma.graph.Adj Gamma.target hsourceOriginal
      _ = C := htrimOriginal
  have hrightSource : (Gamma.normalized.quotient C).source = C := by
    rw [DWeb.quotient_source, Set.union_comm]
    calc
      Gamma.normalized.essential (C ∪ Gamma.normalized.source) =
          Gamma.normalized.essential C :=
        RelationalRoof.essential_union_eq_of_subset_roof
          Gamma.normalized.graph.Adj Gamma.normalized.target hsource
      _ = C := htrim
  rw [DWeb.mk.injEq]
  refine ⟨?_, ?_, rfl⟩
  · apply Digraph.ext
    funext u v
    apply propext
    change
      ((Gamma.graph.Adj u v ∧
          u ∉ Gamma.strictRoof C ∧ v ∉ Gamma.strictRoof C ∧ v ∉ C) ∧
          v ∉ (Gamma.quotient C).source ∧ u ∉ Gamma.target) ↔
        ((Gamma.graph.Adj u v ∧ v ∉ Gamma.source ∧ u ∉ Gamma.target) ∧
          u ∉ Gamma.normalized.strictRoof C ∧
          v ∉ Gamma.normalized.strictRoof C ∧ v ∉ C)
    rw [hleftSource, hstrict]
    constructor
    · rintro ⟨⟨huv, huRoof, hvRoof, hvC⟩, _hvC, huTarget⟩
      refine ⟨⟨huv, ?_, huTarget⟩, huRoof, hvRoof, hvC⟩
      intro hvSource
      have hvInRoof : v ∈ Gamma.roof C := hsourceOriginal hvSource
      by_cases hvEssential : v ∈ Gamma.essential C
      · exact hvC (htrimOriginal ▸ hvEssential)
      · exact hvRoof ⟨hvInRoof, hvEssential⟩
    · rintro ⟨⟨huv, _hvSource, huTarget⟩, huRoof, hvRoof, hvC⟩
      exact ⟨⟨huv, huRoof, hvRoof, hvC⟩, hvC, huTarget⟩
  · exact hleftSource.trans hrightSource.symm

/-- A normalized stop-over transports to the original web as soon as its
actual frontier geometry says that it roofs the source.  The quotient
commutation used here is derived by
`normalized_quotient_eq_of_trimmed_source_roof`, not supplied separately. -/
theorem IsHalfwayStopover.liftNormalized_of_source_roof
    {W : Set Gamma.normalized.DPath}
    (hsource : Gamma.normalized.source ⊆ Gamma.normalized.roof C)
    (hC : IsHalfwayStopover Gamma.normalized W C) :
    IsHalfwayStopover Gamma (Gamma.liftNormalizedFamily W) C := by
  exact hC.liftNormalized
    (normalized_quotient_eq_of_trimmed_source_roof hsource hC.minimal)

/-- Witness-oriented altitude transport at a source-roofing stop-over.  Only
the height witness remains construction-specific; quotient unhinderedness is
now automatic from the normalized stop-over and its source roofing. -/
theorem IsHalfwayLinkageOfAltitude.liftNormalized_of_source_roof
    {A0 : Set V} {kappa : Cardinal.{u}}
    {W : Set Gamma.normalized.DPath}
    (hW : IsHalfwayLinkageOfAltitude Gamma.normalized A0 kappa W)
    (hsource : Gamma.normalized.source ⊆ Gamma.normalized.roof C)
    (hC : IsHalfwayStopover Gamma.normalized W C)
    (hheight : HeightAtMost Gamma C kappa) :
    IsHalfwayLinkageOfAltitude Gamma A0 kappa
      (Gamma.liftNormalizedFamily W) := by
  exact halfwayLinkageOfAltitude_of_stopover
    (hC.liftNormalized_of_source_roof hsource)
    hW.2.1.liftNormalized hheight

end CardinalInduction
end Erdos599
