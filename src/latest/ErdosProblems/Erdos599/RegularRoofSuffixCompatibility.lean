/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularCompletedPendingSplice

/-!
# Compatibility from last-frontier suffix shadows

A comparison component obtained by cutting an old completed path at its
last visit to the old frontier covers the part of that path outside the old
*roof*.  It need not cover earlier visits to the frontier, so the older
`strictRoof`-suffix criterion is unnecessarily strong for this construction.

The missing frontier case is controlled directly by ownership.  Every used
component meets the old frontier only at the initial vertex of an old
pending component.  Since the old row is a warp, that vertex cannot lie on
an old completed component.  The lemma below packages exactly this
two-region argument.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace RegularRoofSuffixCompatibility

open SingularExtension SliceSpliceSource

universe u

variable {V : Type u}

/-- A family which meets an old pending frontier only at its own initial
vertex is owned there by the carrier of the old pending row.  This is the
precise frontier fact supplied by a `CleanTargetSlice`: its installed
family starts on the old pending terminal frontier. -/
theorem frontierOwner_of_sourcePure
    (G : DWeb V) {old used : Set G.DPath} {C : Set V}
    (hsource : ∀ q ∈ used, q.support ∩ C = {q.initial})
    (hinitial : G.initialSet used ⊆
      G.terminalFrontier (pendingPart G old)) :
    G.vertexSet used ∩ C ⊆ G.vertexSet (pendingPart G old) := by
  rintro x ⟨⟨q, hqUsed, hxq⟩, hxC⟩
  have hxInitial : x = q.initial := by
    have hx : x ∈ q.support ∩ C := ⟨hxq, hxC⟩
    rw [hsource q hqUsed] at hx
    exact Set.mem_singleton_iff.mp hx
  subst x
  obtain ⟨p, hpPending, hpTerminal⟩ :=
    hinitial ⟨q, hqUsed, rfl⟩
  refine ⟨p, hpPending, ?_⟩
  rcases p with p | r
  · have hfinish : p.finish = q.initial := Option.some.inj hpTerminal
    exact hfinish ▸ p.finish_mem_support
  · cases hpTerminal

/-- The common installed family of a clean/target slice has the frontier
ownership required by `cleanTargetStep_of_roofSuffixShadow`. -/
theorem frontierOwner_of_cleanTargetSlice
    (G : DWeb V) {old : Set G.DPath} {C right U : Set V}
    (S : RegularCompletedPendingSplice.CleanTargetSlice G C right U)
    (hC : C = G.terminalFrontier (pendingPart G old)) :
    G.vertexSet (S.target ∪ S.clean) ∩ C ⊆
      G.vertexSet (pendingPart G old) := by
  apply frontierOwner_of_sourcePure G S.source_pure
  rw [S.initialSet_union, hC]

/-- If every old completed component already lies below the old roof, no
suffix comparison is needed.  A used component avoids the strict roof, so
any collision is forced onto the essential frontier; frontier ownership then
reduces it to a collision between two distinct members of the old warp. -/
theorem disjoint_subfamily_of_roofedCompleted
    (G : DWeb V) {old used : Set G.DPath} {C : Set V}
    (hOld : G.IsWarp old)
    (hessential : G.essential C = C)
    (hcompletedRoof : G.vertexSet (completedPart G old) ⊆ G.roof C)
    (husedAvoid : G.vertexSet used ⊆ (G.strictRoof C)ᶜ)
    (husedFrontierOwner : G.vertexSet used ∩ C ⊆
      G.vertexSet (pendingPart G old)) :
    Disjoint (G.vertexSet (completedPart G old))
      (G.vertexSet used) := by
  apply Set.disjoint_left.2
  intro x hxCompleted hxUsed
  have hxRoof : x ∈ G.roof C := hcompletedRoof hxCompleted
  have hxNotStrict : x ∉ G.strictRoof C := husedAvoid hxUsed
  have hxEssential : x ∈ G.essential C := by
    by_contra hxNotEssential
    exact hxNotStrict ⟨hxRoof, hxNotEssential⟩
  have hxC : x ∈ C := hessential ▸ hxEssential
  obtain ⟨f, hfCompleted, hxf⟩ := hxCompleted
  obtain ⟨p, hpPending, hxp⟩ :=
    husedFrontierOwner ⟨hxUsed, hxC⟩
  have hfp : f ≠ p := by
    intro hfp
    subst p
    exact hpPending.2 hfCompleted
  exact Set.disjoint_left.1
    (hOld hfCompleted.1 hpPending.1 hfp) hxf hxp

/-- Direct provider-facing clean-step criterion for a canonical row lying
below its current roof.  This is the comparison-free form used by the
source-9.15 recursion. -/
theorem cleanTargetStep_of_roofedCompleted
    (G : DWeb V) {old used : Set G.DPath} {C : Set V}
    (hOld : G.IsWarp old)
    (hessential : G.essential C = C)
    (hcompletedRoof : G.vertexSet (completedPart G old) ⊆ G.roof C)
    (husedWarp : G.IsWarp used)
    (husedAvoid : G.vertexSet used ⊆ (G.strictRoof C)ᶜ)
    (husedFrontierOwner : G.vertexSet used ∩ C ⊆
      G.vertexSet (pendingPart G old))
    (hcompat : G.StarCompatible (pendingPart G old) used) :
    RegularCompletedPendingSplice.IsCleanTargetStep
      G old used hcompat := by
  apply RegularCompletedPendingSplice.IsCleanTargetStep.of_disjoint_slice
    hOld husedWarp
  exact disjoint_subfamily_of_roofedCompleted G hOld hessential
    hcompletedRoof husedAvoid husedFrontierOwner

/-- A full comparison warp whose unused components shadow the portions of
old completed paths outside the old roof separates its used subfamily from
the completed carrier.

Inside the old roof, avoidance of the strict roof reduces a possible
intersection to the essential frontier.  The `used_frontier_owner` premise
then identifies that vertex with the initial vertex of an old pending
component, contradicting disjointness in the old warp.  Outside the roof,
the unused shadow and the used component are distinct members of the full
comparison warp. -/
theorem disjoint_subfamily_of_roofSuffixShadow
    (G : DWeb V) {old full used : Set G.DPath} {C : Set V}
    (hOld : G.IsWarp old)
    (hessential : G.essential C = C)
    (hfull : G.IsWarp full)
    (hused : used ⊆ full)
    (husedAvoid : G.vertexSet used ⊆ (G.strictRoof C)ᶜ)
    (husedFrontierOwner : G.vertexSet used ∩ C ⊆
      G.vertexSet (pendingPart G old))
    (hshadow : ∀ f ∈ completedPart G old, ∃ t ∈ full,
      t ∉ used ∧ f.support \ G.roof C ⊆ t.support) :
    Disjoint (G.vertexSet (completedPart G old))
      (G.vertexSet used) := by
  apply Set.disjoint_left.2
  intro x hxCompleted hxUsed
  obtain ⟨f, hfCompleted, hxf⟩ := hxCompleted
  obtain ⟨q, hqUsed, hxq⟩ := hxUsed
  have hxNotStrict : x ∉ G.strictRoof C :=
    husedAvoid ⟨q, hqUsed, hxq⟩
  by_cases hxRoof : x ∈ G.roof C
  · have hxEssential : x ∈ G.essential C := by
      by_contra hxNotEssential
      exact hxNotStrict ⟨hxRoof, hxNotEssential⟩
    have hxC : x ∈ C := hessential ▸ hxEssential
    obtain ⟨p, hpPending, hxp⟩ :=
      husedFrontierOwner ⟨⟨q, hqUsed, hxq⟩, hxC⟩
    have hfp : f ≠ p := by
      intro hfp
      subst p
      exact hpPending.2 hfCompleted
    exact Set.disjoint_left.1
      (hOld hfCompleted.1 hpPending.1 hfp) hxf hxp
  · obtain ⟨t, htFull, htUnused, hft⟩ := hshadow f hfCompleted
    have hxt : x ∈ t.support := hft ⟨hxf, hxRoof⟩
    have htq : t ≠ q := by
      intro htq
      subst q
      exact htUnused hqUsed
    exact Set.disjoint_left.1
      (hfull htFull (hused hqUsed) htq) hxt hxq

/-- Provider-facing form of
`disjoint_subfamily_of_roofSuffixShadow`.  It discharges the exact
completed/pending cross-disjointness predicate used by the regular splice. -/
theorem cleanTargetStep_of_roofSuffixShadow
    (G : DWeb V) {old full used : Set G.DPath} {C : Set V}
    (hOld : G.IsWarp old)
    (hessential : G.essential C = C)
    (hfull : G.IsWarp full)
    (hused : used ⊆ full)
    (husedAvoid : G.vertexSet used ⊆ (G.strictRoof C)ᶜ)
    (husedFrontierOwner : G.vertexSet used ∩ C ⊆
      G.vertexSet (pendingPart G old))
    (hshadow : ∀ f ∈ completedPart G old, ∃ t ∈ full,
      t ∉ used ∧ f.support \ G.roof C ⊆ t.support)
    (hcompat : G.StarCompatible (pendingPart G old) used) :
    RegularCompletedPendingSplice.IsCleanTargetStep
      G old used hcompat := by
  apply RegularCompletedPendingSplice.IsCleanTargetStep.of_disjoint_slice
    hOld
  · exact hfull.subset hused
  · exact disjoint_subfamily_of_roofSuffixShadow G hOld hessential
      hfull hused husedAvoid husedFrontierOwner hshadow

end RegularRoofSuffixCompatibility
end CardinalInduction
end Erdos599
