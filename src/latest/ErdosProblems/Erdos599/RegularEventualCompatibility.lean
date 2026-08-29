/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularCompletedPendingSplice
import ErdosProblems.Erdos599.RegularJointSafeReplacement

/-!
# Eventual slice compatibility with completed components

Permanent deletion of completed paths is stronger than the source regular
recursion needs.  A later full frontier linkage can instead carry a shadow
suffix for each completed component.  Since that full family is a warp, all
other components of the later linkage avoid the shadow.  After restricting
the later family to the pending frontier coordinates, the completed carrier
is therefore disjoint from the used slice.

This file isolates that elementary argument.  Constructing the shadow
suffixes is the history-sensitive part of the regular provider; no
unhinderedness-after-deletion assertion is assumed here.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace RegularEventualCompatibility

open SingularExtension SliceSpliceSource

universe u

variable {V : Type u}

/-- A completed path cannot meet a used subfamily of a larger comparison
warp when a different comparison component shadows every part of the
completed path outside the old strict roof.

Only the *used* subfamily has to avoid the old strict roof.  This is the
form needed by the protected-residual construction: already completed
components may be retained verbatim in `Tfull` and serve as their own
shadows, while the residual fill is the subfamily actually used for the
next clean slice. -/
theorem disjoint_subfamily_of_suffixShadow
    (G : DWeb V) {F Tfull Tused : Set G.DPath} {C : Set V}
    (hTfull : G.IsWarp Tfull)
    (hused : Tused ⊆ Tfull)
    (husedAvoid : G.vertexSet Tused ⊆ (G.strictRoof C)ᶜ)
    (hshadow : ∀ f ∈ F, ∃ t ∈ Tfull,
      t ∉ Tused ∧ f.support \ G.strictRoof C ⊆ t.support) :
    Disjoint (G.vertexSet F) (G.vertexSet Tused) := by
  apply Set.disjoint_left.2
  intro x hxF hxUsed
  obtain ⟨f, hfF, hxf⟩ := hxF
  obtain ⟨q, hqUsed, hxq⟩ := hxUsed
  obtain ⟨t, htT, htNotUsed, hft⟩ := hshadow f hfF
  have hxNotStrict : x ∉ G.strictRoof C := by
    exact husedAvoid ⟨q, hqUsed, hxq⟩
  have hxt : x ∈ t.support := hft ⟨hxf, hxNotStrict⟩
  have htq : t ≠ q := by
    intro htq
    subst q
    exact htNotUsed hqUsed
  exact Set.disjoint_left.1 (hTfull htT (hused hqUsed) htq) hxt hxq

/-- A completed path cannot meet a used later component if the later full
warp contains a different component shadowing every part of the completed
path outside the old strict roof.

The shadow's initial coordinate is required to lie outside `D`, whereas the
used family is the initial restriction to `D`; hence the shadow and the used
component are distinct members of the later warp. -/
theorem disjoint_initialRestriction_of_suffixShadow
    (G : DWeb V) {F T : Set G.DPath} {C D : Set V}
    (hT : G.IsWarp T)
    (hTavoid : G.vertexSet T ⊆ (G.strictRoof C)ᶜ)
    (hshadow : ∀ f ∈ F, ∃ t ∈ T,
      t.initial ∉ D ∧ f.support \ G.strictRoof C ⊆ t.support) :
    Disjoint (G.vertexSet F)
      (G.vertexSet (initialRestriction G T D)) := by
  apply disjoint_subfamily_of_suffixShadow G hT
  · exact fun _ hp ↦ hp.1
  · exact (vertexSet_initialRestriction_subset G T D).trans hTavoid
  · intro f hf
    obtain ⟨t, htT, htInitial, hft⟩ := hshadow f hf
    exact ⟨t, htT, (fun htUsed ↦ htInitial htUsed.2), hft⟩

/-- Provider-facing form of `disjoint_subfamily_of_suffixShadow`.  It
constructs a completed/pending successor directly from an arbitrary used
subfamily of a full comparison warp. -/
theorem cleanTargetStep_of_used_suffixShadow
    (G : DWeb V) {W Tfull Tused : Set G.DPath} {C : Set V}
    (hW : G.IsWarp W)
    (hTfull : G.IsWarp Tfull)
    (hused : Tused ⊆ Tfull)
    (husedAvoid : G.vertexSet Tused ⊆ (G.strictRoof C)ᶜ)
    (hshadow : ∀ f ∈ completedPart G W, ∃ t ∈ Tfull,
      t ∉ Tused ∧ f.support \ G.strictRoof C ⊆ t.support)
    (hcompat : G.StarCompatible (pendingPart G W) Tused) :
    RegularCompletedPendingSplice.IsCleanTargetStep G W Tused hcompat := by
  apply RegularCompletedPendingSplice.IsCleanTargetStep.of_disjoint_slice
    hW
  · exact fun p hp q hq hpq ↦ hTfull (hused hp) (hused hq) hpq
  · exact disjoint_subfamily_of_suffixShadow G hTfull hused
      husedAvoid hshadow

/-- Provider-facing form: the shadow criterion is enough to discharge the
cross-disjointness premise of the completed/pending successor constructor. -/
theorem cleanTargetStep_of_suffixShadow
    (G : DWeb V) {W Tfull : Set G.DPath} {C D : Set V}
    (hW : G.IsWarp W)
    (hTfull : G.IsWarp Tfull)
    (hTavoid : G.vertexSet Tfull ⊆ (G.strictRoof C)ᶜ)
    (hshadow : ∀ f ∈ completedPart G W, ∃ t ∈ Tfull,
      t.initial ∉ D ∧ f.support \ G.strictRoof C ⊆ t.support)
    (hcompat : G.StarCompatible (pendingPart G W)
      (initialRestriction G Tfull D)) :
    RegularCompletedPendingSplice.IsCleanTargetStep G W
      (initialRestriction G Tfull D) hcompat := by
  apply RegularCompletedPendingSplice.IsCleanTargetStep.of_disjoint_slice
    hW
  · intro p hp q hq hpq
    exact hTfull hp.1 hq.1 hpq
  · exact disjoint_initialRestriction_of_suffixShadow G hTfull
      hTavoid hshadow

/-! ## A comparison warp from the protected residual -/

/-- Every vertex of a path in a quotient survives deletion of the strict
roof, provided its initial vertex survives.  Nontrivial edges of the
quotient already carry this information at both endpoints; the proof only
propagates it along a finite walk or a ray. -/
theorem quotientPath_support_subset_quotientVertexSet
    (G : DWeb V) (C : Set V) (p : (G.quotient C).DPath)
    (hstart : p.initial ∈ G.quotientVertexSet C) :
    p.support ⊆ G.quotientVertexSet C := by
  rcases p with p | r
  · intro x hx
    have hwalk : ∀ {a b : V}
        (w : DirectedPath.Walk (G.quotient C).graph a b),
        a ∈ G.quotientVertexSet C →
          ∀ {y}, y ∈ w.support → y ∈ G.quotientVertexSet C := by
      intro a b w ha y hy
      induction w with
      | nil =>
          simp only [DirectedPath.Walk.support_nil,
            List.mem_singleton] at hy
          subst y
          exact ha
      | @cons a b c e w ih =>
          simp only [DirectedPath.Walk.support_cons, List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact ha
          · exact ih ((G.quotient_adj_endpoints e).2.1) hy
    exact hwalk p.walk hstart hx
  · rintro x ⟨n, rfl⟩
    cases n with
    | zero => exact hstart
    | succ n => exact (G.quotient_adj_endpoints (r.adj_succ n)).2.1

/-- The exact comparison family supplied by a protected ambient frame.
The residual fill is chosen in the frame's genuine deletion--quotient web
using the lower-cardinal induction hypothesis, then transported back to the
ambient graph.  Old completed components are retained verbatim.  Hence the
union is a warp, the transported fill avoids the completed carrier, and each
old completed component is literally its own suffix shadow.

The cardinal `max (#requests) aleph0` handles finite as well as infinite
request sets while remaining below the uncountable regular stage cardinal.
No deletion/quotient commutation is used. -/
theorem exists_protectedComparisonWarp_of_lower
    {kappa : Cardinal.{u}} (G : DWeb V) (hNorm : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hkappa : Cardinal.aleph0 < kappa)
    {row : Set G.DPath}
    (F : RegularJointSafeReplacement.ProtectedRestorationFrame G row)
    (hrequestsSmall : Cardinal.mk ↑(F.state.requests) < kappa) :
    ∃ Tused Tfull : Set G.DPath,
      G.IsWarp Tfull ∧
        Tused ⊆ Tfull ∧
        Disjoint (G.vertexSet (completedPart G row))
          (G.vertexSet Tused) ∧
        G.vertexSet Tused ⊆
          (G.strictRoof F.split.boundary)ᶜ ∧
        (∀ f ∈ completedPart G row, ∃ t ∈ Tfull,
          t ∉ Tused ∧
            f.support \ G.strictRoof F.split.boundary ⊆ t.support) := by
  let rho : Cardinal.{u} :=
    max (Cardinal.mk ↑(F.state.requests)) Cardinal.aleph0
  have hrhoKappa : rho < kappa := by
    exact max_lt_iff.mpr ⟨hrequestsSmall, hkappa⟩
  have hrhoInfinite : Cardinal.aleph0 ≤ rho := by
    exact le_max_right _ _
  have hrequestCard : Cardinal.mk ↑(F.state.requests) ≤ rho := by
    exact le_max_left _ _
  have hNoEnterG : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hNoEnterState :
      ((G.delete F.protectedSet).quotient F.split.boundary).NoEdgeEnters
        ((G.delete F.protectedSet).quotient F.split.boundary).source := by
    exact DWeb.NoEdgeEnters.quotient (G.delete F.protectedSet)
      hNoEnterG.delete
  obtain ⟨B⟩ := SingularSafeBatch.exists_fullSourceSafeBatch_of_lower
    hlower hrhoKappa hrhoInfinite
      ((G.delete F.protectedSet).quotient F.split.boundary)
      F.residual_unhindered hNoEnterState
      (by simpa only
        [RegularJointSafeReplacement.ProtectedRestorationFrame.state]
        using F.requests_source) hrequestCard
  let R : Set (G.quotient F.split.boundary).DPath :=
    deletedQuotientFamily G F.split.boundary F.protectedSet B.paths
  let Tused : Set G.DPath :=
    G.liftQuotientFamily F.split.boundary R
  let Tfull : Set G.DPath := completedPart G row ∪ Tused
  have hBwarp : ((G.delete F.protectedSet).quotient
      F.split.boundary).IsWarp B.paths :=
    B.separating.linkage.isWarp
  have hBinitial : ((G.delete F.protectedSet).quotient
      F.split.boundary).initialSet B.paths =
        ((G.delete F.protectedSet).quotient F.split.boundary).source :=
    B.separating.linkage.initialSet_eq
  have hRwarp : (G.quotient F.split.boundary).IsWarp R := by
    exact deletedQuotientFamily_isWarp hBwarp
  have hUsedWarp : G.IsWarp Tused := by
    exact DWeb.IsWarp.liftQuotientFamily G hRwarp
  have hUsedProtected : Disjoint (G.vertexSet Tused) F.protectedSet := by
    apply lift_deletedQuotientFamily_vertexSet_disjoint
    simpa only [RegularJointSafeReplacement.ProtectedRestorationFrame.state]
      using hBinitial.le
  have hRsource :
      (G.quotient F.split.boundary).initialSet R ⊆
        (G.quotient F.split.boundary).source := by
    dsimp only [R]
    rw [deletedQuotientFamily_initialSet]
    intro x hx
    have hxState : x ∈ ((G.delete F.protectedSet).quotient
        F.split.boundary).source := hBinitial ▸ hx
    exact (G.deleteQuotient_source_subset_quotientDelete_source
      F.split.boundary F.protectedSet hxState).1
  have hUsedAvoid : G.vertexSet Tused ⊆
      (G.strictRoof F.split.boundary)ᶜ := by
    rintro x ⟨p, hpUsed, hxp⟩
    obtain ⟨q, hqR, rfl⟩ := hpUsed
    have hqSource : q.initial ∈
        (G.quotient F.split.boundary).source := by
      apply hRsource
      exact ⟨q, hqR, rfl⟩
    have hqStart : q.initial ∈
        G.quotientVertexSet F.split.boundary := by
      rw [G.quotient_source_eq_union_sdiff_strictRoof_of_noEdgeEnters_general
        hNoEnterG] at hqSource
      exact hqSource.2
    exact quotientPath_support_subset_quotientVertexSet G
      F.split.boundary q hqStart (by simpa using hxp)
  have hCompletedProtected :
      G.vertexSet (completedPart G row) ⊆ F.protectedSet := by
    rintro x ⟨p, hp, hxp⟩
    exact F.frozen_protected ⟨p, F.completed_frozen hp, hxp⟩
  have hCross : Disjoint (G.vertexSet (completedPart G row))
      (G.vertexSet Tused) := by
    apply Set.disjoint_left.2
    intro x hxCompleted hxUsed
    exact Set.disjoint_left.1 hUsedProtected hxUsed
      (hCompletedProtected hxCompleted)
  have hCompletedWarp : G.IsWarp (completedPart G row) := by
    intro p hp q hq hpq
    exact F.row_warp hp.1 hq.1 hpq
  have hFullWarp : G.IsWarp Tfull := by
    exact SingularContinuation.isWarp_union_of_disjoint_vertexSet G
      hCompletedWarp hUsedWarp hCross
  refine ⟨Tused, Tfull, hFullWarp, Set.subset_union_right, hCross,
    hUsedAvoid, ?_⟩
  intro f hf
  refine ⟨f, Set.mem_union_left Tused hf, ?_, Set.sdiff_subset⟩
  intro hfUsed
  exact Set.disjoint_left.1 hCross
    ⟨f, hf, f.initial_mem_support⟩
    ⟨f, hfUsed, f.initial_mem_support⟩

end RegularEventualCompatibility
end CardinalInduction
end Erdos599
