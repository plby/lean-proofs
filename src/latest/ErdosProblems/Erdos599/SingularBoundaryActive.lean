/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularExtension
import ErdosProblems.Erdos599.SingularHalfwayComposition
import ErdosProblems.Erdos599.SingularLinkageGeometry

/-!
# The active boundary at a singular successor row

This file packages the current directed-web analogue of the source proof's
`CleanHalfWayLinkage.boundaryActive` construction.  At a successor row it is
enough to continue the sources which have become active since the preceding
row.  Their present terminals form a small subset of the old terminal
frontier and hence a small subset of the source of the quotient by that
frontier.

The last theorem performs the complete bookkeeping step.  Links already
present at the old row survive the source-star continuation by forward
extension.  Links supplied in the quotient for the newly active terminal
boundary lift through the continuation.  Normalization then restores the
source-purity condition simultaneously for the whole enlarged source set.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularBoundaryActive

universe u

variable {V : Type u}

/-- The old terminal vertices belonging to components whose sources have
just entered `next`.  Sources already in `old` need no new quotient request:
their target links are preserved by forward extension. -/
def newActiveBoundary (G : DWeb V) (W : Set G.DPath)
    (old next : Set V) : Set V :=
  {c | ∃ p ∈ W, p.initial ∈ next \ old ∧ G.terminal? p = some c}

theorem newActiveBoundary_subset_terminalFrontier
    (G : DWeb V) (W : Set G.DPath) (old next : Set V) :
    newActiveBoundary G W old next ⊆ G.terminalFrontier W := by
  rintro c ⟨p, hpW, _hpNew, hpc⟩
  exact ⟨p, hpW, hpc⟩

/-- Exact terminal-frontier data exposes every newly active boundary point
as a source of the quotient web. -/
theorem newActiveBoundary_subset_quotientSource
    {G : DWeb V} (hNorm : G.IsNormalized)
    {I : Type u} {rho : I → Cardinal.{u}}
    (S : SingularExtension.CertifiedTargetRowStage G I rho)
    (i : I) (next : Set V) :
    newActiveBoundary G (S.row.paths i) (S.row.sources i) next ⊆
      (G.quotient (S.stopover i)).source := by
  intro c hc
  apply SingularExtension.trimmed_subset_quotient_source_of_normalized
    hNorm (S.separating i).stopover.minimal
  rw [← S.frontier_eq i]
  exact newActiveBoundary_subset_terminalFrontier
    G (S.row.paths i) (S.row.sources i) next hc

/-- Choose the old component witnessing a newly active boundary point. -/
def boundaryPath (G : DWeb V) (W : Set G.DPath)
    (old next : Set V) (c : newActiveBoundary G W old next) : G.DPath :=
  Classical.choose c.2

theorem boundaryPath_spec (G : DWeb V) (W : Set G.DPath)
    (old next : Set V) (c : newActiveBoundary G W old next) :
    boundaryPath G W old next c ∈ W ∧
      (boundaryPath G W old next c).initial ∈ next \ old ∧
      G.terminal? (boundaryPath G W old next c) = some c.1 :=
  Classical.choose_spec c.2

/-- Sending a boundary terminal back to the initial vertex of its old
component is injective. -/
theorem boundaryInitial_injective
    (G : DWeb V) {W : Set G.DPath} {old next : Set V}
    (hW : G.IsWarp W) :
    Function.Injective (fun c : newActiveBoundary G W old next =>
      (⟨(boundaryPath G W old next c).initial,
        (boundaryPath_spec G W old next c).2.1⟩ :
          {x : V // x ∈ next \ old})) := by
  intro c d hcd
  have hinitial : (boundaryPath G W old next c).initial =
      (boundaryPath G W old next d).initial :=
    congrArg (fun x : {x : V // x ∈ next \ old} => x.1) hcd
  have hpath : boundaryPath G W old next c =
      boundaryPath G W old next d :=
    DWeb.IsWarp.eq_of_initial_eq G hW
      (boundaryPath_spec G W old next c).1
      (boundaryPath_spec G W old next d).1 hinitial
  apply Subtype.ext
  exact Option.some.inj <| calc
    some c.1 = G.terminal? (boundaryPath G W old next c) :=
      (boundaryPath_spec G W old next c).2.2.symm
    _ = G.terminal? (boundaryPath G W old next d) := congrArg _ hpath
    _ = some d.1 := (boundaryPath_spec G W old next d).2.2

theorem mk_newActiveBoundary_le
    {G : DWeb V} {I : Type u} {rho : I → Cardinal.{u}}
    (S : SingularExtension.CertifiedTargetRowStage G I rho)
    (i : I) (next : Set V) :
    Cardinal.mk
        (newActiveBoundary G (S.row.paths i) (S.row.sources i) next) ≤
      Cardinal.mk next := by
  exact (Cardinal.mk_le_of_injective
    (boundaryInitial_injective G (S.row.isWarp i))).trans
      (Cardinal.mk_subtype_mono Set.sdiff_subset)

/-- In particular, a singular-row cardinal bound on the enlarged source set
is inherited by the quotient request. -/
theorem mk_newActiveBoundary_lt
    {G : DWeb V} {I : Type u} {rho : I → Cardinal.{u}}
    (S : SingularExtension.CertifiedTargetRowStage G I rho)
    (i : I) {next : Set V} {kappa : Cardinal.{u}}
    (hcard : Cardinal.mk next < kappa) :
    Cardinal.mk
        (newActiveBoundary G (S.row.paths i) (S.row.sources i) next) <
      kappa :=
  (mk_newActiveBoundary_le S i next).trans_lt hcard

/-- The exact-frontier certificate of a certified row supplies the
terminal-clean premise needed by source-star continuation. -/
theorem certifiedTerminalClean
    (G : DWeb V) {I : Type u} {rho : I → Cardinal.{u}}
    (S : SingularExtension.CertifiedTargetRowStage G I rho) (i : I) :
    SingularContinuation.TerminalCleanAt G (S.row.paths i) (S.stopover i) :=
  SingularContinuation.terminalCleanAt_of_isWarp_terminalFrontier_eq
    G (S.row.isWarp i) (S.frontier_eq i)

/-- Continue a certified row column through a full-source separating
half-way linkage in its quotient. -/
def certifiedComposedContinuation
    (G : DWeb V) {I : Type u} {rho : I → Cardinal.{u}}
    (S : SingularExtension.CertifiedTargetRowStage G I rho) (i : I)
    {D : Set V} (U : Set (G.quotient (S.stopover i)).DPath)
    (hD : IsSeparatingHalfwayStopover
      (G.quotient (S.stopover i)) U D) : Set G.DPath :=
  SingularHalfwayComposition.composedContinuation G (S.separating i)
    (certifiedTerminalClean G S i) U hD

theorem certifiedComposedContinuation_finiteCharacter
    (G : DWeb V) {I : Type u} {rho : I → Cardinal.{u}}
    (S : SingularExtension.CertifiedTargetRowStage G I rho) (i : I)
    {D : Set V} {U : Set (G.quotient (S.stopover i)).DPath}
    (hD : IsSeparatingHalfwayStopover
      (G.quotient (S.stopover i)) U D) :
    G.HasFiniteCharacter (certifiedComposedContinuation G S i U hD) := by
  exact SingularHalfwayComposition.composedContinuation_finiteCharacter
    G (S.separating i) (certifiedTerminalClean G S i) hD

theorem forwardExtension_certifiedComposedContinuation
    (G : DWeb V) {I : Type u} {rho : I → Cardinal.{u}}
    (S : SingularExtension.CertifiedTargetRowStage G I rho) (i : I)
    {D : Set V} (U : Set (G.quotient (S.stopover i)).DPath)
    (hD : IsSeparatingHalfwayStopover
      (G.quotient (S.stopover i)) U D) :
    G.ForwardExtension (S.row.paths i)
      (certifiedComposedContinuation G S i U hD) := by
  exact SingularHalfwayComposition.forwardExtension_composedContinuation
    G (S.separating i) (certifiedTerminalClean G S i) U hD

/-- Under normalization, a source-faithful target link can be represented by
a component which starts at the selected source and actually terminates in
the target.  This lets links proved relative to two different source sets be
combined without losing the purity clause. -/
theorem exists_completed_of_linksToTarget
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {A : Set V} (hA : A ⊆ G.source)
    (hlinks : LinksToTarget G W A) {a : V} (ha : a ∈ A) :
    ∃ p ∈ W, p.initial = a ∧
      ∃ b ∈ G.target, G.terminal? p = some b := by
  obtain ⟨p, hpW, q, rfl, hpure, before, after, hsupport,
    b, hbTarget, hbAfter⟩ := hlinks a ha
  have haSupport : a ∈ q.support := by
    have haInter : a ∈ q.support ∩ A := by
      rw [hpure]
      exact Set.mem_singleton a
    exact haInter.1
  have hqStart : q.start = a :=
    (hNorm.eq_initial_of_mem_path (.inl q) haSupport (hA ha)).symm
  have hbSupport : b ∈ q.support := by
    change b ∈ q.walk.support
    rw [hsupport]
    exact List.mem_append_right before hbAfter
  have hqTerminal : G.terminal? (.inl q : G.DPath) = some b :=
    hNorm.terminal?_eq_of_mem_path (.inl q) hbSupport hbTarget
  exact ⟨.inl q, hpW, hqStart, b, hbTarget, hqTerminal⟩

/-- Successor bookkeeping with the minimal quotient request.

The quotient linkage is required to link only terminals belonging to the
new sources `next \ old`.  Old links are transported by forward extension;
new links are transported through the active boundary.  The final call to
`linksToTarget_of_completed_sources` re-establishes purity relative to all
of `next` at once. -/
theorem linksToTarget_certifiedComposedContinuation
    (G : DWeb V) (hNorm : G.IsNormalized)
    {I : Type u} {rho : I → Cardinal.{u}}
    (S : SingularExtension.CertifiedTargetRowStage G I rho) (i : I)
    {next : Set V} (holdNext : S.row.sources i ⊆ next)
    (hnext : next ⊆ G.source)
    {D : Set V} {U : Set (G.quotient (S.stopover i)).DPath}
    (hD : IsSeparatingHalfwayStopover
      (G.quotient (S.stopover i)) U D)
    (hUlinks : LinksToTarget (G.quotient (S.stopover i)) U
      (newActiveBoundary G (S.row.paths i) (S.row.sources i) next)) :
    LinksToTarget G (certifiedComposedContinuation G S i U hD) next := by
  let W' : Set G.DPath := certifiedComposedContinuation G S i U hD
  have hfinite : G.HasFiniteCharacter W' :=
    certifiedComposedContinuation_finiteCharacter G S i hD
  have holdSource : S.row.sources i ⊆ G.source := holdNext.trans hnext
  have holdLinks : LinksToTarget G W' (S.row.sources i) := by
    exact SingularExtension.linksToTarget_of_forwardExtension hNorm
      holdSource (S.row.links i)
      (forwardExtension_certifiedComposedContinuation G S i U hD)
      hfinite
  have hnewSource : next \ S.row.sources i ⊆ G.source :=
    Set.sdiff_subset.trans hnext
  have hnewLinks : LinksToTarget G W' (next \ S.row.sources i) := by
    exact SingularContinuation.linksToTarget_continuation_of_activeBoundary
      G hNorm (S.separating i).linkage (S.separating i).separator
      (S.separating i).stopover.minimal (certifiedTerminalClean G S i)
      hnewSource hD (by simpa only [newActiveBoundary] using hUlinks)
  apply SingularContinuation.linksToTarget_of_initial_terminal
    G hNorm hfinite hnext
  intro a haNext
  by_cases haOld : a ∈ S.row.sources i
  · exact exists_completed_of_linksToTarget hNorm holdSource holdLinks haOld
  · exact exists_completed_of_linksToTarget hNorm hnewSource hnewLinks
      ⟨haNext, haOld⟩

end SingularBoundaryActive
end CardinalInduction
end Erdos599
