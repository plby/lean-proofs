/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularHalfwaySplit
import ErdosProblems.Erdos599.RegularEventualCompatibility

/-!
# The persistent/movable split of a regular slice request

A small request on one ladder frontier has two geometrically different
parts.  A non-target point in the limit strict roof can be avoided by a
sufficiently late club frontier.  A point outside the limit strict roof is
persistent and belongs to every sufficiently late frontier; it therefore
cannot occur in a right-tight target-linking row and must be put on the
completed track.

This file makes that dichotomy simultaneous for the whole request and then
applies it to a weak full-source linkage.  The result is exactly a
`CleanTargetSlice`: persistent coordinates are completed, while first-hit
normalization of the complementary row remains target-linking on every
movable requested coordinate.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace CardinalInduction
namespace RegularPersistentRequestSplit

open SliceSpliceSource

universe u

variable {V : Type u}

/-- Requested non-target coordinates which no strict ladder roof captures. -/
def persistentPart {kappa : Cardinal.{u}} (Gamma : DWeb V)
    (L : Gamma.KappaLadder kappa) (U : Set V) : Set V :=
  (U \ Gamma.target) \ L.limitStrictRoof

/-- The complementary request, which can be made right-boundary clean. -/
def movablePart {kappa : Cardinal.{u}} (Gamma : DWeb V)
    (L : Gamma.KappaLadder kappa) (U : Set V) : Set V :=
  U \ persistentPart Gamma L U

theorem persistentPart_subset_request
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (U : Set V) :
    persistentPart Gamma L U ⊆ U := by
  exact Set.sdiff_subset.trans Set.sdiff_subset

theorem movablePart_subset_request
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (U : Set V) :
    movablePart Gamma L U ⊆ U :=
  Set.sdiff_subset

theorem persistent_union_movable
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (U : Set V) :
    persistentPart Gamma L U ∪ movablePart Gamma L U = U := by
  exact Set.union_sdiff_cancel (persistentPart_subset_request L U)

theorem disjoint_persistent_movable
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (U : Set V) :
    Disjoint (persistentPart Gamma L U) (movablePart Gamma L U) := by
  exact Set.disjoint_sdiff_right

theorem persistentPart_subset_limitPersistent
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) {delta : Ladder.Stage kappa}
    {U : Set V} (hU : U ⊆ L.frontier delta) :
    persistentPart Gamma L U ⊆ L.limitRoof \ L.limitStrictRoof := by
  rintro x ⟨⟨hxU, _hxTarget⟩, hxStrict⟩
  refine ⟨?_, hxStrict⟩
  apply Set.mem_iUnion.2
  exact ⟨delta, Gamma.subset_roof (L.frontier delta) (hU hxU)⟩

theorem movablePart_nonTarget_subset_limitStrictRoof
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (U : Set V) :
    movablePart Gamma L U \ Gamma.target ⊆ L.limitStrictRoof := by
  rintro x ⟨⟨hxU, hxNotPersistent⟩, hxNotTarget⟩
  by_contra hxNotStrict
  exact hxNotPersistent ⟨⟨hxU, hxNotTarget⟩, hxNotStrict⟩

/-- Simultaneous club selection for an arbitrary small request.  Persistent
coordinates occur on the selected right boundary, while every movable
non-target coordinate avoids it. -/
theorem exists_later_club_persistent_movable_split
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : L.IsSplitLegal)
    {Sigma : Set (Ladder.Stage kappa)}
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    {delta : Ladder.Stage kappa} {U : Set V}
    (hU : U ⊆ L.frontier delta) (hUsmall : #U < kappa) :
    ∃ beta ∈ Sigma, delta < beta ∧
      persistentPart Gamma L U ⊆ L.frontier beta \ Gamma.target ∧
      Disjoint (movablePart Gamma L U \ Gamma.target)
        (L.frontier beta) := by
  have hPersistentSmall : #(persistentPart Gamma L U) < kappa :=
    (Cardinal.mk_subtype_mono
      (persistentPart_subset_request L U)).trans_lt hUsmall
  obtain ⟨beta₀, hbeta₀, hdeltaBeta₀, hPersistentEventually⟩ :=
    RegularBetaSelection.exists_later_club_eventually_contains_of_small_persistent
      hL hSigma (persistentPart_subset_limitPersistent L hU)
        hPersistentSmall delta
  have hMovableSmall : #(movablePart Gamma L U) < kappa :=
    (Cardinal.mk_subtype_mono
      (movablePart_subset_request L U)).trans_lt hUsmall
  obtain ⟨beta, hbeta, hbeta₀Beta, hMovableAvoid⟩ :=
    RegularBetaSelection.exists_later_club_disjoint_nonTarget_frontier
      hL hSigma (movablePart_nonTarget_subset_limitStrictRoof L U)
        hMovableSmall beta₀
  refine ⟨beta, hbeta, hdeltaBeta₀.trans hbeta₀Beta, ?_,
    hMovableAvoid⟩
  intro x hx
  exact ⟨hPersistentEventually beta hbeta₀Beta.le hx, hx.1.2⟩

/-- A weak full-source target-linking row at each late club frontier yields
a completed/pending row at one compatible frontier.  The persistent request
is placed on the target track.  First-hit normalization of the complementary
row is terminal-clean and still links the entire movable request.

This is the local provider datum consumed before the history-sensitive
suffix-shadow check: no completed path is incorrectly required to be tight
at a frontier containing its non-target initial vertex. -/
theorem exists_later_cleanTargetSlice
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : L.IsSplitLegal)
    {Sigma : Set (Ladder.Stage kappa)}
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    {Q : DWeb V} (hNorm : Q.IsNormalized)
    (hTarget : Q.target = Gamma.target)
    {delta : Ladder.Stage kappa} {U : Set V}
    (hUfrontier : U ⊆ L.frontier delta)
    (hUsource : U ⊆ Q.source) (hUsmall : #U < kappa)
    (hweak : ∀ beta ∈ Sigma, delta < beta →
      ∃ W : Set Q.DPath,
        IsLinkageBetween Q Q.source (L.frontier beta) W ∧
          LinksToTarget Q W U) :
    ∃ beta ∈ Sigma, delta < beta ∧
      ∃ W : Set Q.DPath,
        IsLinkageBetween Q Q.source (L.frontier beta) W ∧
          LinksToTarget Q W U ∧
          ∃ S : RegularCompletedPendingSplice.CleanTargetSlice Q Q.source
              (L.frontier beta) (persistentPart Gamma L U),
            LinksToTarget Q S.clean (movablePart Gamma L U) ∧
              #S.target < kappa ∧
              S.target ⊆ SingularExtension.completedPart Q W ∧
              persistentPart Gamma L U ⊆
                L.frontier beta \ Gamma.target ∧
              Disjoint (movablePart Gamma L U \ Gamma.target)
                (L.frontier beta) := by
  obtain ⟨beta, hbeta, hdeltaBeta, hPersistent, hMovableAvoid⟩ :=
    exists_later_club_persistent_movable_split hL hSigma
      hUfrontier hUsmall
  let W : Set Q.DPath := Classical.choose (hweak beta hbeta hdeltaBeta)
  have hW : IsLinkageBetween Q Q.source (L.frontier beta) W :=
    (Classical.choose_spec (hweak beta hbeta hdeltaBeta)).1
  have hWlinks : LinksToTarget Q W U :=
    (Classical.choose_spec (hweak beta hbeta hdeltaBeta)).2
  have hPersistentSource : persistentPart Gamma L U ⊆ Q.source :=
    (persistentPart_subset_request L U).trans hUsource
  have hPersistentLinks : LinksToTarget Q W
      (persistentPart Gamma L U) :=
    ControlledSlices.linksToTarget_mono Q W
      (persistentPart_subset_request L U) hWlinks
  obtain ⟨S, hStarget, hSclean, hStargetCard, hStargetCompleted⟩ :=
    RegularHalfwaySplit.exists_cleanTargetSlice_of_halfway hNorm hW
      hPersistentSource hPersistentLinks
  let P := initialRestriction Q W
    (Q.source \ persistentPart Gamma L U)
  have hP : IsLinkageBetween Q
      (Q.source \ persistentPart Gamma L U) (L.frontier beta) P :=
    isLinkageBetween_initialRestriction hW Set.sdiff_subset
  have hMovableSource : movablePart Gamma L U ⊆ Q.source :=
    (movablePart_subset_request L U).trans hUsource
  have hMovableSub : movablePart Gamma L U ⊆
      Q.source \ persistentPart Gamma L U := by
    intro x hx
    exact ⟨hMovableSource hx, hx.2⟩
  have hMovableLinksW : LinksToTarget Q W (movablePart Gamma L U) :=
    ControlledSlices.linksToTarget_mono Q W
      (movablePart_subset_request L U) hWlinks
  have hMovableLinksP : LinksToTarget Q P (movablePart Gamma L U) := by
    apply SliceSegmentCore.linksToTarget_mono_family (W :=
      initialRestriction Q W (movablePart Gamma L U))
    · intro p hp
      exact ⟨hp.1, hMovableSub hp.2⟩
    · exact RegularHalfwaySplit.linksToTarget_initialRestriction hW
        hMovableSource hMovableLinksW
  have hMovableAvoidQ : Disjoint
      (movablePart Gamma L U \ Q.target) (L.frontier beta) := by
    simpa only [hTarget] using hMovableAvoid
  have hCleanLinks : LinksToTarget Q
      (RegularBetaSelection.targetFirstHitFamily hP)
      (movablePart Gamma L U) :=
    RegularBetaSelection.targetFirstHitFamily_linksToTarget_of_subsource
      hNorm hP hMovableSub hMovableLinksP hMovableAvoidQ
  refine ⟨beta, hbeta, hdeltaBeta, W, hW, hWlinks, S, ?_, ?_, ?_, hPersistent,
    hMovableAvoid⟩
  · rw [hSclean]
    exact hCleanLinks
  · exact hStargetCard.trans_lt hPersistentSmall
  · exact hStargetCompleted
where
  hPersistentSmall : #(persistentPart Gamma L U) < kappa :=
    (Cardinal.mk_subtype_mono
      (persistentPart_subset_request L U)).trans_lt hUsmall

/-- Glue from the persistent/movable local split to the exact successor
predicate used by the recursive completed/pending splice.  The full later
warp carries shadow components for old completed paths; the used restriction
is the union of the newly completed persistent track and the clean movable
track. -/
theorem cleanTargetStep_of_persistentSplit_suffixShadow
    (G : DWeb V) {left right U : Set V}
    (S : RegularCompletedPendingSplice.CleanTargetSlice G left right U)
    {old Tfull : Set G.DPath} {C D : Set V}
    (hOld : G.IsWarp old) (hTfull : G.IsWarp Tfull)
    (hTavoid : G.vertexSet Tfull ⊆ (G.strictRoof C)ᶜ)
    (hshadow : ∀ f ∈ SingularExtension.completedPart G old,
      ∃ t ∈ Tfull,
        t.initial ∉ D ∧ f.support \ G.strictRoof C ⊆ t.support)
    (_hused : S.target ∪ S.clean = initialRestriction G Tfull D)
    (hcompat : G.StarCompatible (SingularExtension.pendingPart G old)
      (initialRestriction G Tfull D)) :
    RegularCompletedPendingSplice.IsCleanTargetStep G old
      (initialRestriction G Tfull D) hcompat := by
  exact RegularEventualCompatibility.cleanTargetStep_of_suffixShadow
    G hOld hTfull hTavoid hshadow hcompat

/-- The provider-facing version in which the later comparison warp retains
every already-completed path literally.  The retained path is its own
suffix shadow; disjointness from the used subfamily is the only extra fact
needed to keep the newly used slice away from the completed carrier.

This formulation is particularly convenient for an iterative provider:
`Tfull` is the whole comparison row (old completed paths plus a fresh
pending fill), while `Tused` is only the fresh fill installed at this step. -/
theorem cleanTargetStep_of_retainedCompleted
    (G : DWeb V) {old Tfull Tused : Set G.DPath} {C : Set V}
    (hOld : G.IsWarp old) (hTfull : G.IsWarp Tfull)
    (hused : Tused ⊆ Tfull)
    (husedAvoid : G.vertexSet Tused ⊆ (G.strictRoof C)ᶜ)
    (hretained : SingularExtension.completedPart G old ⊆ Tfull)
    (hunused : Disjoint (SingularExtension.completedPart G old) Tused)
    (hcompat : G.StarCompatible (SingularExtension.pendingPart G old)
      Tused) :
    RegularCompletedPendingSplice.IsCleanTargetStep G old Tused hcompat := by
  apply RegularEventualCompatibility.cleanTargetStep_of_used_suffixShadow
    G hOld hTfull hused husedAvoid
  · intro f hf
    refine ⟨f, hretained hf, ?_, Set.sdiff_subset⟩
    intro hfUsed
    exact Set.disjoint_left.1 hunused hf hfUsed

/-- More flexible provider-facing form: the full comparison row need only
be a forward extension of the old row.  For every old completed path choose
its extending comparison component.  A used component starts at an old
pending coordinate, so it cannot be that chosen component: otherwise the
completed and pending old paths would have the same initial vertex, contrary
to the old warp's disjointness.

Thus a full forward comparison row automatically supplies all suffix shadows
required by `cleanTargetStep_of_used_suffixShadow`; it need not contain old
completed paths literally. -/
theorem cleanTargetStep_of_forwardComparison
    (G : DWeb V) {old Tfull Tused : Set G.DPath} {C : Set V}
    (hOld : G.IsWarp old) (hTfull : G.IsWarp Tfull)
    (hforward : G.ForwardExtension old Tfull)
    (hused : Tused ⊆ Tfull)
    (husedAvoid : G.vertexSet Tused ⊆ (G.strictRoof C)ᶜ)
    (husedInitial : G.initialSet Tused ⊆
      G.initialSet (SingularExtension.pendingPart G old))
    (hcompat : G.StarCompatible (SingularExtension.pendingPart G old)
      Tused) :
    RegularCompletedPendingSplice.IsCleanTargetStep G old Tused hcompat := by
  apply RegularEventualCompatibility.cleanTargetStep_of_used_suffixShadow
    G hOld hTfull hused husedAvoid
  intro f hf
  obtain ⟨t, htFull, hft⟩ := hforward.1 f hf.1
  refine ⟨t, htFull, ?_, Set.sdiff_subset.trans
    (G.support_mono_of_extends hft)⟩
  intro htUsed
  obtain ⟨p, hpPending, hpInitial⟩ :=
    husedInitial ⟨t, htUsed, rfl⟩
  have hfp : f ≠ p := by
    intro hfp
    subst p
    exact Set.disjoint_left.1
      (SingularExtension.disjoint_completedPart_pendingPart G old)
      hf hpPending
  have hdis : Disjoint f.support p.support :=
    hOld hf.1 hpPending.1 hfp
  have hinitial : f.initial = p.initial :=
    (G.extends_initial hft).trans hpInitial.symm
  have hfInitialMem : f.initial ∈ p.support := by
    rw [hinitial]
    exact p.initial_mem_support
  exact Set.disjoint_left.1 hdis f.initial_mem_support hfInitialMem

/-- Direct glue from a persistent/movable `CleanTargetSlice` to the exact
completed/pending successor predicate.  The equality records that the used
subfamily is precisely the completed persistent track together with the
first-hit-clean movable track; compatibility itself follows from retaining
all old completed paths in the full comparison row. -/
theorem cleanTargetStep_of_persistentSplit_retainedCompleted
    (G : DWeb V) {left right U : Set V}
    (S : RegularCompletedPendingSplice.CleanTargetSlice G left right U)
    {old Tfull Tused : Set G.DPath} {C : Set V}
    (hOld : G.IsWarp old) (hTfull : G.IsWarp Tfull)
    (hused : Tused ⊆ Tfull)
    (husedAvoid : G.vertexSet Tused ⊆ (G.strictRoof C)ᶜ)
    (hretained : SingularExtension.completedPart G old ⊆ Tfull)
    (hunused : Disjoint (SingularExtension.completedPart G old) Tused)
    (_husedEq : S.target ∪ S.clean = Tused)
    (hcompat : G.StarCompatible (SingularExtension.pendingPart G old)
      Tused) :
    RegularCompletedPendingSplice.IsCleanTargetStep G old Tused hcompat := by
  exact cleanTargetStep_of_retainedCompleted G hOld hTfull hused
    husedAvoid hretained hunused hcompat

end RegularPersistentRequestSplit
end CardinalInduction
end Erdos599
