/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularPersistentRequestSplit
import ErdosProblems.Erdos599.LadderSliceGeometry
import ErdosProblems.Erdos599.HalfwayFrontierHeight

/-!
# Causal coordinates for weak split annular candidates

The persistent part of a request cannot be put on the right-tight clean
row.  Nor can a requested non-target source which already belongs to the
half-way stop-over: first-hit trimming would make its component trivial and
destroy its target link.  A causal table entry therefore chooses three
families: a small selected target track containing the persistent part, a
right-tight clean track for the unselected request, and a weak full
comparison row.

Only data visible at the two table stages occurs in the candidate
predicate.  In particular, the local persistent set is the requested
non-target overlap with the chosen right frontier.  The later-club
selection theorem identifies this set with the global persistent part at
the coordinate eventually used by the provider.

The causal row registers every vertex of the small target track and every
vertex of a clean-track maverick.  Ordinary clean paths need no separate
registration: their vertices are handled by limit-warp closure.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularWeakSplitCandidate

open SingularExtension SliceSpliceSource

universe u

variable {V : Type u}

/-- The part of `U` which is visibly persistent at this table coordinate. -/
def stagePersistent (G : DWeb V) (right U : Set V) : Set V :=
  (U \ G.target) ∩ right

/-- The complementary, movable part of the request. -/
def stageMovable (G : DWeb V) (right U : Set V) : Set V :=
  U \ stagePersistent G right U

theorem stagePersistent_subset_request (G : DWeb V) (right U : Set V) :
    stagePersistent G right U ⊆ U :=
  Set.inter_subset_left.trans Set.sdiff_subset

theorem stagePersistent_union_stageMovable
    (G : DWeb V) (right U : Set V) :
    stagePersistent G right U ∪ stageMovable G right U = U :=
  Set.union_sdiff_cancel (stagePersistent_subset_request G right U)

theorem disjoint_stagePersistent_stageMovable
    (G : DWeb V) (right U : Set V) :
    Disjoint (stagePersistent G right U) (stageMovable G right U) :=
  Set.disjoint_sdiff_right

/-- At a frontier selected by the global persistent/movable club lemma, the
prefix-stable stage-local split is exactly the global split. -/
theorem stageSplit_eq_persistentSplit
    {kappa : Cardinal.{u}} (G : DWeb V) (L : G.KappaLadder kappa)
    {right U : Set V}
    (hPersistent : RegularPersistentRequestSplit.persistentPart G L U ⊆
      right \ G.target)
    (hMovableAvoid : Disjoint
      (RegularPersistentRequestSplit.movablePart G L U \ G.target) right) :
    stagePersistent G right U =
        RegularPersistentRequestSplit.persistentPart G L U ∧
      stageMovable G right U =
        RegularPersistentRequestSplit.movablePart G L U := by
  have hpersistent : stagePersistent G right U =
      RegularPersistentRequestSplit.persistentPart G L U := by
    apply Set.Subset.antisymm
    · rintro x ⟨⟨hxU, hxNotTarget⟩, hxRight⟩
      have hxSplit : x ∈
          RegularPersistentRequestSplit.persistentPart G L U ∪
            RegularPersistentRequestSplit.movablePart G L U := by
        rw [RegularPersistentRequestSplit.persistent_union_movable]
        exact hxU
      rcases hxSplit with hxPersistent | hxMovable
      · exact hxPersistent
      · exfalso
        exact Set.disjoint_left.1 hMovableAvoid
          ⟨hxMovable, hxNotTarget⟩ hxRight
    · intro x hxPersistent
      exact ⟨
        ⟨RegularPersistentRequestSplit.persistentPart_subset_request L U
            hxPersistent,
          (hPersistent hxPersistent).2⟩,
        (hPersistent hxPersistent).1⟩
  refine ⟨hpersistent, ?_⟩
  unfold stageMovable RegularPersistentRequestSplit.movablePart
  rw [hpersistent]

/-- The path-family value stored in a causal table.  Its type is independent
of the ladder, which makes equality of choices under prefix agreement an
ordinary congruence argument. -/
structure WeakSplitFamilies (G : DWeb V) where
  target : Set G.DPath
  clean : Set G.DPath
  comparison : Set G.DPath

/-- A weak annular comparison together with its selected-target and
complementary-clean installed tracks.  The selected set contains every
persistent non-target coordinate; it may also contain additional sources
completed by the protected half-way construction.  The comparison is
intentionally not right-tight.  Only `clean` has a
right-boundary terminal-purity condition, through `CleanTargetSlice`.

The cardinal clauses are precisely those needed by the causal
registration: the full target carrier is small, and all nonordinary clean
components are small. -/
def IsWeakSplitAnnularCandidate
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (delta beta gamma : Ladder.Stage kappa)
    (P : WeakSplitFamilies G) : Prop :=
  let U := request delta gamma
  let persistent := stagePersistent G (L.frontier beta) U
  ∃ selected : Set V,
    persistent ⊆ selected ∧
    ∃ S : RegularCompletedPendingSplice.CleanTargetSlice G
        (L.frontier delta) (L.frontier beta) selected,
      S.target = P.target ∧
        S.clean = P.clean ∧
        SliceSplice.IsAnnularSlice G L P.comparison delta beta
          (U \ selected) ∧
        P.clean ⊆ P.comparison ∧
        G.vertexSet P.target ⊆ G.roof (L.frontier beta) ∧
        #P.target < kappa ∧
        LinksToTarget G P.clean (U \ selected) ∧
        SliceCandidate.HasStageIntervalSegments G L P.clean delta beta ∧
        #(ControlledSlices.sliceMavericks G (L.warpAt beta) P.clean) < kappa

/-- The split predicate depends only on the two visible ladder coordinates
and the current request.  This is the causality lemma used when a choice
made in a truncated ladder is transported to the final ladder. -/
theorem isWeakSplitAnnularCandidate_congr_stageData
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L L' : G.KappaLadder kappa}
    {request request' : Ladder.Stage kappa → Ladder.Stage kappa → Set V}
    {delta beta gamma : Ladder.Stage kappa} {P : WeakSplitFamilies G}
    (hwarpDelta : L.warpAt delta = L'.warpAt delta)
    (hwarpBeta : L.warpAt beta = L'.warpAt beta)
    (hfrontierDelta : L.frontier delta = L'.frontier delta)
    (hfrontierBeta : L.frontier beta = L'.frontier beta)
    (hrequest : request delta gamma = request' delta gamma) :
    IsWeakSplitAnnularCandidate G L request delta beta gamma P ↔
      IsWeakSplitAnnularCandidate G L' request' delta beta gamma P := by
  unfold IsWeakSplitAnnularCandidate
  simp only [stagePersistent,
    SliceSplice.IsAnnularSlice, ControlledSlices.SliceGood,
    DWeb.KappaLadder.lowerRegion, DWeb.KappaLadder.upperRegion,
    SliceCandidate.HasStageIntervalSegments, SliceCandidate.IsStageInterval]
  rw [hrequest, hfrontierDelta, hfrontierBeta, hwarpDelta, hwarpBeta]

/-- The set from which the causal coordinate makes its canonical choice. -/
def weakSplitCandidateFamilies
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (delta beta gamma : Ladder.Stage kappa) : Set (WeakSplitFamilies G) :=
  {P | IsWeakSplitAnnularCandidate G L request delta beta gamma P}

/-- Canonical causal choice, empty in every component when the coordinate
has no split candidate. -/
noncomputable def chosenWeakSplitCandidate
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (delta beta gamma : Ladder.Stage kappa) : WeakSplitFamilies G := by
  classical
  exact if h : (weakSplitCandidateFamilies G L request
      delta beta gamma).Nonempty then
    Classical.choose h
  else
    ⟨∅, ∅, ∅⟩

theorem chosenWeakSplitCandidate_spec_of_exists
    {kappa : Cardinal.{u}} {G : DWeb V}
    (L : G.KappaLadder kappa)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    {delta beta gamma : Ladder.Stage kappa}
    (h : ∃ P, IsWeakSplitAnnularCandidate G L request
      delta beta gamma P) :
    IsWeakSplitAnnularCandidate G L request delta beta gamma
      (chosenWeakSplitCandidate G L request delta beta gamma) := by
  classical
  change (weakSplitCandidateFamilies G L request
    delta beta gamma).Nonempty at h
  rw [chosenWeakSplitCandidate, dif_pos h]
  exact Classical.choose_spec h

/-- The canonical split choice itself is invariant under agreement of the
two visible stage coordinates. -/
theorem chosenWeakSplitCandidate_congr_stageData
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L L' : G.KappaLadder kappa}
    {request request' : Ladder.Stage kappa → Ladder.Stage kappa → Set V}
    {delta beta gamma : Ladder.Stage kappa}
    (hwarpDelta : L.warpAt delta = L'.warpAt delta)
    (hwarpBeta : L.warpAt beta = L'.warpAt beta)
    (hfrontierDelta : L.frontier delta = L'.frontier delta)
    (hfrontierBeta : L.frontier beta = L'.frontier beta)
    (hrequest : request delta gamma = request' delta gamma) :
    chosenWeakSplitCandidate G L request delta beta gamma =
      chosenWeakSplitCandidate G L' request' delta beta gamma := by
  have hfamilies :
      weakSplitCandidateFamilies G L request delta beta gamma =
        weakSplitCandidateFamilies G L' request' delta beta gamma := by
    ext P
    exact isWeakSplitAnnularCandidate_congr_stageData hwarpDelta hwarpBeta
      hfrontierDelta hfrontierBeta hrequest
  unfold chosenWeakSplitCandidate
  rw [hfamilies]

/-- The exact bounded vertex set owned by one weak split coordinate. -/
def registeredVerticesAt
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (delta beta gamma : Ladder.Stage kappa) : Set V :=
  let P := chosenWeakSplitCandidate G L request delta beta gamma
  G.vertexSet P.target ∪
    G.vertexSet
      (ControlledSlices.sliceMavericks G (L.warpAt beta) P.clean)

/-- The registered coordinate inherits the same causal prefix congruence. -/
theorem registeredVerticesAt_congr_stageData
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L L' : G.KappaLadder kappa}
    {request request' : Ladder.Stage kappa → Ladder.Stage kappa → Set V}
    {delta beta gamma : Ladder.Stage kappa}
    (hwarpDelta : L.warpAt delta = L'.warpAt delta)
    (hwarpBeta : L.warpAt beta = L'.warpAt beta)
    (hfrontierDelta : L.frontier delta = L'.frontier delta)
    (hfrontierBeta : L.frontier beta = L'.frontier beta)
    (hrequest : request delta gamma = request' delta gamma) :
    registeredVerticesAt G L request delta beta gamma =
      registeredVerticesAt G L' request' delta beta gamma := by
  unfold registeredVerticesAt
  rw [hwarpBeta,
    chosenWeakSplitCandidate_congr_stageData hwarpDelta hwarpBeta
      hfrontierDelta hfrontierBeta hrequest]

theorem chosen_target_vertices_subset_registered
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (delta beta gamma : Ladder.Stage kappa) :
    G.vertexSet
        (chosenWeakSplitCandidate G L request delta beta gamma).target ⊆
      registeredVerticesAt G L request delta beta gamma :=
  Set.subset_union_left

theorem chosen_cleanMaverick_vertices_subset_registered
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (delta beta gamma : Ladder.Stage kappa) :
    G.vertexSet (ControlledSlices.sliceMavericks G (L.warpAt beta)
        (chosenWeakSplitCandidate G L request delta beta gamma).clean) ⊆
      registeredVerticesAt G L request delta beta gamma :=
  Set.subset_union_right

/-- Once the coordinate registration is closed, every chosen clean path
whose initial vertex is closed is wholly closed.  Mavericks are registered
directly; an ordinary path embeds through its stage-warp carrier into the
limit warp. -/
theorem chosen_clean_support_subset_of_initial_mem
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} (hL : L.SliceGeometry)
    {Z : Set V}
    (hclosed : SliceSplice.IsLimitWarpClosed G L Z)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (delta beta gamma : Ladder.Stage kappa)
    (hregistered : registeredVerticesAt G L request
      delta beta gamma ⊆ Z)
    {p : G.DPath}
    (hpClean : p ∈
      (chosenWeakSplitCandidate G L request delta beta gamma).clean)
    (hpInitial : p.initial ∈ Z) :
    p.support ⊆ Z := by
  by_cases hpOrdinary :
      ControlledSlices.IsLadderFragment G (L.warpAt beta) p
  · obtain ⟨q, hqStage, hpq⟩ := hpOrdinary
    obtain ⟨r, hrLimit, hqr⟩ :=
      ControlledSlices.stagesEmbedInLimit_of_limitStages G L
        hL.regular hL.limitStages beta q hqStage
    have hrMeets : (r.support ∩ Z).Nonempty := by
      exact ⟨p.initial, hqr.1 (hpq.1 p.initial_mem_support), hpInitial⟩
    exact hpq.1.trans (hqr.1.trans (hclosed r hrLimit hrMeets))
  · intro x hxp
    apply hregistered
    apply chosen_cleanMaverick_vertices_subset_registered
      G L request delta beta gamma
    exact ⟨p, ⟨hpClean, hpOrdinary⟩, hxp⟩

/-- The full installed target/clean carrier is closed once the clean
initial set is closed.  This is the provider-facing closure rule for a
restricted pending-boundary slice. -/
theorem chosen_installed_vertices_subset
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} (hL : L.SliceGeometry)
    {Z : Set V}
    (hclosed : SliceSplice.IsLimitWarpClosed G L Z)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (delta beta gamma : Ladder.Stage kappa)
    (hregistered : registeredVerticesAt G L request
      delta beta gamma ⊆ Z)
    (hcleanInitial : G.initialSet
      (chosenWeakSplitCandidate G L request delta beta gamma).clean ⊆ Z) :
    G.vertexSet
        ((chosenWeakSplitCandidate G L request delta beta gamma).target ∪
          (chosenWeakSplitCandidate G L request delta beta gamma).clean) ⊆
      Z := by
  rintro x ⟨p, hpTarget | hpClean, hxp⟩
  · apply hregistered
    apply chosen_target_vertices_subset_registered
      G L request delta beta gamma
    exact ⟨p, hpTarget, hxp⟩
  · apply chosen_clean_support_subset_of_initial_mem hL hclosed request
      delta beta gamma hregistered hpClean
    · apply hcleanInitial
      exact ⟨p, hpClean, rfl⟩
    · exact hxp

/-- One coordinate uses at most `kappa` registered vertices. -/
theorem mk_registeredVerticesAt_le
    {kappa : Cardinal.{u}} (hkappa : aleph0 ≤ kappa) (G : DWeb V)
    (L : G.KappaLadder kappa)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (delta beta gamma : Ladder.Stage kappa) :
    #(registeredVerticesAt G L request delta beta gamma) ≤ kappa := by
  classical
  by_cases hcandidate : ∃ P,
      IsWeakSplitAnnularCandidate G L request delta beta gamma P
  · have hchosen :=
      chosenWeakSplitCandidate_spec_of_exists L request hcandidate
    rcases hchosen with
      ⟨_selected, _hpersistent, S, htarget, hclean,
        _hcomparison, _hcleanInstalled, _htargetRoof,
        htargetSmall, _hlinks, _hintervals, hmavericksSmall⟩
    have htargetVertices :
        #(G.vertexSet
          (chosenWeakSplitCandidate G L request delta beta gamma).target) ≤
            kappa :=
      HalfwayFrontierHeight.mk_vertexSet_le_of_mk_family_le hkappa _
        htargetSmall.le
    have hmaverickVertices :
        #(G.vertexSet (ControlledSlices.sliceMavericks G (L.warpAt beta)
          (chosenWeakSplitCandidate G L request delta beta gamma).clean)) ≤
            kappa :=
      HalfwayFrontierHeight.mk_vertexSet_le_of_mk_family_le hkappa _
        hmavericksSmall.le
    exact (Cardinal.mk_union_le _ _).trans
      (Cardinal.add_le_of_le hkappa htargetVertices hmaverickVertices)
  · have hempty : chosenWeakSplitCandidate G L request delta beta gamma =
        (⟨∅, ∅, ∅⟩ : WeakSplitFamilies G) := by
      rw [chosenWeakSplitCandidate, dif_neg]
      intro hnonempty
      apply hcandidate
      exact hnonempty
    have htargetEmpty :
        (chosenWeakSplitCandidate G L request delta beta gamma).target = ∅ := by
      rw [hempty]
    have hcleanEmpty :
        (chosenWeakSplitCandidate G L request delta beta gamma).clean = ∅ := by
      rw [hempty]
    have hregisteredEmpty :
        registeredVerticesAt G L request delta beta gamma = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      change x ∈
        G.vertexSet
            (chosenWeakSplitCandidate G L request delta beta gamma).target ∪
          G.vertexSet (ControlledSlices.sliceMavericks G (L.warpAt beta)
            (chosenWeakSplitCandidate G L request delta beta gamma).clean) at hx
      rcases hx with hxTarget | hxClean
      · obtain ⟨p, hp, _hxp⟩ := hxTarget
        rw [htargetEmpty] at hp
        exact hp
      · obtain ⟨p, hp, _hxp⟩ := hxClean
        have hpClean := hp.1
        rw [hcleanEmpty] at hpClean
        exact hpClean
    rw [hregisteredEmpty]
    rw [Cardinal.mk_emptyCollection]
    exact bot_le

end RegularWeakSplitCandidate
end CardinalInduction
end Erdos599
