/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredHalfwayGeometry
import ErdosProblems.Erdos599.LadderLimitHitClosure

/-!
# Limit-hit closure for deferred ladders

This file packages the corrected form of source Lemma 7.28 for the
deferred current-marker bookkeeping.  Deferred legality supplies the
global ladder laws used by the closure argument.  The genuinely path-local
limit input remains explicit: when a limiting component misses the
frontier at a directed supremum of earlier hits, it belongs to the
inessential part at that supremum.

Keeping this premise visible is important.  It is not a consequence of
bookkeeping validity alone; it comes from the direct-limit geometry of the
particular family to which the lemma is applied.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

/-- Every limiting ladder component has a directed-supremum-closed set of
hits on `Sigma`.  This is the downstream form of source Lemma 7.28. -/
def LimitHitClosure (G : DWeb V) (L : G.KappaLadder kappa)
    (Sigma : Set (Ladder.Stage kappa)) : Prop :=
  ∀ p ∈ L.limitWarp, DirSupClosed (L.hitStages Sigma p)

/-- The path-local direct-limit premise in the corrected Lemma 7.28. -/
def LimitMissesAreInessential (G : DWeb V) (L : G.KappaLadder kappa)
    (Sigma : Set (Ladder.Stage kappa)) : Prop :=
  ∀ p ∈ L.limitWarp, L.LimitMissIsInessential Sigma p

/-- The current marker has not yet entered the accumulated warp.  The
canonical deferred ladder has this property by its marker construction;
it is stated separately because it is geometry, not bookkeeping validity. -/
def MarkersOutsideCurrentWarp (G : DWeb V)
    (L : G.KappaLadder kappa) : Prop :=
  ∀ (a : Ladder.Stage kappa) (y : V),
    L.marker a = some y → y ∉ G.vertexSet (L.warpAt a)

/-- An inessential component of an ordinary stage of the canonical
deferred ladder occurs literally in its final warp.  Deferred bookkeeping
does not change the accumulated families, so this is the canonical
inessential-persistence theorem evaluated at the final extended stage. -/
theorem canonicalDeferredLadder_mem_limitWarp_of_mem_inessential
    (preferred : Ladder.Stage kappa → Option V)
    (hNoEnter : G.NoEdgeEnters G.source)
    {a : Ladder.Stage kappa} {p : G.DPath}
    (hp : p ∈ G.inessentialPaths
      ((canonicalDeferredLadder G kappa preferred).warpAt a)) :
    p ∈ (canonicalDeferredLadder G kappa preferred).limitWarp := by
  have hpFinal : p ∈ G.inessentialPaths
      (G.canonicalLadderAccumulated kappa preferred
        (Ladder.finalStage kappa)) := by
    exact canonicalAccumulated_inessential_mono preferred hNoEnter
      (a := Ladder.Stage.toExtended a)
      (b := Ladder.finalStage kappa) a.2.le hp
  exact hpFinal.1

/-- Strict roofs of deferred ladder frontiers increase with the stage. -/
theorem HalfwayGeometry.strictRoof_frontier_mono
    {L : G.KappaLadder kappa} (hL : HalfwayGeometry L)
    {a b : Ladder.Stage kappa} (hab : a ≤ b) :
    G.strictRoof (L.frontier a) ⊆ G.strictRoof (L.frontier b) := by
  rcases hab.lt_or_eq with hab | rfl
  · intro x hx
    constructor
    · exact G.roof_cut (hL.frontierChronology hab) hx.1
    · intro hxEssential
      have hxFrontier : x ∈ L.frontier b := by
        rw [← hL.frontiersEssential b]
        exact hxEssential
      exact Set.disjoint_left.1 (hL.strictFrontierChronology hab)
        hx hxFrontier
  · exact fun _ hx ↦ hx

/-- Inessential components persist between ordinary stages of every
deferred-legal ladder.  The proof uses only the geometric and persistence
fields shared with the source ladder construction. -/
theorem HalfwayGeometry.inessentialPaths_mono_stage
    {L : G.KappaLadder kappa} (hL : HalfwayGeometry L)
    {a b : Ladder.Stage kappa} (hab : a ≤ b) :
    G.inessentialPaths (L.warpAt a) ⊆
      G.inessentialPaths (L.warpAt b) := by
  let accumulatedAt (o : Ordinal.{u}) (ho : o < kappa.ord) :=
    L.accumulated (⟨o, ho.le⟩ : Ladder.ExtendedStage kappa)
  have hmain : ∀ o : Ordinal.{u}, ∀ ho : o < kappa.ord,
      ∀ c : Ordinal.{u}, c ≤ o → ∀ hc : c < kappa.ord,
        G.inessentialPaths (accumulatedAt c hc) ⊆
          G.inessentialPaths (accumulatedAt o ho) := by
    intro o
    induction o using Ordinal.limitRecOn with
    | zero =>
        intro ho c hc hcKappa
        have hc0 : c = 0 := le_antisymm hc bot_le
        subst c
        exact Set.Subset.rfl
    | add_one o ih =>
        intro ho c hc hcKappa p hp
        rcases hc.lt_or_eq with hc | rfl
        · have hco : c ≤ o := (Order.lt_add_one_iff).1 hc
          have hoKappa : o < kappa.ord :=
            (show o < o + 1 by
              rw [← Order.succ_eq_add_one]
              exact Order.lt_succ o).trans ho
          have hpO := ih hoKappa c hco hcKappa hp
          let os : Ladder.Stage kappa := ⟨o, hoKappa⟩
          exact hL.currentInessentialPersists os hpO
        · exact hp
    | limit o hoLimit ih =>
        intro hoKappa c hc hcKappa p hp
        rcases hc.lt_or_eq with hc | rfl
        · let oe : Ladder.ExtendedStage kappa := ⟨o, hoKappa.le⟩
          obtain ⟨C, hstage, hlimit⟩ := hL.limitStages oe hoLimit
          let : Nonempty (Set.Iio o) := hoLimit.nonempty_Iio.to_subtype
          let ci : Set.Iio o := ⟨c, hc⟩
          have hpCi : p ∈ G.inessentialPaths (C.stage ci) := by
            rw [hstage ci]
            exact hp
          have hpTail : ∀ d, ci ≤ d →
              p ∈ G.inessentialPaths (C.stage d) := by
            intro d hcd
            rw [hstage d]
            exact ih d.1 d.2 (d.2.trans hoKappa) c hcd hcKappa hp
          have hstrict :
              G.strictRoof (G.terminalFrontier (C.stage ci)) ⊆
                G.strictRoof (G.terminalFrontier (C.limitPaths G)) := by
            rw [hstage ci, ← hlimit]
            let cs : Ladder.Stage kappa := ⟨c, hcKappa⟩
            let os : Ladder.Stage kappa := ⟨o, hoKappa⟩
            change
              G.strictRoof (G.terminalFrontier (L.warpAt cs)) ⊆
                G.strictRoof (G.terminalFrontier (L.warpAt os))
            have hfront := hL.strictRoof_frontier_mono
              (show cs ≤ os from hc.le)
            simpa only [
              L.frontier_eq_essential_terminalFrontier
                hL.roofsSourceAtStages,
              G.strictRoof_essential] using hfront
          change p ∈ G.inessentialPaths (L.accumulated oe)
          rw [hlimit]
          exact C.mem_inessentialPaths_limitPaths_of_tail
            ci hpCi hpTail hstrict
        · exact hp
  exact hmain b.1 b.2 a.1 hab a.2

/-- Deferred analogue of the final persistence lemma: an inessential
ordinary-stage component occurs literally in the final ladder warp. -/
theorem HalfwayGeometry.mem_limitWarp_of_mem_inessential
    {L : G.KappaLadder kappa} (hL : HalfwayGeometry L)
    {a : Ladder.Stage kappa} {p : G.DPath}
    (hp : p ∈ G.inessentialPaths (L.warpAt a)) :
    p ∈ L.limitWarp := by
  have hKappaLimit : Order.IsSuccLimit kappa.ord :=
    Cardinal.isSuccLimit_ord hL.regular.aleph0_le
  obtain ⟨C, hstage, hlimit⟩ :=
    hL.limitStages (Ladder.finalStage kappa) hKappaLimit
  let ai : Set.Iio kappa.ord := ⟨a.1, a.2⟩
  have hpAi : p ∈ C.stage ai := by
    rw [hstage ai]
    exact hp.1
  have hpTail : ∀ b, ai ≤ b → p ∈ C.stage b := by
    intro b hab
    rw [hstage b]
    let bs : Ladder.Stage kappa := ⟨b.1, b.2⟩
    exact (hL.inessentialPaths_mono_stage
      (a := a) (b := bs) hab hp).1
  change p ∈ L.accumulated (Ladder.finalStage kappa)
  rw [hlimit]
  exact C.mem_limitPaths_of_tail ai hpAi hpTail

/-- A hit of a limiting component is witnessed by an essential component
at that stage.  Its proof only uses the source-roof identity, so it remains
valid for the repaired deferred legality package. -/
theorem HalfwayGeometry.limitWarp_hitStages_essential_prefix
    {L : G.KappaLadder kappa} (hL : HalfwayGeometry L)
    {p : G.DPath} (hp : p ∈ L.limitWarp)
    (Sigma : Set (Ladder.Stage kappa)) :
    ∀ a ∈ L.hitStages Sigma p,
      ∃ q ∈ G.essentialWarpPart (L.warpAt a),
        (p.support ∩ q.support).Nonempty := by
  intro a ha
  obtain ⟨x, hxFrontier, hxp⟩ := ha.2
  have hxEssential :
      x ∈ G.essential (G.terminalFrontier (L.warpAt a)) := by
    rwa [← L.frontier_eq_essential_terminalFrontier
      hL.roofsSourceAtStages a]
  have hxTerminal :
      x ∈ G.terminalFrontier (G.essentialWarpPart (L.warpAt a)) := by
    rwa [G.terminalFrontier_essentialWarpPart]
  obtain ⟨q, hq, hqx⟩ := hxTerminal
  exact ⟨q, hq, x, hxp, G.terminal_mem_support hqx⟩

/-- Pointwise directed-supremum form of the corrected source Lemma 7.28
for deferred bookkeeping.

The last contradiction is genuinely deferred: the path found at the
supremum was already in the current warp, whereas the current marker is
outside that warp.  Hence the path belongs to `selectable L a`; together
with the no-earlier-record conclusion this puts `a` in `Deferred.phi L`. -/
theorem hitStages_dirSupClosed
    {L : G.KappaLadder kappa} (hL : HalfwayGeometry L)
    (Sigma : Set (Ladder.Stage kappa))
    (hSigma : DirSupClosed Sigma)
    (hmarkerOutside : MarkersOutsideCurrentWarp G L)
    {p : G.DPath} (hp : p ∈ L.limitWarp)
    (hmiss : L.LimitMissIsInessential Sigma p)
    (havoid : Disjoint Sigma (phi L)) :
    DirSupClosed (L.hitStages Sigma p) := by
  intro d hd hdn hdir a ha
  have haSigma : a ∈ Sigma :=
    hSigma (fun x hx ↦ (hd hx).1) hdn hdir ha
  by_cases hmeet : (L.frontier a ∩ p.support).Nonempty
  · exact ⟨haSigma, hmeet⟩
  have hpCurrent : p ∈ G.inessentialPaths (L.warpAt a) :=
    hmiss d a hd hdn hdir ha hmeet
  have hpNotRecorded : p ∉ (bookkeeping L).recordedBefore a := by
    rintro ⟨b, hba, hb⟩
    have hcofinal : ∃ c ∈ d, b < c := by
      by_contra h
      push Not at h
      have hub : ∀ c ∈ d, c ≤ b := fun c hc ↦ h c hc
      exact (not_le_of_gt hba) (ha.2 hub)
    obtain ⟨c, hc, hbc⟩ := hcofinal
    obtain ⟨q, hq, hpq⟩ :=
      hL.limitWarp_hitStages_essential_prefix hp Sigma c (hd hc)
    have hsuccle :
        Ladder.Stage.succExtended b ≤ Ladder.Stage.toExtended c := by
      change b.1 + 1 ≤ c.1
      exact (Order.add_one_le_iff).2 hbc
    have hpIE : p ∈ G.inessentialPaths (L.warpAt c) :=
      hL.recordedPathsPersist b p hb
        (Ladder.Stage.toExtended c) hsuccle
    exact (G.not_mem_inessentialPaths_of_intersects_essential
      (hL.warpStages (Ladder.Stage.toExtended c)) hq hpq) hpIE
  have hpNext : p ∈ G.inessentialPaths (L.successorWarp a) :=
    hL.currentInessentialPersists a hpCurrent
  have hmarker : L.marker a ≠ some p.initial := by
    intro hmarker
    exact hmarkerOutside a p.initial hmarker
      ⟨p, hpCurrent.1, p.initial_mem_support⟩
  have hpSelectable : p ∈ selectable L a := ⟨hpNext, hmarker⟩
  have haPhi : a ∈ phi L := ⟨p, hpSelectable, hpNotRecorded⟩
  exact (Set.disjoint_left.1 havoid haSigma haPhi).elim

/-- Directed-supremum form of the corrected source Lemma 7.28 for a
deferred-legal ladder. -/
theorem limitHitClosure_of_dirSupClosed
    {L : G.KappaLadder kappa} (hL : HalfwayGeometry L)
    (Sigma : Set (Ladder.Stage kappa))
    (hSigma : DirSupClosed Sigma)
    (hmarkerOutside : MarkersOutsideCurrentWarp G L)
    (hmiss : LimitMissesAreInessential G L Sigma)
    (havoid : Disjoint Sigma (phi L)) :
    LimitHitClosure G L Sigma := by
  intro p hp
  exact hitStages_dirSupClosed hL Sigma hSigma hmarkerOutside hp
    (hmiss p hp) havoid

/-- Club-specialized form used by the regular-cardinal construction. -/
theorem limitHitClosure_of_club
    {L : G.KappaLadder kappa} (hL : HalfwayGeometry L)
    (Sigma : Set (Ladder.Stage kappa))
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (hmarkerOutside : MarkersOutsideCurrentWarp G L)
    (hmiss : LimitMissesAreInessential G L Sigma)
    (havoid : Disjoint Sigma (phi L)) :
    LimitHitClosure G L Sigma :=
  limitHitClosure_of_dirSupClosed hL Sigma hSigma.dirSupClosed
    hmarkerOutside hmiss havoid

/-- Pointwise club-specialized form, convenient when the direct-limit
geometry establishes the missed-frontier conclusion for one path at a
time. -/
theorem hitStages_dirSupClosed_of_club
    {L : G.KappaLadder kappa} (hL : HalfwayGeometry L)
    (Sigma : Set (Ladder.Stage kappa))
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (hmarkerOutside : MarkersOutsideCurrentWarp G L)
    {p : G.DPath} (hp : p ∈ L.limitWarp)
    (hmiss : L.LimitMissIsInessential Sigma p)
    (havoid : Disjoint Sigma (phi L)) :
    DirSupClosed (L.hitStages Sigma p) := by
  exact hitStages_dirSupClosed hL Sigma hSigma.dirSupClosed
    hmarkerOutside hp hmiss havoid

end Deferred
end KappaLadder
end DWeb
end Erdos599
