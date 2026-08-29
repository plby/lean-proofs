/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CommonQuotient
import ErdosProblems.Erdos599.Ladder

/-!
# Fresh markers and the canonical arrow

This file isolates the exact contact invariant needed to show that the
optional marker path is disjoint from the canonical arrow.  Warp-valuedness
alone does not imply this invariant: an interior vertex of an arbitrary old
warp can survive the quotient and be target-reachable there.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath

universe u

namespace DWeb

variable {V : Type u} (G : DWeb V)

/-- Every target-reachable vertex of the old family which survives the
quotient is already in the source of the essential quotient stage.  The
reachability conjunct is essential: without it, membership in the quotient
source does not imply membership in the source of its `essentialPart`. -/
def LadderStateContactsStageSource (s : G.LadderAccumulationState) : Prop :=
  (G.vertexSet s.1 ∩ G.quotientVertexSet (G.terminalFrontier s.1)) ∩
      (G.stageWebOf s.1).reachableToTarget ⊆
    (G.stageWebOf s.1).source

/-- The two roofing invariants maintained by the canonical recursion imply
the exact old-family contact condition needed for marker freshness.  Indeed,
a roofed vertex which survives strict-roof deletion is essential; source
roofing identifies that essential frontier with the quotient source, and
the final reachability conjunct puts it in the source of the essential
part. -/
theorem ladderStateContactsStageSource_of_roofs
    (s : G.LadderAccumulationState)
    (hsource : G.source ⊆ G.roof (G.terminalFrontier s.1))
    (hold : G.vertexSet s.1 ⊆ G.roof (G.terminalFrontier s.1)) :
    G.LadderStateContactsStageSource s := by
  intro x hx
  have hxRoof : x ∈ G.roof (G.terminalFrontier s.1) := hold hx.1.1
  have hxEssential : x ∈ G.essential (G.terminalFrontier s.1) := by
    by_contra hxNotEssential
    exact hx.1.2 ⟨hxRoof, hxNotEssential⟩
  let Q := G.quotient (G.terminalFrontier s.1)
  have hxQReach : x ∈ Q.reachableToTarget := by
    have hxStageReach := hx.2
    change x ∈ Q.essentialPart.reachableToTarget at hxStageReach
    obtain ⟨p, hpStart, hpFinish⟩ := hxStageReach
    let q : DirectedPath.FinitePath Q.graph :=
      p.lift (fun {_ _} h ↦ Q.essentialPart_adj_imp h)
    exact ⟨q,
      by simpa only [q, DirectedPath.FinitePath.lift] using hpStart,
      by simpa only [q, DirectedPath.FinitePath.lift,
        Q.essentialPart_target] using hpFinish⟩
  refine ⟨?_, hxQReach⟩
  rw [G.quotient_source_eq_essential_terminalFrontier_of_roofsSource
    hsource]
  exact hxEssential

/-- The family-level lift of the rung preserves its vertex set. -/
theorem vertexSet_liftedLadderRungOfState
    (s : G.LadderAccumulationState) :
    G.vertexSet (G.liftedLadderRungOfState s) =
      (G.stageWebOf s.1).vertexSet (G.ladderRungOfState s) := by
  ext x
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hxp⟩
    refine ⟨q, hq, ?_⟩
    unfold liftLadderStagePathOf at hxp
    rw [G.support_liftQuotientPath] at hxp
    change x ∈
      ((G.quotient (G.terminalFrontier s.1)).liftEssentialPartPath
        (show (G.quotient
          (G.terminalFrontier s.1)).essentialPart.DPath from q)).support at hxp
    rw [(G.quotient
      (G.terminalFrontier s.1)).support_liftEssentialPartPath] at hxp
    exact hxp
  · rintro ⟨q, hq, hxq⟩
    refine ⟨G.liftLadderStagePathOf s.1 q, ⟨q, hq, rfl⟩, ?_⟩
    unfold liftLadderStagePathOf
    rw [G.support_liftQuotientPath]
    change x ∈
      ((G.quotient (G.terminalFrontier s.1)).liftEssentialPartPath
        (show (G.quotient
          (G.terminalFrontier s.1)).essentialPart.DPath from q)).support
    rw [(G.quotient
      (G.terminalFrontier s.1)).support_liftEssentialPartPath]
    exact hxq

/-- A selected marker is outside the old accumulated family, provided the
old family meets the surviving quotient region only in the stage source. -/
theorem ladderMarkerOfState_not_mem_old_vertexSet
    {preferred : Option V} {s : G.LadderAccumulationState} {y : V}
    (hcontact : G.LadderStateContactsStageSource s)
    (hy : G.ladderMarkerOfState preferred s = some y) :
    y ∉ G.vertexSet s.1 := by
  have hyCandidate := G.ladderMarkerOfState_mem_candidates hy
  intro hyOld
  exact hyCandidate.2 (Or.inl
    (hcontact ⟨⟨hyOld, hyCandidate.1.2⟩, hyCandidate.1.1⟩))

/-- A selected marker is outside the lifted canonical rung. -/
theorem ladderMarkerOfState_not_mem_liftedRung_vertexSet
    {preferred : Option V} {s : G.LadderAccumulationState} {y : V}
    (hy : G.ladderMarkerOfState preferred s = some y) :
    y ∉ G.vertexSet (G.liftedLadderRungOfState s) := by
  have hyCandidate := G.ladderMarkerOfState_mem_candidates hy
  rw [G.vertexSet_liftedLadderRungOfState s]
  exact fun hyRung ↦ hyCandidate.2 (Or.inr hyRung)

/-- Under the exact old-family contact invariant, the concrete arrow and
the optional marker have disjoint total vertex sets.  This is the cross
support condition actually needed to preserve warp-valuedness under union. -/
theorem disjoint_vertexSet_arrow_ladderMarkerPathSetOfState
    (preferred : Option V) (s : G.LadderAccumulationState)
    (_hwarp : G.IsWarp s.1)
    (hcontact : G.LadderStateContactsStageSource s) :
    Disjoint
      (G.vertexSet (G.arrow s.1 (G.liftedLadderRungOfState s)))
      (G.vertexSet (G.ladderMarkerPathSetOfState preferred s)) := by
  cases hm : G.ladderMarkerOfState preferred s with
  | none =>
      apply Set.disjoint_left.2
      intro x _hx hxEmpty
      rcases hxEmpty with ⟨p, hp, _hxp⟩
      simp [ladderMarkerPathSetOfState, hm] at hp
  | some y =>
      have hyOld : y ∉ G.vertexSet s.1 :=
        G.ladderMarkerOfState_not_mem_old_vertexSet hcontact hm
      have hyRung : y ∉ G.vertexSet (G.liftedLadderRungOfState s) :=
        G.ladderMarkerOfState_not_mem_liftedRung_vertexSet hm
      have hyArrow :
          y ∉ G.vertexSet
            (G.arrow s.1 (G.liftedLadderRungOfState s)) := by
        intro hy
        rcases G.vertexSet_arrow_subset s.1
            (G.liftedLadderRungOfState s) hy with hy | hy
        · exact hyOld hy
        · exact hyRung hy
      rw [Set.disjoint_left]
      intro x hxArrow hxMarker
      rcases hxMarker with ⟨p, hp, hxp⟩
      have hp : p = G.trivialPath y := by
        simpa [ladderMarkerPathSetOfState, hm] using hp
      rw [hp, G.support_trivialPath] at hxp
      have hxy : x = y := by simpa using hxp
      exact hyArrow (hxy ▸ hxArrow)

/-- Family-level disjointness follows from the stronger vertex-set
disjointness.  This is useful for removing the optional marker from the
successor family, while the preceding theorem is the one used for warps. -/
theorem disjoint_arrow_ladderMarkerPathSetOfState
    (preferred : Option V) (s : G.LadderAccumulationState)
    (hwarp : G.IsWarp s.1)
    (hcontact : G.LadderStateContactsStageSource s) :
    Disjoint (G.arrow s.1 (G.liftedLadderRungOfState s))
      (G.ladderMarkerPathSetOfState preferred s) := by
  have hvertex :=
    G.disjoint_vertexSet_arrow_ladderMarkerPathSetOfState preferred s
      hwarp hcontact
  rw [Set.disjoint_left]
  intro p hpArrow hpMarker
  have hpSupport : p.support.Nonempty := DirectedPath.Path.support_nonempty p
  obtain ⟨x, hxp⟩ := hpSupport
  exact Set.disjoint_left.1 hvertex
    ⟨p, hpArrow, hxp⟩ ⟨p, hpMarker, hxp⟩

/-- Unconditional marker/arrow support-disjointness from the canonical
roofing invariants. -/
theorem disjoint_vertexSet_arrow_ladderMarkerPathSetOfState_of_roofs
    (preferred : Option V) (s : G.LadderAccumulationState)
    (hwarp : G.IsWarp s.1)
    (hsource : G.source ⊆ G.roof (G.terminalFrontier s.1))
    (hold : G.vertexSet s.1 ⊆ G.roof (G.terminalFrontier s.1)) :
    Disjoint
      (G.vertexSet (G.arrow s.1 (G.liftedLadderRungOfState s)))
      (G.vertexSet (G.ladderMarkerPathSetOfState preferred s)) :=
  G.disjoint_vertexSet_arrow_ladderMarkerPathSetOfState preferred s hwarp
    (G.ladderStateContactsStageSource_of_roofs s hsource hold)

/-- The optional marker family is itself always a warp. -/
theorem isWarp_ladderMarkerPathSetOfState
    (preferred : Option V) (s : G.LadderAccumulationState) :
    G.IsWarp (G.ladderMarkerPathSetOfState preferred s) := by
  cases hm : G.ladderMarkerOfState preferred s with
  | none => simp [ladderMarkerPathSetOfState, hm, IsWarp]
  | some y =>
      intro p hp q hq hpq
      simp only [ladderMarkerPathSetOfState, hm,
        Set.mem_singleton_iff] at hp hq
      exact (hpq (hp.trans hq.symm)).elim

/-- The two canonical path lifts preserve disjointness of the chosen rung.
This local version avoids making the marker theorem depend on the full
transfinite construction module. -/
theorem isWarp_liftedLadderRungOfState_for_marker
    (s : G.LadderAccumulationState) :
    G.IsWarp (G.liftedLadderRungOfState s) := by
  let Q := G.quotient (G.terminalFrontier s.1)
  have hR : Q.essentialPart.IsWarp (G.ladderRungOfState s) :=
    (G.stageWebOf s.1).chosenMaximalWave.property.1
  rintro p ⟨p₀, hp₀, rfl⟩ q ⟨q₀, hq₀, rfl⟩ hpq
  let p₀' : Q.essentialPart.DPath := p₀
  let q₀' : Q.essentialPart.DPath := q₀
  have hp₀' : p₀' ∈ G.ladderRungOfState s := hp₀
  have hq₀' : q₀' ∈ G.ladderRungOfState s := hq₀
  have hpq' : p₀' ≠ q₀' := by
    intro h
    apply hpq
    change G.liftLadderStagePathOf s.1
        (show (G.stageWebOf s.1).DPath from p₀') =
      G.liftLadderStagePathOf s.1
        (show (G.stageWebOf s.1).DPath from q₀')
    rw [h]
  have hdis : Disjoint p₀'.support q₀'.support :=
    hR hp₀' hq₀' hpq'
  change Disjoint
    (G.liftQuotientPath (G.terminalFrontier s.1)
      (Q.liftEssentialPartPath p₀')).support
    (G.liftQuotientPath (G.terminalFrontier s.1)
      (Q.liftEssentialPartPath q₀')).support
  simpa only [G.support_liftQuotientPath,
    Q.support_liftEssentialPartPath] using hdis

/-- The active canonical successor is a warp under the two roofing
invariants.  This is the unconditional successor lemma consumed by the
transfinite construction: no separate marker-contact or disjointness
premise remains. -/
theorem isWarp_activeLadderSuccessor_of_roofs
    (preferred : Option V) (s : G.LadderAccumulationState)
    (hwarp : G.IsWarp s.1)
    (hsource : G.source ⊆ G.roof (G.terminalFrontier s.1))
    (hold : G.vertexSet s.1 ⊆ G.roof (G.terminalFrontier s.1)) :
    G.IsWarp (G.activeLadderSuccessor preferred s) := by
  have harrow :
      G.IsWarp (G.arrow s.1 (G.liftedLadderRungOfState s)) :=
    G.isWarp_arrow hwarp
      (G.isWarp_liftedLadderRungOfState_for_marker s)
  have hmarker := G.isWarp_ladderMarkerPathSetOfState preferred s
  have hcross :=
    G.disjoint_vertexSet_arrow_ladderMarkerPathSetOfState_of_roofs
      preferred s hwarp hsource hold
  unfold activeLadderSuccessor
  intro p hp q hq hpq
  rcases hp with hpArrow | hpMarker <;>
    rcases hq with hqArrow | hqMarker
  · exact harrow hpArrow hqArrow hpq
  · apply Set.disjoint_left.2
    intro x hxp hxq
    exact Set.disjoint_left.1 hcross
      ⟨p, hpArrow, hxp⟩ ⟨q, hqMarker, hxq⟩
  · apply Set.disjoint_left.2
    intro x hxp hxq
    exact Set.disjoint_left.1 hcross
      ⟨q, hqArrow, hxq⟩ ⟨p, hpMarker, hxp⟩
  · exact hmarker hpMarker hqMarker hpq

/-- One canonical successor recursion step preserves warp-valuedness from
the two roofing invariants, whether the state is active or already frozen. -/
theorem isWarp_ladderSuccessorState_of_roofs
    (preferred : Ordinal.{u} → Option V) (o : Ordinal.{u})
    (s : G.LadderAccumulationState)
    (hwarp : G.IsWarp s.1)
    (hsource : G.source ⊆ G.roof (G.terminalFrontier s.1))
    (hold : G.vertexSet s.1 ⊆ G.roof (G.terminalFrontier s.1)) :
    G.IsWarp (G.ladderSuccessorState preferred o s).1 := by
  classical
  by_cases hs : s.2 = true
  · rw [ladderSuccessorState, dif_pos hs]
    exact G.isWarp_activeLadderSuccessor_of_roofs
      (preferred o) s hwarp hsource hold
  · rw [ladderSuccessorState, dif_neg hs]
    exact hwarp

end DWeb
end Erdos599
