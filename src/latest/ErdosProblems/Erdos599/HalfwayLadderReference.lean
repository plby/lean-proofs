/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayClubGeometry
import ErdosProblems.Erdos599.HalfwayFrontierHeight

/-!
# The finite reference warp at a selected ladder stage

After the club argument has selected its later stage, the reference family
used by the Section 9 transaction is the essential part of the accumulated
ladder warp at that stage.  It is important to make this choice *after* the
stage is selected: the family depends on the selected frontier and is not a
single family lying below every earlier ladder frontier.

This file records the elementary but useful consequences of that concrete
choice.  The reference is a finite-character warp, its terminal frontier is
literally the selected ladder frontier, and the canonical self-roofing
invariant puts all of its vertices below that frontier.  In a normalized web,
every member which starts in the original source is endpoint-pure.  Thus a
closing construction only has to absorb the marker-starting reference
members; endpoint purity of the untouched remainder is then automatic.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Ladder

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- The actual finite reference family at a ladder stage. -/
def ladderReference (L : Gamma.KappaLadder kappa)
    (a : Ladder.Stage kappa) : Set Gamma.DPath :=
  Gamma.essentialWarpPart (L.warpAt a)

namespace ladderReference

variable {L : Gamma.KappaLadder kappa} {a : Ladder.Stage kappa}

/-- The reference members which start at ladder markers rather than in the
original source. -/
def markerStarting : Set Gamma.DPath :=
  {p | p ∈ ladderReference L a ∧ p.initial ∉ Gamma.source}

/-- The source-starting part of the selected reference. -/
def sourceStarting : Set Gamma.DPath :=
  {p | p ∈ ladderReference L a ∧ p.initial ∈ Gamma.source}

/-- Essential trimming of an accumulated warp is still a warp. -/
theorem isWarp (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L) :
    Gamma.IsWarp (ladderReference L a) := by
  exact (hL.warpStages (Ladder.Stage.toExtended a)).essentialWarpPart

/-- The earlier marker stage owning a marker-starting reference member. -/
noncomputable def markerOwnerStage
    {rho : Cardinal.{u}}
    {L : Gamma.KappaLadder (succ rho)}
    {a : Ladder.Stage (succ rho)}
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (p : markerStarting (Gamma := Gamma) (L := L) (a := a)) :
    Ladder.Stage (succ rho) :=
  Classical.choose (show ∃ b : Ladder.Stage (succ rho),
      Ladder.Stage.succExtended b ≤ Ladder.Stage.toExtended a ∧
        L.marker b = some p.1.initial by
    rcases hL.accumulatedInitialProvenance
        (Ladder.Stage.toExtended a) p.1 p.2.1.1 with
      hpSource | ⟨b, hb, hmarker⟩
    · exact False.elim (p.2.2 hpSource)
    · exact ⟨b, hb, hmarker⟩)

theorem markerOwnerStage_spec
    {rho : Cardinal.{u}}
    {L : Gamma.KappaLadder (succ rho)}
    {a : Ladder.Stage (succ rho)}
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (p : markerStarting (Gamma := Gamma) (L := L) (a := a)) :
    Ladder.Stage.succExtended (markerOwnerStage hL p) ≤
        Ladder.Stage.toExtended a ∧
      L.marker (markerOwnerStage hL p) = some p.1.initial :=
  Classical.choose_spec (show ∃ b : Ladder.Stage (succ rho),
      Ladder.Stage.succExtended b ≤ Ladder.Stage.toExtended a ∧
        L.marker b = some p.1.initial by
    rcases hL.accumulatedInitialProvenance
        (Ladder.Stage.toExtended a) p.1 p.2.1.1 with
      hpSource | ⟨b, hb, hmarker⟩
    · exact False.elim (p.2.2 hpSource)
    · exact ⟨b, hb, hmarker⟩)

theorem markerOwnerStage_lt
    {rho : Cardinal.{u}}
    {L : Gamma.KappaLadder (succ rho)}
    {a : Ladder.Stage (succ rho)}
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (p : markerStarting (Gamma := Gamma) (L := L) (a := a)) :
    markerOwnerStage hL p < a := by
  have h := (markerOwnerStage_spec hL p).1
  change (markerOwnerStage hL p).1 + 1 ≤ a.1 at h
  change (markerOwnerStage hL p).1 < a.1
  exact Order.add_one_le_iff.mp h

theorem markerOwnerStage_injective
    {rho : Cardinal.{u}}
    {L : Gamma.KappaLadder (succ rho)}
    {a : Ladder.Stage (succ rho)}
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L) :
    Function.Injective
      (markerOwnerStage (Gamma := Gamma) (L := L) (a := a) hL) := by
  intro p q hpq
  apply Subtype.ext
  by_contra hne
  have hpmarker := (markerOwnerStage_spec hL p).2
  have hqmarker := (markerOwnerStage_spec hL q).2
  rw [hpq] at hpmarker
  have hinitial : p.1.initial = q.1.initial :=
    Option.some.inj (hpmarker.symm.trans hqmarker)
  have hdisjoint := (isWarp hL) p.2.1 q.2.1 hne
  exact Set.disjoint_left.1 hdisjoint p.1.initial_mem_support
    (hinitial ▸ q.1.initial_mem_support)

/-- Essential trimming discards every ray. -/
theorem finiteCharacter :
    Gamma.HasFiniteCharacter (ladderReference L a) := by
  exact Gamma.hasFiniteCharacter_essentialWarpPart (L.warpAt a)

theorem markerStarting_subset_hangingAt
    {rho : Cardinal.{u}}
    {L : Gamma.KappaLadder (succ rho)} {a : Ladder.Stage (succ rho)} :
    markerStarting (Gamma := Gamma) (L := L) (a := a) ⊆
      CardinalInduction.HalfwayFrontierHeight.hangingAt L a := by
  intro p hp
  exact ⟨hp.1.1, hp.2⟩

/-- There are at most `rho` marker-starting reference members at a stage of
the `rho^+` ladder. -/
theorem mk_markerStarting_le
    {rho : Cardinal.{u}}
    {L : Gamma.KappaLadder (succ rho)}
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (a : Ladder.Stage (succ rho)) :
    #(markerStarting (Gamma := Gamma) (L := L) (a := a)) ≤ rho := by
  have hlt :
      #(markerStarting (Gamma := Gamma) (L := L) (a := a)) < succ rho :=
    RegularCardinal.mk_lt_of_injective_bounded_stage a
      (markerOwnerStage hL) (markerOwnerStage_injective hL)
      (markerOwnerStage_lt hL)
  exact lt_succ_iff.mp hlt

/-- The vertices of the marker-starting reference are contained in the
canonical hanging deletion set used by the frontier-height proof. -/
theorem markerStarting_vertices_subset_hangingVerticesAt
    {rho : Cardinal.{u}}
    {L : Gamma.KappaLadder (succ rho)} {a : Ladder.Stage (succ rho)} :
    Gamma.vertexSet
        (markerStarting (Gamma := Gamma) (L := L) (a := a)) ⊆
      CardinalInduction.HalfwayFrontierHeight.hangingVerticesAt L a := by
  rintro x ⟨p, hp, hxp⟩
  exact ⟨p, markerStarting_subset_hangingAt hp, hxp⟩

/-- The marker-starting part contributes at most `rho` vertices. -/
theorem mk_markerStarting_vertices_le
    {rho : Cardinal.{u}}
    {L : Gamma.KappaLadder (succ rho)}
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hrho : aleph0 ≤ rho) (a : Ladder.Stage (succ rho)) :
    #(Gamma.vertexSet
        (markerStarting (Gamma := Gamma) (L := L) (a := a))) ≤ rho := by
  exact CardinalInduction.HalfwayFrontierHeight.mk_vertexSet_le_of_mk_family_le
    hrho _ (mk_markerStarting_le hL a)

/-- The reference terminal frontier is the selected ladder frontier. -/
theorem terminalFrontier_eq
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L) :
    Gamma.terminalFrontier (ladderReference L a) = L.frontier a := by
  rw [ladderReference, Gamma.terminalFrontier_essentialWarpPart,
    L.frontier_eq_essential_terminalFrontier hL.roofsSourceAtStages]

/-- The concrete reference lies below its selected frontier whenever the
canonical accumulated family has its construction self-roofing invariant. -/
theorem vertexSet_subset_roof
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hself : Gamma.vertexSet (L.warpAt a) ⊆
      Gamma.roof (Gamma.terminalFrontier (L.warpAt a))) :
    Gamma.vertexSet (ladderReference L a) ⊆
      Gamma.roof (L.frontier a) := by
  intro x hx
  have hxRaw : x ∈ Gamma.vertexSet (L.warpAt a) := by
    obtain ⟨p, hp, hxp⟩ := hx
    exact ⟨p, hp.1, hxp⟩
  have hxRoof := hself hxRaw
  rw [L.frontier_eq_essential_terminalFrontier hL.roofsSourceAtStages,
    Gamma.roof_essential]
  exact hxRoof

/-- A source-starting member of the selected reference is endpoint-pure.

The reference as a whole may also contain marker-starting components.  The
closing construction absorbs precisely those components; this lemma is the
endpoint statement needed for every untouched reference component. -/
theorem endpointPure_of_initial_mem_source
    (hGamma : Gamma.IsNormalized)
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {p : Gamma.DPath} (hp : p ∈ ladderReference L a)
    (hpSource : p.initial ∈ Gamma.source) :
    CardinalInduction.IsPathBetween Gamma Gamma.source (L.frontier a) p := by
  obtain ⟨q, rfl⟩ := finiteCharacter hp
  have hsource : q.support ∩ Gamma.source = {q.start} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxsource⟩
      have hxeq : x = q.start := by
        exact Alternating.path_eq_initial_of_mem_support_of_mem_source
          hGamma (Sum.inl q : Gamma.DPath) hxq hxsource
      subst x
      exact Set.mem_singleton q.start
    · intro x hx
      have hxeq : x = q.start := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨q.start_mem_support, hpSource⟩
  have hterminal : q.support ∩ L.frontier a = {q.finish} := by
    rw [← terminalFrontier_eq hL]
    apply Set.Subset.antisymm
    · exact DWeb.IsWarp.finite_support_inter_terminalFrontier Gamma
        (isWarp hL) hp
    · intro x hx
      have hxeq : x = q.finish := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨q.finish_mem_support, ⟨Sum.inl q, hp, rfl⟩⟩
  refine ⟨q, rfl, ?_, hsource⟩
  apply Set.Subset.antisymm
  · rintro x ⟨hxq, hxboundary⟩
    rcases hxboundary with hxsource | hxfrontier
    · have hxstart : x ∈ ({q.start} : Set V) :=
        hsource ▸ ⟨hxq, hxsource⟩
      exact Set.mem_insert_iff.2
        (Or.inl (Set.mem_singleton_iff.1 hxstart))
    · have hxfinish : x ∈ ({q.finish} : Set V) :=
        hterminal ▸ ⟨hxq, hxfrontier⟩
      exact Set.mem_insert_iff.2
        (Or.inr (Set.mem_singleton_iff.1 hxfinish))
  · intro x hx
    rcases Set.mem_insert_iff.1 hx with hxstart | hxfinish
    · subst x
      exact ⟨q.start_mem_support, Or.inl hpSource⟩
    · have hxeq : x = q.finish := Set.mem_singleton_iff.1 hxfinish
      subst x
      have hfinish : q.finish ∈ L.frontier a := by
        have : q.finish ∈ ({q.finish} : Set V) := Set.mem_singleton _
        exact (hterminal ▸ this).2
      exact ⟨q.finish_mem_support, Or.inr hfinish⟩

/-- Endpoint purity for a subfamily follows once the closing construction
has ruled out marker-starting members of that subfamily. -/
theorem endpointPure_of_initials
    (hGamma : Gamma.IsNormalized)
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {R : Set Gamma.DPath} (hR : R ⊆ ladderReference L a)
    (hinitial : ∀ p ∈ R, p.initial ∈ Gamma.source) :
    ∀ p ∈ R,
      CardinalInduction.IsPathBetween Gamma Gamma.source (L.frontier a) p := by
  intro p hp
  exact endpointPure_of_initial_mem_source hGamma hL (hR hp)
    (hinitial p hp)

end ladderReference

namespace ClubStageGeometry

variable {Y : Set Gamma.DPath} {theta : Cardinal.{u}}

/-- `ClubStageGeometry` has no reference-dependent field.  This explicit
reindexing operation lets the club be selected first and the genuine
stage-dependent reference be installed afterwards. -/
def withReference
    (C : ClubStageGeometry Gamma Y kappa theta)
    (Y' : Set Gamma.DPath) : ClubStageGeometry Gamma Y' kappa theta :=
  { C with }

@[simp] theorem withReference_ladder
    (C : ClubStageGeometry Gamma Y kappa theta) (Y' : Set Gamma.DPath) :
    (C.withReference Y').ladder = C.ladder := rfl

@[simp] theorem withReference_newStage
    (C : ClubStageGeometry Gamma Y kappa theta) (Y' : Set Gamma.DPath) :
    (C.withReference Y').newStage = C.newStage := rfl

@[simp] theorem withReference_closedStage
    (C : ClubStageGeometry Gamma Y kappa theta) (Y' : Set Gamma.DPath) :
    (C.withReference Y').closedStage = C.closedStage := rfl

/-- The reference dictated by the selected later club stage. -/
def selectedReference (C : ClubStageGeometry Gamma Y kappa theta) :
    Set Gamma.DPath :=
  ladderReference C.ladder C.newStage

theorem selectedReference_isWarp
    (C : ClubStageGeometry Gamma Y kappa theta) :
    Gamma.IsWarp C.selectedReference :=
  ladderReference.isWarp C.legal

theorem selectedReference_finiteCharacter
    (C : ClubStageGeometry Gamma Y kappa theta) :
    Gamma.HasFiniteCharacter C.selectedReference :=
  ladderReference.finiteCharacter

theorem terminalFrontier_selectedReference
    (C : ClubStageGeometry Gamma Y kappa theta) :
    Gamma.terminalFrontier C.selectedReference = C.newSlice :=
  ladderReference.terminalFrontier_eq C.legal

end ClubStageGeometry

end LinkageBlueprint
end Blueprint
end Erdos599
