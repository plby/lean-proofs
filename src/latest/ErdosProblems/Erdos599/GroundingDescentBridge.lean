/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingDescent

/-!
# The ordinal descent in the grounding auxiliary web

This file supplies the roof-calculus bridge used in source Lemma 7.17 and
Assertion 8.12.  In particular, it makes explicit the fact which is easy to
lose when quotient webs retain the ambient vertex type: a fresh ladder marker
lies in the *actual quotient vertex region*, and hence is outside the roof of
the frontier at the stage where it is chosen.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

open DirectedPath Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder

/-! ## The exact old/new split in the successor bookkeeping -/

/-- Stages whose selected record was already inessential before the rung
was installed.  These are precisely the records to which source Lemmas
7.19--7.20 apply without an index shift. -/
def priorInessentialRecordStages
    (L : Gamma.KappaLadder kappa) : Set (Stage kappa) :=
  {a | ∃ p : Gamma.DPath, L.chosen a = some p ∧
      p ∈ Gamma.inessentialPaths (L.warpAt a)}

/-- The complementary obstruction stages: their chosen record is
inessential in `Y_(a+1)`, but was not inessential in `Y_a`.  Keeping this
class separate is essential: assigning it the ordinal `a` in the Section 8
auxiliary web permits a same-stage source--target edge. -/
def freshInessentialRecordStages
    (L : Gamma.KappaLadder kappa) : Set (Stage kappa) :=
  L.phi \ L.priorInessentialRecordStages

theorem phi_eq_priorInessential_union_freshInessential
    (L : Gamma.KappaLadder kappa) (hvalid : L.HasValidBookkeeping) :
    L.phi = L.priorInessentialRecordStages ∪
      L.freshInessentialRecordStages := by
  apply Set.Subset.antisymm
  · intro a ha
    by_cases hold : a ∈ L.priorInessentialRecordStages
    · exact Or.inl hold
    · exact Or.inr ⟨ha, hold⟩
  · rintro a (ha | ha)
    · obtain ⟨p, hp, _⟩ := ha
      exact (L.bookkeeping.mem_phi_iff_exists_chosen
        hvalid).2 ⟨p, hp⟩
    · exact ha.1

/-- A fresh record is exactly an unrecorded successor-inessential path
which is not yet inessential in the current warp. -/
theorem freshInessentialRecordStages_spec
    (L : Gamma.KappaLadder kappa) (hvalid : L.HasValidBookkeeping)
    {a : Stage kappa} (ha : a ∈ L.freshInessentialRecordStages) :
    ∃ p : Gamma.DPath,
      L.chosen a = some p ∧
      p ∈ Gamma.inessentialPaths (L.successorWarp a) ∧
      p ∉ Gamma.inessentialPaths (L.warpAt a) ∧
      p ∉ L.bookkeeping.recordedBefore a := by
  obtain ⟨p, hp⟩ :=
    (L.bookkeeping.mem_phi_iff_exists_chosen hvalid).1 ha.1
  have hpAvailable := L.bookkeeping.chosen_mem_available hvalid hp
  refine ⟨p, hp, hpAvailable.1, ?_, hpAvailable.2⟩
  intro hpCurrent
  exact ha.2 ⟨p, hp, hpCurrent⟩

/-- The grounded part of the old-record branch. -/
def priorInessentialGroundStages
    (L : Gamma.KappaLadder kappa) : Set (Stage kappa) :=
  L.phiGround ∩ L.priorInessentialRecordStages

/-- The grounded part of the genuinely successor-new branch. -/
def freshInessentialGroundStages
    (L : Gamma.KappaLadder kappa) : Set (Stage kappa) :=
  L.phiGround ∩ L.freshInessentialRecordStages

theorem phiGround_eq_priorInessential_union_freshInessential
    (L : Gamma.KappaLadder kappa) (hvalid : L.HasValidBookkeeping) :
    L.phiGround = L.priorInessentialGroundStages ∪
      L.freshInessentialGroundStages := by
  have hground : L.phiGround ⊆ L.phi := by
    rintro a ⟨p, hp, _⟩
    exact (L.bookkeeping.mem_phi_iff_exists_chosen hvalid).2 ⟨p, hp⟩
  rw [priorInessentialGroundStages, freshInessentialGroundStages,
    ← Set.inter_union_distrib_left,
    ← L.phi_eq_priorInessential_union_freshInessential hvalid]
  exact (Set.inter_eq_left.2 hground).symm

/-- The stationary grounded obstruction therefore has an exact dichotomy:
either the records already inessential at their named stage are stationary,
or the genuinely successor-new records are stationary.  The first branch is
the input to strict ordinal descent; the second must be grounded separately. -/
theorem IsKappaHindrance.priorInessential_or_freshInessential_isStationary
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance) :
    Stationary.IsStationaryBelow kappa L.priorInessentialGroundStages ∨
      Stationary.IsStationaryBelow kappa L.freshInessentialGroundStages := by
  have hground : Stationary.IsStationaryBelow kappa L.phiGround :=
    KappaLadder.IsKappaHindrance.phiGround_isStationary L hL
      hL.legal.regular hL.legal.uncountable
  have hcof : Order.cof (Stage kappa) ≠ ℵ₀ := by
    rw [Stationary.cof_below_eq_lift hL.legal.regular]
    rw [← Cardinal.lift_aleph0.{u + 1, u}]
    exact (Cardinal.lift_lt.mpr hL.legal.uncountable).ne'
  rw [L.phiGround_eq_priorInessential_union_freshInessential
    hL.legal.validBookkeeping] at hground
  exact (isStationary_union_iff hcof).mp hground

/-- Finite prior records have their terminal in the strict roof of the
frontier with the same ordinal index (source Lemmas 7.19--7.20, in the
case where the emergence stage is already at most the record stage). -/
theorem priorInessential_finite_terminal_mem_strictRoof_frontier
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    {a : Stage kappa} (ha : a ∈ L.priorInessentialRecordStages)
    {p : Gamma.DPath} {x : V} (hp : L.chosen a = some p)
    (hterminal : Gamma.terminal? p = some x) :
    x ∈ Gamma.strictRoof (L.frontier a) := by
  obtain ⟨q, hq, hqCurrent⟩ := ha
  have hqp : q = p := Option.some.inj (hq.symm.trans hp)
  subst q
  have hx : x ∈ Gamma.strictRoof
      (Gamma.terminalFrontier (L.warpAt a)) :=
    Gamma.terminal_mem_strictRoof_of_mem_inessentialPaths
      hqCurrent hterminal
  rw [L.frontier_eq_essential_terminalFrontier
    hlegal.roofsSourceAtStages a, Gamma.strictRoof_essential]
  exact hx

/-- Every vertex of a grounded ray which was already inessential at its
record stage lies in the strict roof of that stage's frontier.  The proof
uses only warp disjointness: a ray component cannot meet the finite terminal
frontier of its own warp, so prefix splicing roofs its whole support. -/
theorem priorInessential_grounded_ray_support_subset_strictRoof_frontier
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    {a : Stage kappa} (ha : a ∈ L.priorInessentialRecordStages)
    {r : DirectedPath.Ray Gamma.graph}
    (hchosen : L.chosen a = some (.inr r : Gamma.DPath))
    (hground : r.initial ∈ Gamma.source) :
    r.support ⊆ Gamma.strictRoof (L.frontier a) := by
  obtain ⟨p, hp, hpCurrent⟩ := ha
  have hpr : p = (.inr r : Gamma.DPath) :=
    Option.some.inj (hp.symm.trans hchosen)
  subst p
  let T := Gamma.terminalFrontier (L.warpAt a)
  have hsupportDisjoint : Disjoint r.support T := by
    apply Set.disjoint_left.2
    intro z hzr hzT
    obtain ⟨q, hqWarp, hqTerminal⟩ := hzT
    have hrq : (.inr r : Gamma.DPath) ≠ q := by
      intro hrq
      have hterm := congrArg Gamma.terminal? hrq
      rw [Gamma.terminal?_ray, hqTerminal] at hterm
      cases hterm
    exact Set.disjoint_left.1
      (hlegal.warpStages (Stage.toExtended a)
        hpCurrent.1 hqWarp hrq)
      hzr (Gamma.terminal_mem_support hqTerminal)
  have hsupportRoofT : r.support ⊆ Gamma.roof T := by
    apply Gamma.pathSupportRoof (.inr r : Gamma.DPath) T
    · exact hlegal.roofsSourceAtStages (Stage.toExtended a) hground
    · intro t ht
      rw [Gamma.terminal?_ray] at ht
      cases ht
    · intro z hz
      exact False.elim
        (Set.disjoint_left.1 hsupportDisjoint hz.1 hz.2)
  intro z hzr
  have hzRoof : z ∈ Gamma.roof (L.frontier a) := by
    rw [L.frontier_eq_essential_terminalFrontier
      hlegal.roofsSourceAtStages a, Gamma.roof_essential]
    exact hsupportRoofT hzr
  refine ⟨hzRoof, ?_⟩
  intro hzEssential
  have hzFrontier : z ∈ L.frontier a := by
    rw [← hlegal.frontiersEssential a]
    exact hzEssential
  have hzT : z ∈ T :=
    by
      rw [L.frontier_eq_essential_terminalFrontier
        hlegal.roofsSourceAtStages a] at hzFrontier
      exact hzFrontier.1
  exact Set.disjoint_left.1 hsupportDisjoint hzr hzT

theorem priorInessentialGround_ray_support_subset_strictRoof_frontier
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    {a : Stage kappa} (ha : a ∈ L.priorInessentialGroundStages)
    {r : DirectedPath.Ray Gamma.graph}
    (hchosen : L.chosen a = some (.inr r : Gamma.DPath)) :
    r.support ⊆ Gamma.strictRoof (L.frontier a) := by
  obtain ⟨q, hq, hqGround⟩ := ha.1
  have hqr : q = (.inr r : Gamma.DPath) :=
    Option.some.inj (hq.symm.trans hchosen)
  have hrGround : r.initial ∈ Gamma.source := by
    rw [hqr] at hqGround
    exact hqGround
  exact L.priorInessential_grounded_ray_support_subset_strictRoof_frontier
    hlegal ha.2 hchosen hrGround

/-- The source of the essential quotient stage is contained in the full
terminal commitment of the accumulated warp. -/
theorem frontier_subset_terminalFrontier
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (a : Stage kappa) :
    L.frontier a ⊆ Gamma.terminalFrontier (L.warpAt a) := by
  intro x hx
  rw [L.frontier_eq_essential_terminalFrontier
    hlegal.roofsSourceAtStages a] at hx
  exact hx.1

/-- A marker selected at stage `a` is outside the commitment set of the
quotient defining that stage.  The `quotientVertexSet` conjunct in
`stageVertexSet` is essential here: without it a deleted target would still
have a spurious length-zero reachability witness in the same ambient type. -/
theorem marker_not_mem_stageCommitment
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    {a : Stage kappa} {y : V} (hy : L.marker a = some y) :
    y ∉ Gamma.terminalFrontier (L.warpAt a) := by
  let T := Gamma.terminalFrontier (L.warpAt a)
  have hyCandidate := (hlegal.freshMarkers.2 a y hy).1
  have hySurvives : y ∉ Gamma.strictRoof T := hyCandidate.1.2
  have hyNotSource : y ∉ (L.stageWeb a).source := by
    exact fun h ↦ hyCandidate.2 (Or.inl h)
  intro hyT
  by_cases hyEssential : y ∈ Gamma.essential T
  · apply hyNotSource
    change y ∈ L.frontier a
    rw [L.frontier_eq_essential_terminalFrontier
      hlegal.roofsSourceAtStages a]
    exact hyEssential
  · exact hySurvives ⟨Gamma.subset_roof T hyT, hyEssential⟩

/-! ## The exact roof-transport content of source Lemma 7.17 -/

/-- The two pathwise roof conclusions supplied by Lemmas 7.17--7.20.

This interface deliberately stops *before* the ordinal inequality.  Its
fields say only that a Lambda path starting at the finite terminal, or at
the proxy, of a record born at stage `a` ends in `roof (frontier a)`.
The theorem below derives strict ordinal descent from these geometric
statements and marker freshness. -/
structure Lemma717RoofTransport
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal) : Prop where
  finite : ∀ (q : FinitePath (L.popularAuxiliaryInput hlegal).lambda.graph)
      (hs : q.start ∈ (L.popularAuxiliaryInput hlegal).lambda.source)
      (ht : q.finish ∈ (L.popularAuxiliaryInput hlegal).lambda.target)
      (x : L.finiteTerminalSet) (y : V),
      q.start = .old x.1 → q.finish = .old y →
      y ∈ Gamma.roof
        (L.frontier (L.finiteTerminalStage x))
  proxy : ∀ (q : FinitePath (L.popularAuxiliaryInput hlegal).lambda.graph)
      (hs : q.start ∈ (L.popularAuxiliaryInput hlegal).lambda.source)
      (ht : q.finish ∈ (L.popularAuxiliaryInput hlegal).lambda.target)
      (i : L.groundedInfiniteRecords) (y : V),
      q.start = .proxy i → q.finish = .old y →
      y ∈ Gamma.roof (L.frontier (L.groundedInfiniteStage i))

/-- Lemma 7.17's roof transport implies the exact strict source/target
index inequality required by Assertion 8.12.  The last step is purely
ordinal: later frontier roofs contain earlier frontier roofs, whereas a
fresh marker is outside the roof of its own frontier. -/
theorem auxiliaryStrictDescent_of_lemma717
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (H : L.Lemma717RoofTransport hlegal) :
    L.AuxiliaryStrictDescent hlegal := by
  let I := L.popularAuxiliaryInput hlegal
  intro q hs ht
  obtain ⟨y, hyTarget, hqy⟩ := I.finish_of_mem_lambda_target q ht
  have hyMarker : y ∈ L.markerSet := hyTarget.1
  let b : Stage kappa := L.markerStage ⟨y, hyMarker⟩
  have hmarker : L.marker b = some y := L.markerStage_spec ⟨y, hyMarker⟩
  have hyNotRoof : y ∉ Gamma.roof (L.frontier b) :=
    L.marker_not_mem_roof_frontier hlegal hmarker
  rcases I.start_of_mem_lambda_source q hs with
      ⟨x, hxSource, hqx⟩ | ⟨i, hqi⟩
  · have hxTerminal : x ∈ L.finiteTerminalSet :=
      L.groundedFiniteTerminalSet_subset_finiteTerminalSet hxSource
    let a : Stage kappa := L.finiteTerminalStage ⟨x, hxTerminal⟩
    have hyRoofA : y ∈ Gamma.roof (L.frontier a) := by
      exact H.finite q hs ht ⟨x, hxTerminal⟩ y hqx hqy
    have hab : b < a := by
      by_contra hnot
      have hab' : a ≤ b := le_of_not_gt hnot
      apply hyNotRoof
      rcases hab'.lt_or_eq with hablt | habeq
      · exact Gamma.roof_cut (hlegal.frontierChronology hablt) hyRoofA
      · rwa [habeq] at hyRoofA
    have htargetSubtype :
        (⟨q.finish, ht⟩ : I.lambda.target) =
          ⟨.old y, (I.mem_lambda_target_old y).2 hyTarget⟩ :=
      Subtype.ext hqy
    have hsourceSubtype :
        (⟨q.start, hs⟩ : I.lambda.source) =
          ⟨.old x, (I.mem_lambda_source_old x).2 hxSource⟩ :=
      Subtype.ext hqx
    rw [htargetSubtype, hsourceSubtype]
    exact hab
  · let a : Stage kappa := L.groundedInfiniteStage i
    have hyRoofA : y ∈ Gamma.roof (L.frontier a) := by
      exact H.proxy q hs ht i y hqi hqy
    have hab : b < a := by
      by_contra hnot
      have hab' : a ≤ b := le_of_not_gt hnot
      apply hyNotRoof
      rcases hab'.lt_or_eq with hablt | habeq
      · exact Gamma.roof_cut (hlegal.frontierChronology hablt) hyRoofA
      · rwa [habeq] at hyRoofA
    have htargetSubtype :
        (⟨q.finish, ht⟩ : I.lambda.target) =
          ⟨.old y, (I.mem_lambda_target_old y).2 hyTarget⟩ :=
      Subtype.ext hqy
    have hsourceSubtype :
        (⟨q.start, hs⟩ : I.lambda.source) =
          ⟨.proxy i, I.mem_lambda_source_proxy i⟩ :=
      Subtype.ext hqi
    rw [htargetSubtype, hsourceSubtype]
    exact hab

end KappaLadder
end DWeb
end Erdos599
