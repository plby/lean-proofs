/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingAuxiliary
import ErdosProblems.Erdos599.GroundingSelection
import ErdosProblems.Erdos599.GroundingApexOwnerAvoidance
import ErdosProblems.Erdos599.GroundingCutReachableOwnerAvoidance

/-!
# Collision controls for deferred Section 8 grounding

This file constructs the `GroundingSelection.Controls` package used while
formalizing Assertions 8.19--8.20.  A strict-prior ladder collision remembers the actual hanging
component of the limiting ladder, its strictly earlier marker provenance,
and the auxiliary trace met by the local in-fan member.  The rank is chosen
on source indices, rather than on paths.  This is sound because the deferred
auxiliary source index is injective and a joined family has at most one path
with a given source index.

The fragment exceptional class includes the literal non-apex cut-contact
class, the countable trace of the apex's own owner away from the apex, and
the cut-reachable carriers of all off-apex reference owners.
Coverage of arbitrary decoded collisions is deliberately not claimed by
`Controls`: the switch/prune compiler must classify a ladder collision as
strict-prior (or handle the equal-origin case), and must show that contact
with a deleted hanging fragment supplies such a cut contact.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

private abbrev AuxInput (L : Gamma.KappaLadder kappa)
    (hL : IsKappaHindrance L) :=
  popularAuxiliaryInput L hL.legal

private abbrev AuxPath (L : Gamma.KappaLadder kappa)
    (hL : IsKappaHindrance L) :=
  FinitePath (AuxInput L hL).lambda.graph

private abbrev AuxVertex (L : Gamma.KappaLadder kappa)
    (_hL : IsKappaHindrance L) :=
  PopularAuxiliary.Input.LambdaVertex V (infiniteRecords L)

private abbrev AuxRequest (L : Gamma.KappaLadder kappa)
    (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)) :=
  PopularGroundingBridge.Request (AuxInput L hL) S.cut

/-- A hanging limiting-ladder component with marker provenance whose full
auxiliary trace misses the current request apex. -/
structure HangingTraceCarrier
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL))
    (r : AuxRequest L hL S) (a : Ladder.Stage kappa) : Type (u + 2) where
  carrier : Gamma.DPath
  carrier_mem : carrier ∈ L.limitWarp
  carrier_hanging : PopularAuxiliary.IsHangingPath Gamma carrier
  marker_eq : L.marker a = some carrier.initial
  trace_disjoint :
    Disjoint
      (PopularSwitching.ladderTrace (AuxInput L hL) carrier)
      {PopularGroundingBridge.requestAuxVertex r}

def HasHangingTraceCarrier
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL))
    (r : AuxRequest L hL S) (a : Ladder.Stage kappa) : Prop :=
  Nonempty (HangingTraceCarrier L hL S r a)

private noncomputable def hangingTraceCarrier
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL))
    (r : AuxRequest L hL S) (a : Ladder.Stage kappa)
    (h : HasHangingTraceCarrier L hL S r a) :
    HangingTraceCarrier L hL S r a :=
  Classical.choice h

private theorem HangingTraceCarrier.carrier_eq
    {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
    {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}
    {r : AuxRequest L hL S} {a : Ladder.Stage kappa}
    (c d : HangingTraceCarrier L hL S r a) : c.carrier = d.carrier := by
  apply DWeb.IsWarp.eq_of_initial_eq Gamma
    (hL.legal.warpStages (Ladder.finalStage kappa))
    c.carrier_mem d.carrier_mem
  exact Option.some.inj (c.marker_eq.symm.trans d.marker_eq)

/-- A concrete Assertion 8.19 witness at the source index `i`.

`carrier` is the actual hanging limiting-ladder component met by the local
fan member.  Its marker provenance is stored explicitly, so the only
ordinal fact needed by pressing down is the genuine inequality
`stage < i`.  The trace-disjointness field records the source's exception
for the component through the common apex. -/
structure PriorHangingCollision
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL))
    (r : AuxRequest L hL S) (i : Stationary.Below kappa) : Type (u + 2) where
  path : AuxPath L hL
  path_mem : path ∈ (PopularGroundingBridge.requestFan S r).paths
  path_index :
    (popularAuxiliaryIndexed L hL).f
      ⟨path.start,
        (PopularGroundingBridge.requestFan S r).starts_in_source path_mem⟩ = i
  stage : Ladder.Stage kappa
  stage_lt : stage < i
  traceCarrier : HangingTraceCarrier L hL S r stage
  path_meets : path.walk.Meets
    (PopularSwitching.ladderTrace (AuxInput L hL) traceCarrier.carrier)

/-- There is a genuine prior hanging collision at this source index. -/
def HasPriorHangingCollision
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL))
    (r : AuxRequest L hL S) (i : Stationary.Below kappa) : Prop :=
  Nonempty (PriorHangingCollision L hL S r i)

private noncomputable def priorHangingCollision
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL))
    (r : AuxRequest L hL S) (i : Stationary.Below kappa)
    (h : HasPriorHangingCollision L hL S r i) :
    PriorHangingCollision L hL S r i :=
  Classical.choice h

/-- Two members of one request fan with equal source index are equal.
This is the well-definedness step behind assigning the collision rank to
the ordinal source index rather than to a chosen path. -/
theorem requestFan_path_eq_of_index_eq
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL))
    (r : AuxRequest L hL S)
    {p q : AuxPath L hL}
    (hp : p ∈ (PopularGroundingBridge.requestFan S r).paths)
    (hq : q ∈ (PopularGroundingBridge.requestFan S r).paths)
    (hindex :
      (popularAuxiliaryIndexed L hL).f
        ⟨p.start,
          (PopularGroundingBridge.requestFan S r).starts_in_source hp⟩ =
      (popularAuxiliaryIndexed L hL).f
        ⟨q.start,
          (PopularGroundingBridge.requestFan S r).starts_in_source hq⟩) :
    p = q := by
  let U := popularAuxiliaryIndexed L hL
  have hsource :
      (⟨p.start,
          (PopularGroundingBridge.requestFan S r).starts_in_source hp⟩ :
        (AuxInput L hL).lambda.source) =
      ⟨q.start,
          (PopularGroundingBridge.requestFan S r).starts_in_source hq⟩ :=
    popularAuxiliaryIndexed_sourceIndexed L hL hindex
  have hstart : p.start = q.start := congrArg Subtype.val hsource
  by_contra hpq
  have hcommon : p.start ∈ p.support ∩ q.support :=
    ⟨p.start_mem_support, hstart ▸ q.start_mem_support⟩
  have hapex : p.start = PopularGroundingBridge.requestAuxVertex r :=
    Set.mem_singleton_iff.1
      ((PopularGroundingBridge.requestFan S r).joined hp hq hpq hcommon)
  exact PopularGroundingBridge.requestAuxVertex_not_mem_source r
    (hapex ▸
      (PopularGroundingBridge.requestFan S r).starts_in_source hp)

/-- The actual ladder-collision exceptional family.  Membership says that
the (necessarily unique) member with this source index has a concrete prior
hanging collision witness. -/
def hangingLadderPaths
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL))
    (r : AuxRequest L hL S) : Set (AuxPath L hL) :=
  {p | ∃ hp : p ∈ (PopularGroundingBridge.requestFan S r).paths,
    HasPriorHangingCollision L hL S r
      ((popularAuxiliaryIndexed L hL).f
        ⟨p.start,
          (PopularGroundingBridge.requestFan S r).starts_in_source hp⟩)}

/-- A concrete prior collision places the corresponding in-fan member in
the ladder exceptional family. -/
theorem mem_hangingLadderPaths_of_collision
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL))
    (r : AuxRequest L hL S) (i : Stationary.Below kappa)
    (w : PriorHangingCollision L hL S r i) :
    w.path ∈ hangingLadderPaths L hL S r := by
  refine ⟨w.path_mem, ?_⟩
  rw [w.path_index]
  exact ⟨w⟩

/-- The regressive rank chosen from the unique collision at an index. -/
noncomputable def hangingLadderRank
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL))
    (r : AuxRequest L hL S) (i : Stationary.Below kappa) :
    Stationary.Below kappa := by
  classical
  exact if h : HasPriorHangingCollision L hL S r i then
    (priorHangingCollision L hL S r i h).stage
  else i

/-- The countable auxiliary trace selected at a collision rank. -/
noncomputable def hangingLadderTrace
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL))
    (r : AuxRequest L hL S) (i : Stationary.Below kappa) :
    Set (AuxVertex L hL) := by
  classical
  exact if h : HasHangingTraceCarrier L hL S r i then
    PopularSwitching.ladderTrace (AuxInput L hL)
      (hangingTraceCarrier L hL S r i h).carrier
  else ∅

private theorem hangingLadderRank_regressive
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL))
    (r : AuxRequest L hL S) :
    Stationary.IsRegressiveOn
      (Popular.initialIndicesOf (popularAuxiliaryIndexed L hL)
        (PopularSwitching.restrictPaths
          (PopularGroundingBridge.requestFan S r)
          (hangingLadderPaths L hL S r)).paths
        (PopularSwitching.restrictPaths
          (PopularGroundingBridge.requestFan S r)
          (hangingLadderPaths L hL S r)).starts_in_source)
      (hangingLadderRank L hL S r) := by
  rintro i ⟨p, hp, hpi⟩
  obtain ⟨hpFan, hpCollision⟩ := hp
  obtain ⟨hpFan', hcollision⟩ := hpCollision
  change (popularAuxiliaryIndexed L hL).f
    ⟨p.start,
      (PopularGroundingBridge.requestFan S r).starts_in_source hpFan⟩ = i at hpi
  have hindex :
      (popularAuxiliaryIndexed L hL).f
        ⟨p.start,
          (PopularGroundingBridge.requestFan S r).starts_in_source hpFan'⟩ = i := by
    simpa only using hpi
  rw [hindex] at hcollision
  simp only [hangingLadderRank, dif_pos hcollision]
  exact (priorHangingCollision L hL S r i hcollision).stage_lt

private theorem hangingLadderTrace_countable
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL))
    (r : AuxRequest L hL S) (i : Stationary.Below kappa) :
    (hangingLadderTrace L hL S r i).Countable := by
  classical
  by_cases h : HasHangingTraceCarrier L hL S r i
  · simp only [hangingLadderTrace, dif_pos h]
    exact PopularSwitching.ladderTrace_countable _ _
  · simp [hangingLadderTrace, h]

private theorem hangingLadderTrace_disjoint_apex
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL))
    (r : AuxRequest L hL S) (i : Stationary.Below kappa) :
    Disjoint (hangingLadderTrace L hL S r i)
      {PopularGroundingBridge.requestAuxVertex r} := by
  classical
  by_cases h : HasHangingTraceCarrier L hL S r i
  · simp only [hangingLadderTrace, dif_pos h]
    exact (hangingTraceCarrier L hL S r i h).trace_disjoint
  · simp [hangingLadderTrace, h]

private theorem hangingLadderPaths_meets_aux
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL))
    (r : AuxRequest L hL S) (p : AuxPath L hL)
    (hpFan : p ∈ (PopularGroundingBridge.requestFan S r).paths)
    (hpCollision : p ∈ hangingLadderPaths L hL S r) :
    ∃ x ∈ hangingLadderTrace L hL S r
        (hangingLadderRank L hL S r
          ((popularAuxiliaryIndexed L hL).f
            ⟨p.start,
              (PopularGroundingBridge.requestFan S r).starts_in_source hpFan⟩)),
      x ∈ p.support := by
  obtain ⟨hpFan', hcollision⟩ := hpCollision
  let i : Stationary.Below kappa :=
    (popularAuxiliaryIndexed L hL).f
      ⟨p.start,
        (PopularGroundingBridge.requestFan S r).starts_in_source hpFan'⟩
  have hindex :
      (popularAuxiliaryIndexed L hL).f
        ⟨p.start,
          (PopularGroundingBridge.requestFan S r).starts_in_source hpFan⟩ = i := by
    rfl
  rw [hindex]
  have hcollision_i : HasPriorHangingCollision L hL S r i := hcollision
  let w := priorHangingCollision L hL S r i hcollision_i
  have hwp : w.path = p := by
    apply requestFan_path_eq_of_index_eq L hL S r w.path_mem hpFan'
    exact w.path_index.trans rfl
  have htrace : HasHangingTraceCarrier L hL S r w.stage :=
    ⟨w.traceCarrier⟩
  let c := hangingTraceCarrier L hL S r w.stage htrace
  have hc : c.carrier = w.traceCarrier.carrier := c.carrier_eq w.traceCarrier
  have hmeet : p.walk.Meets
      (PopularSwitching.ladderTrace (AuxInput L hL) c.carrier) := by
    rw [hc, ← hwp]
    exact w.path_meets
  have hrank : hangingLadderRank L hL S r i = w.stage := by
    simp only [hangingLadderRank, dif_pos hcollision_i]
    rfl
  rw [hrank]
  simp only [hangingLadderTrace, dif_pos htrace]
  change p.walk.Meets
    (PopularSwitching.ladderTrace (AuxInput L hL) c.carrier) at hmeet
  obtain ⟨x, hxp, hxc⟩ := hmeet
  exact ⟨x, hxc, hxp⟩

/-- The Assertion 8.20 exceptional family: paths making a non-apex contact
with the popular cut.  The fragment decoder supplies this exact witness
when a path meets a deleted hanging fragment. -/
def hangingFragmentPaths
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL))
    (r : AuxRequest L hL S) : Set (AuxPath L hL) :=
  {p | p.walk.Meets
    (S.cut \ {PopularGroundingBridge.requestAuxVertex r})}

/-- The concrete control package for strict-prior ladder collisions and
non-apex cut contacts. -/
noncomputable def selectionControls
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)) :
    GroundingSelection.Controls S where
  hangingLadder := hangingLadderPaths L hL S
  hangingFragment := fun r ↦ hangingFragmentPaths L hL S r ∪
    (GroundingApexOwnerAvoidance.collidingPaths r ∪
      GroundingCutReachableOwnerAvoidance.collidingPaths S r)
  ladderRank := hangingLadderRank L hL S
  ladderTrace := hangingLadderTrace L hL S
  ladderRank_regressive := hangingLadderRank_regressive L hL S
  ladderTrace_countable := hangingLadderTrace_countable L hL S
  ladderTrace_disjoint_apex := hangingLadderTrace_disjoint_apex L hL S
  hangingLadder_meets := by
    intro r p hp
    exact hangingLadderPaths_meets_aux L hL S r p hp.1 hp.2
  fragmentIndices_nonstationary := by
    intro r
    have hcut : ¬ Stationary.IsStationaryBelow kappa
        (GroundingSelection.restrictedIndices (popularAuxiliaryIndexed L hL)
          (PopularGroundingBridge.requestFan S r) (hangingFragmentPaths L hL S r)) := by
      apply PopularSwitching.initialIndices_nonstationary_of_all_meet_notStronglyPopular
        (popularAuxiliaryIndexed L hL)
        (PopularSwitching.restrictPaths
          (PopularGroundingBridge.requestFan S r) (hangingFragmentPaths L hL S r))
        Set.disjoint_sdiff_left
      · intro p hp
        exact hp.2
      · exact GroundingSelection.not_stronglyPopular_of_subset_cut S Set.sdiff_subset
    have hapex := GroundingApexOwnerAvoidance.collidingPaths_indices_nonstationary S r
    have hreach := GroundingCutReachableOwnerAvoidance.collidingPaths_indices_nonstationary S r
    have howner : ¬ Stationary.IsStationaryBelow kappa
        (GroundingSelection.restrictedIndices (popularAuxiliaryIndexed L hL)
          (PopularGroundingBridge.requestFan S r)
          (GroundingApexOwnerAvoidance.collidingPaths r ∪
            GroundingCutReachableOwnerAvoidance.collidingPaths S r)) := by
      intro hstationary
      apply GroundingSelection.not_isStationaryBelow_union
        hL.legal.regular hL.legal.uncountable hapex hreach
      exact hstationary.mono (GroundingControlledAssembly.restrictedIndices_union_subset
        (popularAuxiliaryIndexed L hL) (PopularGroundingBridge.requestFan S r)
        (GroundingApexOwnerAvoidance.collidingPaths r)
        (GroundingCutReachableOwnerAvoidance.collidingPaths S r))
    intro hstationary
    apply GroundingSelection.not_isStationaryBelow_union
      hL.legal.regular hL.legal.uncountable hcut howner
    exact hstationary.mono (GroundingControlledAssembly.restrictedIndices_union_subset
      (popularAuxiliaryIndexed L hL) (PopularGroundingBridge.requestFan S r)
      (hangingFragmentPaths L hL S r) (GroundingApexOwnerAvoidance.collidingPaths r ∪
        GroundingCutReachableOwnerAvoidance.collidingPaths S r))

/-- Deferred bookkeeping packages the two concrete exceptional classes for
every popular separator, with no constructor hypothesis.  This theorem does
not assert coverage of arbitrary decoded collisions. -/
theorem hasSelectionControls
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L) :
    ∀ S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL),
      Nonempty (GroundingSelection.Controls S) := by
  intro S
  exact ⟨selectionControls L hL S⟩

end Deferred
end KappaLadder
end DWeb
end Erdos599
