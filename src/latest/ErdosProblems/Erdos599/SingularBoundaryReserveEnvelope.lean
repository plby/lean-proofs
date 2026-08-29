/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import Mathlib.Order.FixedPoints
import ErdosProblems.Erdos599.SingularBoundaryFutureSafeSelection

/-!
# Monotone reserve envelopes for boundary-safe singular batches

The reserve needed by a simultaneous singular construction is normally
computed from all columns and all earlier histories.  This file separates
the order-theoretic closing-up from the graph-theoretic selection problem.

For an arbitrary index type `I` (which may already encode a column/history
pair), `leastClosedEnvelope` is the genuine Knaster--Tarski least fixed point
of `E ↦ seed ∪ step E`.  It contains the seed and is closed under `step`.

An envelope helps with boundary future safety in exactly one direction.  If
the batches have already been selected safely for the envelope and their
final batch-dependent reserves lie below it, reserve shrinking gives a
simultaneous joint selection for the final reserves.  Conversely, every
simultaneous joint selection is an envelope selection by taking the final
reserves themselves as the envelope.  Thus the fixed point settles all set
closure bookkeeping, but does not manufacture a boundary-safe batch.

The last theorem supplies those batches unconditionally when every ambient
residual source is below the induction cardinal.  The only remaining case is
therefore the genuine strict-large graph selection problem, not a failure of
the envelope construction.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularBoundaryReserveEnvelope

open SingularBoundaryFutureSafeSelection SingularSafeBatch

universe u v

variable {V : Type u} {I : Type v}

/-- A reserve envelope for every column/history index. -/
abbrev ReserveProfile (I : Type v) (V : Type u) := I → Set V

/-- Adjoin a fixed seed profile to one application of a monotone reserve
operator. -/
def seededStep (seed : ReserveProfile I V)
    (step : ReserveProfile I V →o ReserveProfile I V) :
    ReserveProfile I V →o ReserveProfile I V where
  toFun E i := seed i ∪ step E i
  monotone' := by
    intro E F hEF i x hx
    exact hx.elim Or.inl (fun hxStep ↦ Or.inr (step.monotone hEF i hxStep))

/-- The least simultaneous envelope containing `seed` and closed under the
monotone reserve operator `step`. -/
def leastClosedEnvelope (seed : ReserveProfile I V)
    (step : ReserveProfile I V →o ReserveProfile I V) :
    ReserveProfile I V :=
  (seededStep seed step).lfp

/-- The least envelope is a genuine fixed point. -/
theorem leastClosedEnvelope_fixed
    (seed : ReserveProfile I V)
    (step : ReserveProfile I V →o ReserveProfile I V) :
    seededStep seed step (leastClosedEnvelope seed step) =
      leastClosedEnvelope seed step :=
  (seededStep seed step).map_lfp

/-- Every seed reserve is contained in the least closed envelope. -/
theorem seed_subset_leastClosedEnvelope
    (seed : ReserveProfile I V)
    (step : ReserveProfile I V →o ReserveProfile I V) :
    seed ≤ leastClosedEnvelope seed step := by
  intro i x hx
  have hfixed := congrFun (leastClosedEnvelope_fixed seed step) i
  rw [← hfixed]
  exact Or.inl hx

/-- One further application of the reserve operator is also absorbed by the
least closed envelope. -/
theorem step_le_leastClosedEnvelope
    (seed : ReserveProfile I V)
    (step : ReserveProfile I V →o ReserveProfile I V) :
    step (leastClosedEnvelope seed step) ≤ leastClosedEnvelope seed step := by
  intro i x hx
  have hfixed := congrFun (leastClosedEnvelope_fixed seed step) i
  rw [← hfixed]
  exact Or.inr hx

/-- Minimality among profiles which contain the seed and are closed under
the reserve operator. -/
theorem leastClosedEnvelope_le
    (seed : ReserveProfile I V)
    (step : ReserveProfile I V →o ReserveProfile I V)
    {E : ReserveProfile I V}
    (hseed : seed ≤ E) (hstep : step E ≤ E) :
    leastClosedEnvelope seed step ≤ E := by
  apply (seededStep seed step).lfp_le
  intro i x hx
  exact hx.elim (fun h ↦ hseed i h) (fun h ↦ hstep i h)

/-! ## The concrete competitor operator -/

/-- Apply competitor closure for one simultaneous path family at every
column/history index.  Monotonicity is exactly monotonicity in the requested
source set; no row-selection choice occurs in this operator. -/
def competitorOperator (G : DWeb V) (W : Set G.DPath) :
    ReserveProfile I V →o ReserveProfile I V where
  toFun E i := G.competitorClosure W (E i)
  monotone' := by
    intro E F hEF i
    exact G.competitorClosure_mono_sources (hEF i)

/-- The canonical least competitor envelope for an indexed seed profile. -/
def leastCompetitorEnvelope
    (G : DWeb V) (W : Set G.DPath) (seed : ReserveProfile I V) :
    ReserveProfile I V :=
  leastClosedEnvelope seed (competitorOperator G W)

/-- Every indexed seed lies in the canonical competitor envelope. -/
theorem seed_subset_leastCompetitorEnvelope
    (G : DWeb V) (W : Set G.DPath) (seed : ReserveProfile I V) :
    seed ≤ leastCompetitorEnvelope G W seed :=
  seed_subset_leastClosedEnvelope seed (competitorOperator G W)

/-- The canonical envelope is closed under all competitors of `W`. -/
theorem competitorClosure_leastCompetitorEnvelope
    (G : DWeb V) (W : Set G.DPath) (seed : ReserveProfile I V) (i : I) :
    G.competitorClosure W (leastCompetitorEnvelope G W seed i) ⊆
      leastCompetitorEnvelope G W seed i :=
  step_le_leastClosedEnvelope seed (competitorOperator G W) i

/-- Minimality in the concrete pointwise form used by row constructions. -/
theorem leastCompetitorEnvelope_le
    (G : DWeb V) (W : Set G.DPath) (seed E : ReserveProfile I V)
    (hseed : seed ≤ E)
    (hclosed : ∀ i, G.competitorClosure W (E i) ⊆ E i) :
    leastCompetitorEnvelope G W seed ≤ E := by
  apply leastClosedEnvelope_le seed (competitorOperator G W) hseed
  exact hclosed

/-- Knaster--Tarski's least envelope agrees pointwise with the existing
explicit omega competitor closure.  Hence all previously proved cardinal
bounds for omega closure apply to this fixed-point presentation. -/
theorem leastCompetitorEnvelope_eq_omegaCompetitorClosure
    (G : DWeb V) (W : Set G.DPath) (seed : ReserveProfile I V) :
    leastCompetitorEnvelope G W seed =
      fun i ↦ G.omegaCompetitorClosure W (seed i) := by
  apply le_antisymm
  · apply leastCompetitorEnvelope_le G W seed
    · intro i
      exact G.subset_omegaCompetitorClosure W (seed i)
    · intro i
      exact G.competitorClosure_omega_subset W (seed i)
  · intro i
    apply G.omegaCompetitorClosure_minimal
    · exact seed_subset_leastCompetitorEnvelope G W seed i
    · exact competitorClosure_leastCompetitorEnvelope G W seed i

/-- Exact cardinal preservation for the fixed-point envelope, inherited from
the omega-closure calculation. -/
theorem mk_leastCompetitorEnvelope_eq
    (G : DWeb V) (W : Set G.DPath) (seed : ReserveProfile I V) (i : I)
    {rho : Cardinal.{u}}
    (hseed : #(seed i) = rho) (hrho : aleph0 ≤ rho)
    (hstage : ∀ n,
      #(G.competitorIterate W (seed i) n) ≤ rho) :
    #(leastCompetitorEnvelope G W seed i) = rho := by
  rw [leastCompetitorEnvelope_eq_omegaCompetitorClosure]
  exact G.mk_omegaCompetitorClosure_eq W (seed i) hseed hrho hstage

/-! ## Simultaneous graph selections -/

/-- A boundary-future-safe batch in every column/history, for the final
batch-dependent reserve rule. -/
structure SimultaneousJointSelection
    (H : DWeb V) (current : I → Set V)
    (reserveAfter : ∀ i, FullSourceSafeBatch H (current i) → Set V) where
  batch : ∀ i, FullSourceSafeBatch H (current i)
  futureSafe : ∀ i,
    BoundaryFutureSafeFor (batch i) (reserveAfter i (batch i))

/-- A simultaneous selection certified against a possibly larger provisional
envelope. -/
structure SimultaneousEnvelopeSelection
    (H : DWeb V) (current : I → Set V)
    (reserveAfter : ∀ i, FullSourceSafeBatch H (current i) → Set V) where
  batch : ∀ i, FullSourceSafeBatch H (current i)
  envelope : ReserveProfile I V
  reserve_subset : ∀ i, reserveAfter i (batch i) ⊆ envelope i
  envelopeSafe : ∀ i, BoundaryFutureSafeFor (batch i) (envelope i)

namespace SimultaneousEnvelopeSelection

variable {H : DWeb V} {current : I → Set V}
variable {reserveAfter : ∀ i, FullSourceSafeBatch H (current i) → Set V}

/-- Shrink every provisional envelope to the final batch-dependent reserve. -/
def toJoint
    (hNoEnter : H.NoEdgeEnters H.source)
    (S : SimultaneousEnvelopeSelection H current reserveAfter) :
    SimultaneousJointSelection H current reserveAfter where
  batch := S.batch
  futureSafe i := BoundaryFutureSafeFor.mono hNoEnter
    (S.batch i) (S.envelopeSafe i) (S.reserve_subset i)

end SimultaneousEnvelopeSelection

namespace SimultaneousJointSelection

variable {H : DWeb V} {current : I → Set V}
variable {reserveAfter : ∀ i, FullSourceSafeBatch H (current i) → Set V}

/-- Every joint selection is tautologically an envelope selection for its
own final reserve profile. -/
def toEnvelope
    (S : SimultaneousJointSelection H current reserveAfter) :
    SimultaneousEnvelopeSelection H current reserveAfter where
  batch := S.batch
  envelope i := reserveAfter i (S.batch i)
  reserve_subset _ := Set.Subset.rfl
  envelopeSafe := S.futureSafe

end SimultaneousJointSelection

/-- The existence of a dominating safe envelope is exactly equivalent to
the original simultaneous joint-selection problem.  Knaster--Tarski closes
sets, but this equivalence shows that it cannot by itself create the graph
batches certified safe for the resulting envelope. -/
theorem nonempty_simultaneousEnvelopeSelection_iff_joint
    {H : DWeb V} (hNoEnter : H.NoEdgeEnters H.source)
    {current : I → Set V}
    {reserveAfter : ∀ i, FullSourceSafeBatch H (current i) → Set V} :
    Nonempty (SimultaneousEnvelopeSelection H current reserveAfter) ↔
      Nonempty (SimultaneousJointSelection H current reserveAfter) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.toJoint hNoEnter⟩
  · rintro ⟨S⟩
    exact ⟨S.toEnvelope⟩

/-- A least closed reserve envelope compiles to the final simultaneous
selection once lower graph theory has actually supplied batches safe for
that envelope and the final requirements lie below it. -/
def jointOfLeastClosedEnvelope
    {H : DWeb V} (hNoEnter : H.NoEdgeEnters H.source)
    {current : I → Set V}
    {reserveAfter : ∀ i, FullSourceSafeBatch H (current i) → Set V}
    (seed : ReserveProfile I V)
    (step : ReserveProfile I V →o ReserveProfile I V)
    (batch : ∀ i, FullSourceSafeBatch H (current i))
    (hreserve : ∀ i,
      reserveAfter i (batch i) ⊆ leastClosedEnvelope seed step i)
    (hsafe : ∀ i,
      BoundaryFutureSafeFor (batch i) (leastClosedEnvelope seed step i)) :
    SimultaneousJointSelection H current reserveAfter :=
  (show SimultaneousEnvelopeSelection H current reserveAfter from
    { batch := batch
      envelope := leastClosedEnvelope seed step
      reserve_subset := hreserve
      envelopeSafe := hsafe }).toJoint hNoEnter

/-! ## The unconditional lower-source branch -/

/-- If the whole ambient residual source lies below `kappa`, lower induction
simultaneously supplies a boundary-safe full linkage in every indexed
column/history.  No safe-envelope existence premise is assumed. -/
theorem exists_simultaneousJointSelection_of_source_below
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    {H : DWeb V} (hH : H.IsUnhindered)
    (hsource : #H.source < kappa)
    (current : I → Set V)
    (hcurrent : ∀ i, current i ⊆ H.source)
    (reserveAfter : ∀ i, FullSourceSafeBatch H (current i) → Set V)
    (hreserve : ∀ i B, reserveAfter i B ⊆ H.source) :
    Nonempty (SimultaneousJointSelection H current reserveAfter) := by
  have hchoose : ∀ i,
      Nonempty (JointBoundaryFutureSafeSelection H (current i)
        (reserveAfter i)) := by
    intro i
    exact exists_jointBoundaryFutureSafeSelection_of_source_below
      hlower hH hsource (hcurrent i) (reserveAfter i) (hreserve i)
  let J : ∀ i, JointBoundaryFutureSafeSelection H (current i)
      (reserveAfter i) := fun i ↦ Classical.choice (hchoose i)
  exact ⟨
    { batch := fun i ↦ (J i).batch
      futureSafe := fun i ↦ (J i).futureSafe }⟩

/-- The other lower-induction branch works simultaneously as well: each
indexed current set may have its own smaller scale, provided the complement
already has a target linkage.  This is the exact positive strict-source
case; it does not assume safety of a provisional envelope. -/
theorem exists_simultaneousJointSelection_of_complement_linkable
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    {H : DWeb V} (hH : H.IsUnhindered)
    (rho : I → Cardinal.{u}) (hrho : ∀ i, rho i < kappa)
    (current : I → Set V)
    (hcurrent : ∀ i, current i ⊆ H.source)
    (hcurrentCard : ∀ i, #(current i) = rho i)
    (hcomplement : ∀ i, ∃ F : Set H.DPath,
      IsLinkageBetween H (H.source \ current i) H.target F)
    (reserveAfter : ∀ i, FullSourceSafeBatch H (current i) → Set V)
    (hreserve : ∀ i B, reserveAfter i B ⊆ H.source) :
    Nonempty (SimultaneousJointSelection H current reserveAfter) := by
  have hchoose : ∀ i,
      Nonempty (JointBoundaryFutureSafeSelection H (current i)
        (reserveAfter i)) := by
    intro i
    exact exists_jointBoundaryFutureSafeSelection_of_complement_linkable
      hlower (hrho i) hH (hcurrent i) (hcurrentCard i)
        (hcomplement i) (reserveAfter i) (hreserve i)
  let J : ∀ i, JointBoundaryFutureSafeSelection H (current i)
      (reserveAfter i) := fun i ↦ Classical.choice (hchoose i)
  exact ⟨
    { batch := fun i ↦ (J i).batch
      futureSafe := fun i ↦ (J i).futureSafe }⟩

#print axioms leastClosedEnvelope_fixed
#print axioms seed_subset_leastClosedEnvelope
#print axioms step_le_leastClosedEnvelope
#print axioms leastClosedEnvelope_le
#print axioms competitorClosure_leastCompetitorEnvelope
#print axioms leastCompetitorEnvelope_le
#print axioms leastCompetitorEnvelope_eq_omegaCompetitorClosure
#print axioms mk_leastCompetitorEnvelope_eq
#print axioms nonempty_simultaneousEnvelopeSelection_iff_joint
#print axioms jointOfLeastClosedEnvelope
#print axioms exists_simultaneousJointSelection_of_source_below
#print axioms exists_simultaneousJointSelection_of_complement_linkable

end SingularBoundaryReserveEnvelope
end CardinalInduction
end Erdos599
