/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCausalHammockRows
import ErdosProblems.Erdos599.HalfwayGlobalReferenceClosureOfStages
import ErdosProblems.Erdos599.HalfwayDeferredStageIntervalBridge

/-!
# Joint causal reference and hammock rows

This is the source-shaped closing recursion needed before Assertion 9.31.
At an ordinary stage `a`, the row contains

* the maximal-up-to-`kappa` and maximal-up-to-`kappa^+` hammocks selected
  against the full accumulated reference `Y_a`; and
* every member of `Y_a` which meets a strictly earlier row.

The preferred-marker scheduler subsequently roofs every inserted vertex.
The second clause is deliberately causal: if a path first meets the row
born at `a`, its successor extension is absorbed in the row born at
`a + 1`.  Consequently the union of the rows is closed under the genuine
limiting warp.  No finite-character hypothesis and no pre-existing global
closed reservoir occur in the construction.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating Ladder
open CardinalInduction.RegularRows

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace CausalReferenceHammockRows

abbrev priorCarrier
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) : Set V :=
  CausalHammockRows.priorCarrier a prior

/-- Full stage-reference components which already meet a strictly earlier
row. -/
def referenceIncrement
    (Gamma : DWeb V) (kappa : Cardinal.{u})
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) : Set V :=
  let L := UnroofedHalfwayRowLadder.priorLadder
    Gamma a prior
  meetingVertices Gamma (L.warpAt a) (priorCarrier a prior)

/-- One genuine source-closing increment: hammocks plus contacted reference
components. -/
def increment
    (Gamma : DWeb V) (kappa : Cardinal.{u})
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) : Set V :=
  CausalHammockRows.hammockIncrement Gamma kappa a prior ∪
    referenceIncrement Gamma kappa a prior

theorem mk_referenceIncrement_le_succ
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) :
    #(referenceIncrement Gamma kappa a prior) ≤ succ kappa := by
  unfold referenceIncrement
  apply mk_meetingVertices_le Gamma _ _
  · exact UnroofedHalfwayRowLadder.core_warpAt_isWarp_of_normalized
        Gamma hGamma (succ kappa)
        (CardinalInduction.RegularRows.CausalRegular.preferredOfPrior a prior) a
  · exact hkappa.trans (le_succ kappa)
  · exact CausalHammockRows.mk_priorCarrier_le_succ hkappa a prior

theorem mk_increment_le_succ
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) :
    #(increment Gamma kappa a prior) ≤ succ kappa := by
  unfold increment
  apply (Cardinal.mk_union_le _ _).trans
  exact Cardinal.add_le_of_le (hkappa.trans (le_succ kappa))
    (CausalHammockRows.mk_hammockIncrement_le_succ hkappa a prior)
    (mk_referenceIncrement_le_succ hkappa hGamma a prior)

/-- The simultaneous causal row rule. -/
def rule (Gamma : DWeb V) (kappa : Cardinal.{u})
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized) :
    CausalRowRule (succ kappa) V where
  nextRow a prior := increment Gamma kappa a prior
  nextRow_mk_le a prior := mk_increment_le_succ hkappa hGamma a prior

def rowAt (Gamma : DWeb V) (kappa : Cardinal.{u})
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (a : Ladder.Stage (succ kappa)) : Set V :=
  ((rule Gamma kappa hkappa hGamma).state
    (hkappa.trans (le_succ kappa)) a).row

def closedAt (Gamma : DWeb V) (kappa : Cardinal.{u})
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (a : Ladder.Stage (succ kappa)) : Set V :=
  ⋃ b : Set.Iic a, rowAt Gamma kappa hkappa hGamma b.1

def globalCarrier (Gamma : DWeb V) (kappa : Cardinal.{u})
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized) : Set V :=
  ((rule Gamma kappa hkappa hGamma).rowSystem
    (hkappa.trans (le_succ kappa))).carrier

/-- The deferred-bookkeeping ladder driven by the actual causal rows. -/
def finalLadder (Gamma : DWeb V) (kappa : Cardinal.{u})
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized) :
    Gamma.KappaLadder (succ kappa) :=
  UnroofedHalfwayRowLadder.deferred Gamma (succ kappa)
    ((rule Gamma kappa hkappa hGamma).preferred
      (hkappa.trans (le_succ kappa)))

theorem rowAt_mk_le_succ
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (a : Ladder.Stage (succ kappa)) :
    #(rowAt Gamma kappa hkappa hGamma a) ≤ succ kappa :=
  ((rule Gamma kappa hkappa hGamma).state
    (hkappa.trans (le_succ kappa)) a).row_mk_le

theorem globalCarrier_mk_le_succ
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized) :
    #(globalCarrier Gamma kappa hkappa hGamma) ≤ succ kappa :=
  ((rule Gamma kappa hkappa hGamma).rowSystem
    (hkappa.trans (le_succ kappa))).mk_carrier_le
      (hkappa.trans (le_succ kappa))

theorem closedAt_mono
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized) :
    Monotone (closedAt Gamma kappa hkappa hGamma) := by
  intro a b hab x hx
  obtain ⟨c, hxc⟩ := Set.mem_iUnion.1 hx
  exact Set.mem_iUnion.2 ⟨⟨c.1, c.2.trans hab⟩, hxc⟩

theorem rowAt_subset_globalCarrier
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (a : Ladder.Stage (succ kappa)) :
    rowAt Gamma kappa hkappa hGamma a ⊆
      globalCarrier Gamma kappa hkappa hGamma :=
  ((rule Gamma kappa hkappa hGamma).rowSystem
      (hkappa.trans (le_succ kappa))).row_subset_carrier a

theorem iUnion_closedAt_eq_globalCarrier
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized) :
    (⋃ a, closedAt Gamma kappa hkappa hGamma a) =
      globalCarrier Gamma kappa hkappa hGamma := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, hxa⟩ := Set.mem_iUnion.1 hx
    obtain ⟨b, hxb⟩ := Set.mem_iUnion.1 hxa
    exact rowAt_subset_globalCarrier hkappa hGamma b.1 hxb
  · intro hx
    change x ∈ ⋃ a, rowAt Gamma kappa hkappa hGamma a at hx
    obtain ⟨a, hxa⟩ := Set.mem_iUnion.1 hx
    exact Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2
      ⟨⟨a, show a ≤ a from le_rfl⟩, hxa⟩⟩

/-- Prefix-causality identifies the temporary stage reference and frontier
with the final deferred ladder geometry. -/
theorem prior_geometry_eq_final
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (a : Ladder.Stage (succ kappa)) :
    let prior := fun b (_hba : b < a) ↦
      (rule Gamma kappa hkappa hGamma).state
        (hkappa.trans (le_succ kappa)) b
    (UnroofedHalfwayRowLadder.priorLadder
        Gamma a prior).warpAt a =
        (finalLadder Gamma kappa hkappa hGamma).warpAt a ∧
      (UnroofedHalfwayRowLadder.priorLadder
        Gamma a prior).frontier a =
        (finalLadder Gamma kappa hkappa hGamma).frontier a := by
  dsimp only
  let Q := rule Gamma kappa hkappa hGamma
  let hsucc : aleph0 ≤ succ kappa := hkappa.trans (le_succ kappa)
  have hpref : ∀ b : Ladder.Stage (succ kappa), b < a →
      CardinalInduction.RegularRows.CausalRegular.preferredOfPrior a
          (fun c _hca ↦ Q.state hsucc c) b = Q.preferred hsucc b := by
    intro b hba
    simp only [CardinalInduction.RegularRows.CausalRegular.preferredOfPrior,
      dif_pos hba, CausalRowRule.preferred]
  have hwarp :=
    UnroofedHalfwayRowLadder.core_warpAt_eq_of_forall_lt
      Gamma
      (CardinalInduction.RegularRows.CausalRegular.preferredOfPrior a
        (fun c _hca ↦ Q.state hsucc c))
      (Q.preferred hsucc) a hpref
  have hfrontier :=
    UnroofedHalfwayRowLadder.core_frontier_eq_of_forall_lt
      Gamma
      (CardinalInduction.RegularRows.CausalRegular.preferredOfPrior a
        (fun c _hca ↦ Q.state hsucc c))
      (Q.preferred hsucc) a hpref
  constructor
  · change
      (UnroofedHalfwayRowLadder.core Gamma (succ kappa)
        (CardinalInduction.RegularRows.CausalRegular.preferredOfPrior a
          (fun c _hca ↦ Q.state hsucc c))).warpAt a = _
    simpa only [Q, hsucc, finalLadder,
      UnroofedHalfwayRowLadder.deferred,
      DWeb.KappaLadder.Deferred.withValidBookkeeping,
      DWeb.KappaLadder.warpAt] using hwarp
  · change
      (UnroofedHalfwayRowLadder.core Gamma (succ kappa)
        (CardinalInduction.RegularRows.CausalRegular.preferredOfPrior a
          (fun c _hca ↦ Q.state hsucc c))).frontier a = _
    simpa only [Q, hsucc, finalLadder,
      UnroofedHalfwayRowLadder.deferred,
      DWeb.KappaLadder.Deferred.withValidBookkeeping,
      DWeb.KappaLadder.frontier, DWeb.KappaLadder.stageWeb,
      DWeb.KappaLadder.warpAt] using hfrontier

theorem increment_eq_final
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (a : Ladder.Stage (succ kappa)) :
    let prior := fun b (_hba : b < a) ↦
      (rule Gamma kappa hkappa hGamma).state
        (hkappa.trans (le_succ kappa)) b
    increment Gamma kappa a prior =
      (allHammockVertices Gamma
          ((finalLadder Gamma kappa hkappa hGamma).warpAt a) kappa
          (priorCarrier a prior)
          (Gamma.strictRoof
            ((finalLadder Gamma kappa hkappa hGamma).frontier a))
          (Gamma.roof
            ((finalLadder Gamma kappa hkappa hGamma).frontier a)) ∪
        allHammockVertices Gamma
          ((finalLadder Gamma kappa hkappa hGamma).warpAt a) (succ kappa)
          (priorCarrier a prior)
          (Gamma.strictRoof
            ((finalLadder Gamma kappa hkappa hGamma).frontier a))
          (Gamma.roof
            ((finalLadder Gamma kappa hkappa hGamma).frontier a))) ∪
        meetingVertices Gamma
          ((finalLadder Gamma kappa hkappa hGamma).warpAt a)
          (priorCarrier a prior) := by
  dsimp only
  dsimp only [increment, CausalHammockRows.hammockIncrement,
    referenceIncrement]
  rw [(prior_geometry_eq_final (Gamma := Gamma) (kappa := kappa)
      hkappa hGamma a).1,
    (prior_geometry_eq_final (Gamma := Gamma) (kappa := kappa)
      hkappa hGamma a).2]

/-- The actual row contains the stage-reference component of every path
which contacts a strict-prior row. -/
theorem contacted_reference_subset_rowAt
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (a : Ladder.Stage (succ kappa)) :
    meetingVertices Gamma
        ((finalLadder Gamma kappa hkappa hGamma).warpAt a)
        (priorCarrier a (fun b _hba ↦
          (rule Gamma kappa hkappa hGamma).state
            (hkappa.trans (le_succ kappa)) b)) ⊆
      rowAt Gamma kappa hkappa hGamma a := by
  change _ ⊆ ((rule Gamma kappa hkappa hGamma).state
    (hkappa.trans (le_succ kappa)) a).row
  rw [CausalRowRule.state_row_eq]
  change _ ⊆ increment Gamma kappa a _
  rw [increment_eq_final hkappa hGamma a]
  exact Set.subset_union_right

theorem selectedHammocks_subset_rowAt
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (a : Ladder.Stage (succ kappa)) :
    allHammockVertices Gamma
        ((finalLadder Gamma kappa hkappa hGamma).warpAt a) kappa
        (priorCarrier a (fun b _hba ↦
          (rule Gamma kappa hkappa hGamma).state
            (hkappa.trans (le_succ kappa)) b))
        (Gamma.strictRoof
          ((finalLadder Gamma kappa hkappa hGamma).frontier a))
        (Gamma.roof
          ((finalLadder Gamma kappa hkappa hGamma).frontier a)) ⊆
      rowAt Gamma kappa hkappa hGamma a := by
  change _ ⊆ ((rule Gamma kappa hkappa hGamma).state
    (hkappa.trans (le_succ kappa)) a).row
  rw [CausalRowRule.state_row_eq]
  change _ ⊆ increment Gamma kappa a _
  rw [increment_eq_final hkappa hGamma a]
  exact Set.subset_union_left.trans Set.subset_union_left

theorem selectedHammocksSucc_subset_rowAt
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (a : Ladder.Stage (succ kappa)) :
    allHammockVertices Gamma
        ((finalLadder Gamma kappa hkappa hGamma).warpAt a) (succ kappa)
        (priorCarrier a (fun b _hba ↦
          (rule Gamma kappa hkappa hGamma).state
            (hkappa.trans (le_succ kappa)) b))
        (Gamma.strictRoof
          ((finalLadder Gamma kappa hkappa hGamma).frontier a))
        (Gamma.roof
          ((finalLadder Gamma kappa hkappa hGamma).frontier a)) ⊆
      rowAt Gamma kappa hkappa hGamma a := by
  change _ ⊆ ((rule Gamma kappa hkappa hGamma).state
    (hkappa.trans (le_succ kappa)) a).row
  rw [CausalRowRule.state_row_eq]
  change _ ⊆ increment Gamma kappa a _
  rw [increment_eq_final hkappa hGamma a]
  exact Set.subset_union_right.trans Set.subset_union_left

/-- The constructed global carrier contains a maximal-up-to-`kappa`
hammock for every endpoint pair eligible at an ordinary stage. -/
theorem hammockClosedAt
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (a : Ladder.Stage (succ kappa)) :
    HammockClosedUpTo Gamma
      ((finalLadder Gamma kappa hkappa hGamma).warpAt a)
      (globalCarrier Gamma kappa hkappa hGamma)
      (priorCarrier a (fun b _hba ↦
        (rule Gamma kappa hkappa hGamma).state
          (hkappa.trans (le_succ kappa)) b))
      (Gamma.strictRoof
        ((finalLadder Gamma kappa hkappa hGamma).frontier a))
      (Gamma.roof
        ((finalLadder Gamma kappa hkappa hGamma).frontier a)) kappa := by
  intro u e helig
  let q : EligiblePair
      (priorCarrier a (fun b _hba ↦
        (rule Gamma kappa hkappa hGamma).state
          (hkappa.trans (le_succ kappa)) b))
      (Gamma.strictRoof
        ((finalLadder Gamma kappa hkappa hGamma).frontier a))
      (Gamma.roof
        ((finalLadder Gamma kappa hkappa hGamma).frontier a)) :=
    ⟨(u, e), helig⟩
  refine ⟨chosenHammock Gamma
      ((finalLadder Gamma kappa hkappa hGamma).warpAt a) kappa q,
    chosenHammock_spec Gamma
      ((finalLadder Gamma kappa hkappa hGamma).warpAt a) kappa q, ?_⟩
  exact (chosenHammock_contained_all Gamma
      ((finalLadder Gamma kappa hkappa hGamma).warpAt a) kappa q).mono
    ((selectedHammocks_subset_rowAt hkappa hGamma a).trans
      (rowAt_subset_globalCarrier hkappa hGamma a))

/-- The same carrier contains the source's maximal-up-to-`kappa^+`
stage selection. -/
theorem hammockClosedAt_succ
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (a : Ladder.Stage (succ kappa)) :
    HammockClosedUpTo Gamma
      ((finalLadder Gamma kappa hkappa hGamma).warpAt a)
      (globalCarrier Gamma kappa hkappa hGamma)
      (priorCarrier a (fun b _hba ↦
        (rule Gamma kappa hkappa hGamma).state
          (hkappa.trans (le_succ kappa)) b))
      (Gamma.strictRoof
        ((finalLadder Gamma kappa hkappa hGamma).frontier a))
      (Gamma.roof
        ((finalLadder Gamma kappa hkappa hGamma).frontier a))
      (succ kappa) := by
  intro u e helig
  let q : EligiblePair
      (priorCarrier a (fun b _hba ↦
        (rule Gamma kappa hkappa hGamma).state
          (hkappa.trans (le_succ kappa)) b))
      (Gamma.strictRoof
        ((finalLadder Gamma kappa hkappa hGamma).frontier a))
      (Gamma.roof
        ((finalLadder Gamma kappa hkappa hGamma).frontier a)) :=
    ⟨(u, e), helig⟩
  refine ⟨chosenHammock Gamma
      ((finalLadder Gamma kappa hkappa hGamma).warpAt a) (succ kappa) q,
    chosenHammock_spec Gamma
      ((finalLadder Gamma kappa hkappa hGamma).warpAt a) (succ kappa) q, ?_⟩
  exact (chosenHammock_contained_all Gamma
      ((finalLadder Gamma kappa hkappa hGamma).warpAt a) (succ kappa) q).mono
    ((selectedHammocksSucc_subset_rowAt hkappa hGamma a).trans
      (rowAt_subset_globalCarrier hkappa hGamma a))

/-- Every stage path meeting the displayed closure is absorbed at the next
ordinary stage. -/
theorem causalStagePathClosure
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized) :
    CausalStagePathClosure (finalLadder Gamma kappa hkappa hGamma)
      (closedAt Gamma kappa hkappa hGamma) := by
  intro a p hp hmeet
  let hsucc : aleph0 ≤ succ kappa := hkappa.trans (le_succ kappa)
  let preferred :=
    (rule Gamma kappa hkappa hGamma).preferred hsucc
  have hregular : (succ kappa).IsRegular := Cardinal.isRegular_succ hkappa
  have huncountable : aleph0 < succ kappa :=
    hkappa.trans_lt (lt_succ kappa)
  have hNoEnter : Gamma.NoEdgeEnters Gamma.source := by
    intro x y hxy hy
    exact (hGamma hxy).1 hy
  have hlegal : DWeb.KappaLadder.Deferred.HalfwayGeometry
      (finalLadder Gamma kappa hkappa hGamma) := by
    simpa only [finalLadder, preferred, hsucc] using
      UnroofedHalfwayRowLadder.deferred_halfwayGeometry
        preferred hregular huncountable hNoEnter
  let b : Ladder.Stage (succ kappa) :=
    ⟨a.1 + 1, (Cardinal.isSuccLimit_ord hsucc).succ_lt a.2⟩
  have hab : a < b := by
    change a.1 < a.1 + 1
    exact Order.lt_succ a.1
  obtain ⟨q, hqSucc, hpq⟩ :=
    CardinalInduction.DeferredStageInterval.successorExtensions hlegal a p hp
  have hq : q ∈ (finalLadder Gamma kappa hkappa hGamma).warpAt b := by
    change q ∈ (finalLadder Gamma kappa hkappa hGamma).accumulated
      (Ladder.Stage.toExtended b)
    change q ∈ (finalLadder Gamma kappa hkappa hGamma).accumulated
      (Ladder.Stage.succExtended a) at hqSucc
    have hstage : Ladder.Stage.toExtended b =
        Ladder.Stage.succExtended a := by
      apply Subtype.ext
      rfl
    rwa [hstage]
  obtain ⟨x, hxp, hxClosed⟩ := hmeet
  obtain ⟨c, hxc⟩ := Set.mem_iUnion.1 hxClosed
  have hcb : c.1 < b := c.2.trans_lt hab
  have hxPrior : x ∈ priorCarrier b (fun d _hdb ↦
      (rule Gamma kappa hkappa hGamma).state hsucc d) := by
    exact Set.mem_iUnion.2 ⟨⟨c.1, hcb⟩, hxc⟩
  have hxq : x ∈ q.support :=
    Gamma.support_mono_of_extends hpq hxp
  have hqMeet : (q.support ∩ priorCarrier b (fun d _hdb ↦
      (rule Gamma kappa hkappa hGamma).state hsucc d)).Nonempty :=
    ⟨x, hxq, hxPrior⟩
  have hqRow : q.support ⊆ rowAt Gamma kappa hkappa hGamma b :=
    (support_subset_meetingVertices Gamma
      ((finalLadder Gamma kappa hkappa hGamma).warpAt b)
      (priorCarrier b (fun d _hdb ↦
        (rule Gamma kappa hkappa hGamma).state hsucc d)) hq hqMeet).trans
      (contacted_reference_subset_rowAt hkappa hGamma b)
  refine ⟨b, hab.le, ?_⟩
  intro y hyp
  exact Set.mem_iUnion.2 ⟨⟨b, show b ≤ b from le_rfl⟩,
    hqRow (Gamma.support_mono_of_extends hpq hyp)⟩

/-- The actual global causal carrier is closed under the final limiting
reference. -/
theorem reference_closed
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized) :
    ClosedUnderPaths Gamma
      (finalLadder Gamma kappa hkappa hGamma).limitWarp
      (globalCarrier Gamma kappa hkappa hGamma) := by
  let hsucc : aleph0 ≤ succ kappa := hkappa.trans (le_succ kappa)
  let preferred :=
    (rule Gamma kappa hkappa hGamma).preferred hsucc
  have hregular : (succ kappa).IsRegular := Cardinal.isRegular_succ hkappa
  have huncountable : aleph0 < succ kappa :=
    hkappa.trans_lt (lt_succ kappa)
  have hNoEnter : Gamma.NoEdgeEnters Gamma.source := by
    intro x y hxy hy
    exact (hGamma hxy).1 hy
  have hlegal : DWeb.KappaLadder.Deferred.HalfwayGeometry
      (finalLadder Gamma kappa hkappa hGamma) := by
    simpa only [finalLadder, preferred, hsucc] using
      UnroofedHalfwayRowLadder.deferred_halfwayGeometry
        preferred hregular huncountable hNoEnter
  rw [← iUnion_closedAt_eq_globalCarrier hkappa hGamma]
  exact closedUnderPaths_limitWarp_iUnion_of_causalStages
    (finalLadder Gamma kappa hkappa hGamma) hlegal
    (closedAt Gamma kappa hkappa hGamma)
    (closedAt_mono hkappa hGamma)
    (causalStagePathClosure hkappa hGamma)

/-- Every inserted reference or hammock vertex is eventually roofed by the
same preferred-marker scheduler. -/
theorem globalCarrier_subset_limitRoof
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized) :
    globalCarrier Gamma kappa hkappa hGamma ⊆
      (finalLadder Gamma kappa hkappa hGamma).limitRoof := by
  have hNoEnter : Gamma.NoEdgeEnters Gamma.source := by
    intro x y hxy hy
    exact (hGamma hxy).1 hy
  exact DWeb.UnroofedMarker.causalCarrier_subset_limitRoof Gamma
    (rule Gamma kappa hkappa hGamma) hNoEnter
    (Cardinal.isRegular_succ hkappa) (hkappa.trans_lt (lt_succ kappa))

#print axioms CausalReferenceHammockRows.mk_increment_le_succ
#print axioms CausalReferenceHammockRows.hammockClosedAt
#print axioms CausalReferenceHammockRows.hammockClosedAt_succ
#print axioms CausalReferenceHammockRows.causalStagePathClosure
#print axioms CausalReferenceHammockRows.reference_closed
#print axioms CausalReferenceHammockRows.globalCarrier_subset_limitRoof

end CausalReferenceHammockRows
end Erdos599.Blueprint.LinkageBlueprint
