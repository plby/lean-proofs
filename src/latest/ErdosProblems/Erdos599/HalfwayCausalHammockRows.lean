/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedHalfwayRowLadder
import ErdosProblems.Erdos599.HalfwayLadderReference
import ErdosProblems.Erdos599.LadderDeferredBookkeeping

/-!
# Causal stage-local hammock rows

The Section 9 closing construction does not assume that a newly selected
maximal hammock is already contained in the current roof.  At stage `a` it
selects maximal hammocks for the full accumulated reference `Y_a`, inserts
their vertices in the new bounded row, and lets the causal
preferred-marker scheduler roof those vertices at later stages.

This file implements that non-circular part of the simultaneous
ladder/closing-set recursion.  Its global rows are `kappa^+`-bounded, as in
the source, and contain both the maximal-up-to-`kappa` selection used by a
single Claim 9.31 transaction and the maximal-up-to-`kappa^+` selection used
by the global closure.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating Ladder
open CardinalInduction.RegularRows

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace CausalHammockRows

/-- Vertices present in rows born strictly before `a`. -/
def priorCarrier
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) : Set V :=
  ⋃ b : Set.Iio a, (prior b.1 b.2).row

/-- The stage-local maximal-hammock increment.  Both the reference and the
two roof parameters are read from the strict-prior unroofed ladder, so the
definition has no access to a future preferred marker. -/
def hammockIncrement
    (Gamma : DWeb V) (kappa : Cardinal.{u})
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) : Set V :=
  let L := UnroofedHalfwayRowLadder.priorLadder
    Gamma a prior
  allHammockVertices Gamma (L.warpAt a) kappa
      (priorCarrier a prior)
      (Gamma.strictRoof (L.frontier a))
      (Gamma.roof (L.frontier a)) ∪
    allHammockVertices Gamma (L.warpAt a) (succ kappa)
      (priorCarrier a prior)
      (Gamma.strictRoof (L.frontier a))
      (Gamma.roof (L.frontier a))

/-- Coarse cardinal bound used only to form a `CausalRowRule` on
`Stage (kappa^+)`. -/
theorem mk_priorCarrier_le_succ
    (hkappa : aleph0 ≤ kappa)
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) :
    #(priorCarrier a prior) ≤ succ kappa := by
  apply CardinalInduction.RegularRows.mk_iUnion_stageSet_le
    (hkappa.trans (le_succ kappa))
  intro b
  exact (prior b.1 b.2).row_mk_le

/-- The local hammock increment has the coarse bound required by the
ambient causal scheduling API. -/
theorem mk_hammockIncrement_le_succ
    (hkappa : aleph0 ≤ kappa)
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) :
    #(hammockIncrement Gamma kappa a prior) ≤ succ kappa := by
  unfold hammockIncrement
  apply (Cardinal.mk_union_le _ _).trans
  apply Cardinal.add_le_of_le (hkappa.trans (le_succ kappa))
  · apply mk_allHammockVertices_le Gamma _
      (hkappa.trans (le_succ kappa)) (le_succ kappa)
    exact mk_priorCarrier_le_succ hkappa a prior
  · apply mk_allHammockVertices_le Gamma _
      (hkappa.trans (le_succ kappa)) (le_refl (succ kappa))
    exact mk_priorCarrier_le_succ hkappa a prior

/-- The actual causal rule which inserts all stage-local maximal-hammock
vertices and schedules them one at a time as future preferred markers. -/
def rule (Gamma : DWeb V) (kappa : Cardinal.{u})
    (hkappa : aleph0 ≤ kappa) : CausalRowRule (succ kappa) V where
  nextRow a prior := hammockIncrement Gamma kappa a prior
  nextRow_mk_le a prior := mk_hammockIncrement_le_succ hkappa a prior

/-- The actual row born at `a`. -/
def rowAt (Gamma : DWeb V) (kappa : Cardinal.{u})
    (hkappa : aleph0 ≤ kappa) (a : Ladder.Stage (succ kappa)) : Set V :=
  ((rule Gamma kappa hkappa).state
    (hkappa.trans (le_succ kappa)) a).row

/-- The monotone displayed closure through stage `a`. -/
def closedAt (Gamma : DWeb V) (kappa : Cardinal.{u})
    (hkappa : aleph0 ≤ kappa) (a : Ladder.Stage (succ kappa)) : Set V :=
  ⋃ b : Set.Iic a, rowAt Gamma kappa hkappa b.1

/-- The complete causal closing set. -/
def globalCarrier (Gamma : DWeb V) (kappa : Cardinal.{u})
    (hkappa : aleph0 ≤ kappa) : Set V :=
  ((rule Gamma kappa hkappa).rowSystem
    (hkappa.trans (le_succ kappa))).carrier

/-- Every actual row has the source's global `kappa^+` bound. -/
theorem rowAt_mk_le_succ
    (hkappa : aleph0 ≤ kappa) (a : Ladder.Stage (succ kappa)) :
    #(rowAt Gamma kappa hkappa a) ≤ succ kappa :=
  ((rule Gamma kappa hkappa).state
    (hkappa.trans (le_succ kappa)) a).row_mk_le

/-- Every displayed closure has cardinality at most `kappa^+`. -/
theorem closedAt_mk_le_succ
    (hkappa : aleph0 ≤ kappa) (a : Ladder.Stage (succ kappa)) :
    #(closedAt Gamma kappa hkappa a) ≤ succ kappa := by
  unfold closedAt
  apply CardinalInduction.RegularRows.mk_iUnion_stageSet_le
    (hkappa.trans (le_succ kappa))
  intro b
  exact rowAt_mk_le_succ hkappa b.1

/-- The complete global carrier also has size at most `kappa^+`. -/
theorem globalCarrier_mk_le_succ
    (hkappa : aleph0 ≤ kappa) :
    #(globalCarrier Gamma kappa hkappa) ≤ succ kappa :=
  ((rule Gamma kappa hkappa).rowSystem
    (hkappa.trans (le_succ kappa))).mk_carrier_le
      (hkappa.trans (le_succ kappa))

/-- The displayed stage closures are monotone. -/
theorem closedAt_mono
    (hkappa : aleph0 ≤ kappa) :
    Monotone (closedAt Gamma kappa hkappa) := by
  intro a b hab x hx
  obtain ⟨c, hxc⟩ := Set.mem_iUnion.1 hx
  exact Set.mem_iUnion.2 ⟨⟨c.1, c.2.trans hab⟩, hxc⟩

/-- Strictly earlier displayed closures contain exactly the rows born
strictly before the current stage. -/
theorem closedBefore_closedAt_eq_priorCarrier
    (hkappa : aleph0 ≤ kappa) (a : Ladder.Stage (succ kappa)) :
    closedBefore (closedAt Gamma kappa hkappa) a =
      priorCarrier a (fun b _hba ↦
        (rule Gamma kappa hkappa).state
          (hkappa.trans (le_succ kappa)) b) := by
  ext x
  constructor
  · rintro ⟨b, hba, hxb⟩
    obtain ⟨c, hxc⟩ := Set.mem_iUnion.1 hxb
    exact Set.mem_iUnion.2 ⟨⟨c.1, c.2.trans_lt hba⟩, hxc⟩
  · intro hx
    obtain ⟨b, hxb⟩ := Set.mem_iUnion.1 hx
    refine ⟨b.1, b.2, ?_⟩
    exact Set.mem_iUnion.2
      ⟨⟨b.1, show b.1 ≤ b.1 from le_rfl⟩, hxb⟩

/-- Every actual row is contained in the final causal carrier. -/
theorem rowAt_subset_globalCarrier
    (hkappa : aleph0 ≤ kappa) (a : Ladder.Stage (succ kappa)) :
    rowAt Gamma kappa hkappa a ⊆ globalCarrier Gamma kappa hkappa :=
  ((rule Gamma kappa hkappa).rowSystem
      (hkappa.trans (le_succ kappa))).row_subset_carrier a

/-- The final unroofed core driven by the causal hammock scheduler. -/
def finalCore (Gamma : DWeb V) (kappa : Cardinal.{u})
    (hkappa : aleph0 ≤ kappa) : Gamma.KappaLadder (succ kappa) :=
  UnroofedHalfwayRowLadder.core Gamma (succ kappa)
    ((rule Gamma kappa hkappa).preferred
      (hkappa.trans (le_succ kappa)))

/-- Prefix-causality identifies the reference and frontier used to create
the row at `a` with those of the final scheduled ladder. -/
theorem hammockIncrement_eq_final
    (hkappa : aleph0 ≤ kappa) (a : Ladder.Stage (succ kappa)) :
    hammockIncrement Gamma kappa a
        (fun b _hba ↦ (rule Gamma kappa hkappa).state
          (hkappa.trans (le_succ kappa)) b) =
      allHammockVertices Gamma
          ((finalCore Gamma kappa hkappa).warpAt a) kappa
          (priorCarrier a (fun b _hba ↦
            (rule Gamma kappa hkappa).state
              (hkappa.trans (le_succ kappa)) b))
          (Gamma.strictRoof ((finalCore Gamma kappa hkappa).frontier a))
          (Gamma.roof ((finalCore Gamma kappa hkappa).frontier a)) ∪
        allHammockVertices Gamma
          ((finalCore Gamma kappa hkappa).warpAt a) (succ kappa)
          (priorCarrier a (fun b _hba ↦
            (rule Gamma kappa hkappa).state
              (hkappa.trans (le_succ kappa)) b))
          (Gamma.strictRoof ((finalCore Gamma kappa hkappa).frontier a))
          (Gamma.roof ((finalCore Gamma kappa hkappa).frontier a)) := by
  let Q := rule Gamma kappa hkappa
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
  unfold hammockIncrement
  change
    (allHammockVertices Gamma
        ((UnroofedHalfwayRowLadder.priorLadder Gamma a
          (fun b _hba ↦ Q.state hsucc b)).warpAt a) kappa _ _ _ ∪
      allHammockVertices Gamma
        ((UnroofedHalfwayRowLadder.priorLadder Gamma a
          (fun b _hba ↦ Q.state hsucc b)).warpAt a) (succ kappa) _ _ _) = _
  have hwarp' :
      (UnroofedHalfwayRowLadder.priorLadder Gamma a
          (fun b _hba ↦ Q.state hsucc b)).warpAt a =
        (finalCore Gamma kappa hkappa).warpAt a := by
    change
      (UnroofedHalfwayRowLadder.core Gamma (succ kappa)
          (CardinalInduction.RegularRows.CausalRegular.preferredOfPrior a
            (fun b _hba ↦ Q.state hsucc b))).warpAt a =
        (UnroofedHalfwayRowLadder.core Gamma (succ kappa)
          ((rule Gamma kappa hkappa).preferred
            (hkappa.trans (le_succ kappa)))).warpAt a
    simpa only [Q, hsucc] using hwarp
  have hfrontier' :
      (UnroofedHalfwayRowLadder.priorLadder Gamma a
          (fun b _hba ↦ Q.state hsucc b)).frontier a =
        (finalCore Gamma kappa hkappa).frontier a := by
    change
      (UnroofedHalfwayRowLadder.core Gamma (succ kappa)
          (CardinalInduction.RegularRows.CausalRegular.preferredOfPrior a
            (fun b _hba ↦ Q.state hsucc b))).frontier a =
        (UnroofedHalfwayRowLadder.core Gamma (succ kappa)
          ((rule Gamma kappa hkappa).preferred
            (hkappa.trans (le_succ kappa)))).frontier a
    simpa only [Q, hsucc] using hfrontier
  rw [hwarp', hfrontier']

/-- At every stage, the final causal carrier contains a maximal-up-to-
`kappa` hammock for each pair eligible over the strict-prior carrier, with
the actual full accumulated stage reference. -/
theorem hammockClosedAt
    (hkappa : aleph0 ≤ kappa) (a : Ladder.Stage (succ kappa)) :
    HammockClosedUpTo Gamma
      ((finalCore Gamma kappa hkappa).warpAt a)
      (globalCarrier Gamma kappa hkappa)
      (priorCarrier a (fun b _hba ↦
        (rule Gamma kappa hkappa).state
          (hkappa.trans (le_succ kappa)) b))
      (Gamma.strictRoof ((finalCore Gamma kappa hkappa).frontier a))
      (Gamma.roof ((finalCore Gamma kappa hkappa).frontier a)) kappa := by
  intro u e helig
  let q : EligiblePair
      (priorCarrier a (fun b _hba ↦
        (rule Gamma kappa hkappa).state
          (hkappa.trans (le_succ kappa)) b))
      (Gamma.strictRoof ((finalCore Gamma kappa hkappa).frontier a))
      (Gamma.roof ((finalCore Gamma kappa hkappa).frontier a)) :=
    ⟨(u, e), helig⟩
  refine ⟨chosenHammock Gamma
      ((finalCore Gamma kappa hkappa).warpAt a) kappa q,
    chosenHammock_spec Gamma
      ((finalCore Gamma kappa hkappa).warpAt a) kappa q, ?_⟩
  apply (chosenHammock_contained_all Gamma
    ((finalCore Gamma kappa hkappa).warpAt a) kappa q).mono
  have hallRow :
      allHammockVertices Gamma
          ((finalCore Gamma kappa hkappa).warpAt a) kappa
          (priorCarrier a (fun b _hba ↦
            (rule Gamma kappa hkappa).state
              (hkappa.trans (le_succ kappa)) b))
          (Gamma.strictRoof ((finalCore Gamma kappa hkappa).frontier a))
          (Gamma.roof ((finalCore Gamma kappa hkappa).frontier a)) ⊆
        rowAt Gamma kappa hkappa a := by
    rw [rowAt, CausalRowRule.state_row_eq]
    change _ ⊆ hammockIncrement Gamma kappa a
      (fun b _hba ↦ (rule Gamma kappa hkappa).state
        (hkappa.trans (le_succ kappa)) b)
    rw [hammockIncrement_eq_final (Gamma := Gamma) hkappa a]
    exact Set.subset_union_left
  exact hallRow.trans
    (rowAt_subset_globalCarrier (Gamma := Gamma) hkappa a)

/-- The same row also contains the global maximal-up-to-`kappa^+`
selection required by the source's outer closing construction. -/
theorem hammockClosedAt_succ
    (hkappa : aleph0 ≤ kappa) (a : Ladder.Stage (succ kappa)) :
    HammockClosedUpTo Gamma
      ((finalCore Gamma kappa hkappa).warpAt a)
      (globalCarrier Gamma kappa hkappa)
      (priorCarrier a (fun b _hba ↦
        (rule Gamma kappa hkappa).state
          (hkappa.trans (le_succ kappa)) b))
      (Gamma.strictRoof ((finalCore Gamma kappa hkappa).frontier a))
      (Gamma.roof ((finalCore Gamma kappa hkappa).frontier a))
      (succ kappa) := by
  intro u e helig
  let q : EligiblePair
      (priorCarrier a (fun b _hba ↦
        (rule Gamma kappa hkappa).state
          (hkappa.trans (le_succ kappa)) b))
      (Gamma.strictRoof ((finalCore Gamma kappa hkappa).frontier a))
      (Gamma.roof ((finalCore Gamma kappa hkappa).frontier a)) :=
    ⟨(u, e), helig⟩
  refine ⟨chosenHammock Gamma
      ((finalCore Gamma kappa hkappa).warpAt a) (succ kappa) q,
    chosenHammock_spec Gamma
      ((finalCore Gamma kappa hkappa).warpAt a) (succ kappa) q, ?_⟩
  apply (chosenHammock_contained_all Gamma
    ((finalCore Gamma kappa hkappa).warpAt a) (succ kappa) q).mono
  have hallRow :
      allHammockVertices Gamma
          ((finalCore Gamma kappa hkappa).warpAt a) (succ kappa)
          (priorCarrier a (fun b _hba ↦
            (rule Gamma kappa hkappa).state
              (hkappa.trans (le_succ kappa)) b))
          (Gamma.strictRoof ((finalCore Gamma kappa hkappa).frontier a))
          (Gamma.roof ((finalCore Gamma kappa hkappa).frontier a)) ⊆
        rowAt Gamma kappa hkappa a := by
    rw [rowAt, CausalRowRule.state_row_eq]
    change _ ⊆ hammockIncrement Gamma kappa a
      (fun b _hba ↦ (rule Gamma kappa hkappa).state
        (hkappa.trans (le_succ kappa)) b)
    rw [hammockIncrement_eq_final (Gamma := Gamma) hkappa a]
    exact Set.subset_union_right
  exact hallRow.trans
    (rowAt_subset_globalCarrier (Gamma := Gamma) hkappa a)

/-- The preferred-marker schedule roofs every vertex ever inserted in a
causal hammock row.  This is the non-circular source route to
`Z ⊆ RF(L)`: hammock vertices are roofed *after* their row is born. -/
theorem globalCarrier_subset_limitRoof
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized) :
    globalCarrier Gamma kappa hkappa ⊆
      (finalCore Gamma kappa hkappa).limitRoof := by
  have hNoEnter : Gamma.NoEdgeEnters Gamma.source := by
    intro x y hxy hy
    exact (hGamma hxy).1 hy
  exact DWeb.UnroofedMarker.causalCarrier_subset_limitRoof Gamma
    (rule Gamma kappa hkappa) hNoEnter
    (Cardinal.isRegular_succ hkappa) (hkappa.trans_lt (lt_succ kappa))

#print axioms CausalHammockRows.mk_hammockIncrement_le_succ
#print axioms CausalHammockRows.hammockClosedAt
#print axioms CausalHammockRows.hammockClosedAt_succ
#print axioms CausalHammockRows.globalCarrier_subset_limitRoof

end CausalHammockRows
end Erdos599.Blueprint.LinkageBlueprint
