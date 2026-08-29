/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayGlobalLocalReferenceClassification
import ErdosProblems.Erdos599.HalfwayLiteralContactGeometry

/-!
# Reclassifying the fractured contact transaction at the limiting reference

The local contact transaction compresses each outside-open interval between
two consecutive contacts.  A local shortcut need not remain imaginary for
the limiting reference: an exposed endpoint may lie on an inessential stage
component.  In that case no shortcut is retained.  The literal forward edges
of the interval already belong to the real base of the fractured assignment.

Accordingly, the honest limiting shortcut relation is the subrelation of the
existing grouped contact relation consisting of the pairs which are genuinely
imaginary for the limiting reference.  This preserves the concrete contact
order, grouping, and cross-incidence proofs.  It is deliberately only a
relation-level compiler; it makes no source-cover or linkage claim.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder Alternating
open Alternating.RelationDecomposition

universe u v

variable {V : Type u} {Gamma : DWeb V} {Y closureFamily : Set Gamma.DPath}
variable {X before innerRoof outerRoof : Set V}
variable {kappa : Cardinal.{u}}

namespace ContactSegmentation

variable {Q : AltPath Gamma.graph}

/-- The contact shortcuts which remain genuine shortcuts for the limiting
reference.  Covered branches contribute no shortcut; their literal forward
edges are retained by the real base of the fractured assignment. -/
def limitingShortcutEdges
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (S : ContactSegmentation (Y := C.selectedReference) Q X before innerRoof
      outerRoof closureFamily) : Set (V × V) :=
  S.compressedOutsideEdges ∩
    {e | IsImaginaryEdge Gamma C.ladder.limitWarp kappa e.1 e.2}

theorem limitingShortcutEdges_subset_compressedOutsideEdges
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (S : ContactSegmentation (Y := C.selectedReference) Q X before innerRoof
      outerRoof closureFamily) :
    S.limitingShortcutEdges C ⊆ S.compressedOutsideEdges :=
  Set.inter_subset_left

theorem limitingShortcutEdges_subset_imaginaryGraph
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (S : ContactSegmentation (Y := C.selectedReference) Q X before innerRoof
      outerRoof closureFamily) :
    S.limitingShortcutEdges C ⊆
      {e | (imaginaryGraph Gamma C.ladder.limitWarp kappa).Adj e.1 e.2} := by
  intro e he
  exact Or.inr he.2

private theorem localImaginary_of_mem_compressedOutsideEdges
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (S : ContactSegmentation (Y := C.selectedReference) Q X before innerRoof
      outerRoof closureFamily)
    (hclosed : HammockClosedUpTo Gamma C.selectedReference X before innerRoof
      outerRoof kappa)
    {a b : V} (hab : (a, b) ∈ S.compressedOutsideEdges) :
    IsImaginaryEdge Gamma C.selectedReference kappa a b := by
  cases S with
  | finite T =>
      rcases hab with ⟨i, P, _hi, hpair⟩
      have ha := congrArg Prod.fst hpair
      have hb := congrArg Prod.snd hpair
      simp only at ha hb
      subst a
      subst b
      exact P.isImaginaryEdge hclosed
  | eventuallyOutside T =>
      rcases hab with ⟨i, P, _hi, hpair⟩
      have ha := congrArg Prod.fst hpair
      have hb := congrArg Prod.snd hpair
      simp only at ha hb
      subst a
      subst b
      exact P.isImaginaryEdge hclosed
  | omega T =>
      rcases hab with ⟨i, P, _hi, hpair⟩
      have ha := congrArg Prod.fst hpair
      have hb := congrArg Prod.snd hpair
      simp only at ha hb
      subst a
      subst b
      exact P.isImaginaryEdge hclosed

/-- Every actual local contact shortcut either survives as a limiting
imaginary edge or has a genuine limiting-reference owner at one of its
exposed endpoints.  This is the concrete justification for deleting exactly
the non-surviving shortcuts from the relation. -/
theorem localShortcut_global_or_covered
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (S : ContactSegmentation (Y := C.selectedReference) Q X before innerRoof
      outerRoof closureFamily)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (hclosed : HammockClosedUpTo Gamma C.selectedReference X before innerRoof
      outerRoof kappa)
    {a b : V} (hab : (a, b) ∈ S.compressedOutsideEdges) :
    IsImaginaryEdge Gamma C.ladder.limitWarp kappa a b ∨
      Nonempty (ClubStageGeometry.LimitingReferenceEndpointOwner C a) ∨
      Nonempty (ClubStageGeometry.LimitingReferenceEndpointOwner C b) := by
  have hlocal := S.localImaginary_of_mem_compressedOutsideEdges C hclosed hab
  obtain ⟨K⟩ := C.globalizeLocalImaginary (X := X) (Q := Q)
    hSafeRoof hlocal
  cases K with
  | imaginary h => exact Or.inl h
  | initialCovered P => exact Or.inr (Or.inl ⟨P⟩)
  | terminalCovered P => exact Or.inr (Or.inr ⟨P⟩)

end ContactSegmentation

namespace GroupedContactSegmentedAssignment

/-- The grouped contact relation restricted to the shortcuts which are
genuinely imaginary for the limiting reference. -/
def limitingShortcutEdges
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {Z : Set Gamma.DPath}
    {A : SimultaneousAssignment Z C.selectedReference}
    {G : Type v}
    (S : GroupedContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily G) : Set (V × V) :=
  S.edge ∩ {e | IsImaginaryEdge Gamma C.ladder.limitWarp kappa e.1 e.2}

theorem limitingShortcutEdges_subset_edge
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {Z : Set Gamma.DPath}
    {A : SimultaneousAssignment Z C.selectedReference}
    {G : Type v}
    (S : GroupedContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily G) :
    S.limitingShortcutEdges C ⊆ S.edge :=
  Set.inter_subset_left

theorem limitingShortcutEdges_subset_imaginaryGraph
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {Z : Set Gamma.DPath}
    {A : SimultaneousAssignment Z C.selectedReference}
    {G : Type v}
    (S : GroupedContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily G) :
    S.limitingShortcutEdges C ⊆
      {e | (imaginaryGraph Gamma C.ladder.limitWarp kappa).Adj e.1 e.2} := by
  intro e he
  exact Or.inr he.2

theorem limitingShortcutEdges_biunique
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {Z : Set Gamma.DPath}
    {A : SimultaneousAssignment Z C.selectedReference}
    {G : Type v}
    (S : GroupedContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily G) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ S.limitingShortcutEdges C) := by
  constructor
  · intro a b c hac hbc
    exact S.edge_biunique.1 hac.1 hbc.1
  · intro a b c hab hac
    exact S.edge_biunique.2 hab.1 hac.1

theorem rank_lt_of_mem_limitingShortcutEdges
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {Z : Set Gamma.DPath}
    {A : SimultaneousAssignment Z C.selectedReference}
    {G : Type v}
    (S : GroupedContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily G)
    {a b : V} (hab : (a, b) ∈ S.limitingShortcutEdges C) :
    S.rank a < S.rank b :=
  S.rank_lt_of_mem_edge hab.1

theorem limitingShortcutEdges_acyclic
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {Z : Set Gamma.DPath}
    {A : SimultaneousAssignment Z C.selectedReference}
    {G : Type v}
    (S : GroupedContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily G) :
    ¬ ContainsDirectedCycle (S.limitingShortcutEdges C) :=
  Alternating.GenericSimultaneousSwitch.not_containsDirectedCycle_of_wellFoundedRank
    (S.limitingShortcutEdges C) S.rank
    (S.rank_lt_of_mem_limitingShortcutEdges C)

theorem limitingShortcutEdges_no_reverse_ray
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {Z : Set Gamma.DPath}
    {A : SimultaneousAssignment Z C.selectedReference}
    {G : Type v}
    (S : GroupedContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily G) :
    ¬ ContainsReverseDirectedRay (S.limitingShortcutEdges C) :=
  Alternating.GenericSimultaneousSwitch.not_containsReverseDirectedRay_of_wellFoundedRank
    (S.limitingShortcutEdges C) S.rank
    (S.rank_lt_of_mem_limitingShortcutEdges C)

end GroupedContactSegmentedAssignment

namespace LiteralContactSpliceData

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {Z : FracturedWarp Gamma}
variable {B : FracturedAssignmentPeel.BracketFracturedAssignment
  Z C.selectedReference}
variable {G : Type v}
variable {S : GroupedContactSegmentedAssignment B.assignment X before
  innerRoof outerRoof closureFamily G}

/-- The truthful global-reference relation: all literal real forward edges,
together with only those contact shortcuts which remain globally imaginary. -/
def limitingEdge (D : LiteralContactSpliceData B S) : Set (V × V) :=
  B.retainedForwardEdges ∪ S.limitingShortcutEdges C

theorem limitingEdge_subset_edge (D : LiteralContactSpliceData B S) :
    D.limitingEdge (C := C) ⊆ D.edge := by
  rintro e (he | he)
  · exact Or.inl he
  · exact Or.inr (S.limitingShortcutEdges_subset_edge C he)

theorem limitingEdge_subset_imaginaryGraph
    (D : LiteralContactSpliceData B S) :
    D.limitingEdge (C := C) ⊆
      {e | (imaginaryGraph Gamma C.ladder.limitWarp kappa).Adj e.1 e.2} := by
  rintro e (he | he)
  · exact Or.inl (familyEdges_subset_adj Z.edgeWarp
      (B.retainedForwardEdges_subset_familyEdges he))
  · exact S.limitingShortcutEdges_subset_imaginaryGraph C he

theorem limitingEdge_endpoints_mem_carrier
    (D : LiteralContactSpliceData B S) (e : V × V)
    (he : e ∈ D.limitingEdge (C := C)) :
    e.1 ∈ D.carrier ∧ e.2 ∈ D.carrier :=
  D.endpoints_mem_carrier e (D.limitingEdge_subset_edge he)

theorem limitingEdge_biunique (D : LiteralContactSpliceData B S) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ D.limitingEdge (C := C)) := by
  constructor
  · intro a b c hac hbc
    exact D.edge_biunique.1
      (D.limitingEdge_subset_edge hac) (D.limitingEdge_subset_edge hbc)
  · intro a b c hab hac
    exact D.edge_biunique.2
      (D.limitingEdge_subset_edge hab) (D.limitingEdge_subset_edge hac)

theorem rank_lt_of_mem_limitingEdge (D : LiteralContactSpliceData B S)
    {a b : V} (hab : (a, b) ∈ D.limitingEdge (C := C)) :
    D.rank a < D.rank b :=
  D.rank_lt_of_mem_edge (D.limitingEdge_subset_edge hab)

theorem limitingEdge_acyclic (D : LiteralContactSpliceData B S) :
    ¬ ContainsDirectedCycle (D.limitingEdge (C := C)) :=
  Alternating.GenericSimultaneousSwitch.not_containsDirectedCycle_of_wellFoundedRank
    (D.limitingEdge (C := C)) D.rank
    D.rank_lt_of_mem_limitingEdge

theorem limitingEdge_no_reverse_ray (D : LiteralContactSpliceData B S) :
    ¬ ContainsReverseDirectedRay (D.limitingEdge (C := C)) :=
  Alternating.GenericSimultaneousSwitch.not_containsReverseDirectedRay_of_wellFoundedRank
    (D.limitingEdge (C := C)) D.rank
    D.rank_lt_of_mem_limitingEdge

/-- Compile the corrected limiting-reference relation to an orientation
package.  Source coverage and linkage are intentionally not asserted here. -/
def limitingTransactionGeometry (D : LiteralContactSpliceData B S) :
    LiteralContactTransactionGeometry
      (Gamma := Gamma) (Y := C.ladder.limitWarp) (kappa := kappa) where
  edge := D.limitingEdge (C := C)
  carrier := D.carrier
  edge_subset_imaginaryGraph := D.limitingEdge_subset_imaginaryGraph
  endpoints_mem_carrier := D.limitingEdge_endpoints_mem_carrier
  biunique := D.limitingEdge_biunique
  acyclic := D.limitingEdge_acyclic
  no_reverse_ray := D.limitingEdge_no_reverse_ray

@[simp] theorem limitingTransactionGeometry_edge
    (D : LiteralContactSpliceData B S) :
    (D.limitingTransactionGeometry (C := C)).edge =
      B.retainedForwardEdges ∪ S.limitingShortcutEdges C := rfl

@[simp] theorem limitingTransactionGeometry_carrier
    (D : LiteralContactSpliceData B S) :
    (D.limitingTransactionGeometry (C := C)).carrier = D.carrier := rfl

end LiteralContactSpliceData

#print axioms ContactSegmentation.localShortcut_global_or_covered
#print axioms GroupedContactSegmentedAssignment.limitingShortcutEdges_biunique
#print axioms LiteralContactSpliceData.limitingTransactionGeometry

end Erdos599.Blueprint.LinkageBlueprint
