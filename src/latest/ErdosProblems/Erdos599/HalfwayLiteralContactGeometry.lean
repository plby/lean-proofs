/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayGroupedContactTransaction
import ErdosProblems.Erdos599.HalfwayEndpointCoveredClaim2

/-!
# Literal-order contact transaction geometry

The literal fractured family is not a warp: consecutive holes can have a
common terminal/initial vertex.  Consequently a contact transaction cannot
be indexed by the raw hole source.  `GroupedContactSegmentedAssignment`
retains the correct datum instead: sources which meet at a contact are put in
one recombined macro component, and bi-uniqueness and the traversal rank are
proved inside that component.

This file packages the output of that compiler in the relation-level form
used by the half-way transaction.  The package deliberately records the
carrier and exact edge equation.  This makes it possible to splice the
relation into a club-stage transaction without pretending that different raw
holes have disjoint contact sets.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating
open Alternating.RelationDecomposition

universe u v

variable {V : Type u}
variable {Gamma : DWeb V} {Y closureFamily : Set Gamma.DPath}
variable {X before innerRoof outerRoof : Set V}
variable {kappa : Cardinal.{u}}

/-- A retained relation, with the exact carrier and all structural facts
needed to turn it into an honest forward orientation.

Unlike the older route-indexed `ContactSegmentedAssignment.TransactionGeometry`,
this object does not assert that different literal fractured sources have
disjoint contacts.  That statement is false at a fracture junction.  Its
bi-uniqueness and rank may instead be obtained from a recombined-owner group. -/
structure LiteralContactTransactionGeometry where
  edge : Set (V × V)
  carrier : Set V
  edge_subset_imaginaryGraph :
    edge ⊆ {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2}
  endpoints_mem_carrier : ∀ e ∈ edge, e.1 ∈ carrier ∧ e.2 ∈ carrier
  biunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ edge)
  acyclic : ¬ ContainsDirectedCycle edge
  no_reverse_ray : ¬ ContainsReverseDirectedRay edge

namespace LiteralContactTransactionGeometry

/-- The retained relation has the canonical predecessor well-foundedness
used by the transaction rank construction. -/
theorem predecessorWellFounded
    (G : LiteralContactTransactionGeometry
      (Gamma := Gamma) (Y := Y) (kappa := kappa)) :
    WellFounded (fun x y : V ↦ (x, y) ∈ G.edge) :=
  ForwardOrientation.predecessor_wellFounded G.edge G.acyclic
    G.no_reverse_ray

/-- The canonical depth of the literal retained relation. -/
def rank
    (G : LiteralContactTransactionGeometry
      (Gamma := Gamma) (Y := Y) (kappa := kappa)) : V → Nat :=
  ForwardOrientation.wellFoundedDepth G.edge G.predecessorWellFounded

/-- Every retained edge strictly advances the canonical depth. -/
theorem rank_lt_of_mem_edge
    (G : LiteralContactTransactionGeometry
      (Gamma := Gamma) (Y := Y) (kappa := kappa))
    {x y : V} (hxy : (x, y) ∈ G.edge) : G.rank x < G.rank y := by
  have hstep := ForwardOrientation.wellFoundedDepth_step G.edge G.biunique
    G.predecessorWellFounded hxy
  change ForwardOrientation.wellFoundedDepth G.edge G.predecessorWellFounded x <
    ForwardOrientation.wellFoundedDepth G.edge G.predecessorWellFounded y
  omega

/-- Compile the literal relation into an honest forward orientation. -/
theorem exists_forwardOrientation
    (G : LiteralContactTransactionGeometry
      (Gamma := Gamma) (Y := Y) (kappa := kappa)) :
    ∃ O : ForwardOrientation (imaginaryGraph Gamma Y kappa),
      O.edge = G.edge :=
  ForwardOrientation.exists_forwardOrientation G.edge G.carrier
    G.edge_subset_imaginaryGraph G.endpoints_mem_carrier G.biunique G.acyclic
      G.no_reverse_ray

theorem fst_mem_carrier_of_mem_edge
    (G : LiteralContactTransactionGeometry
      (Gamma := Gamma) (Y := Y) (kappa := kappa))
    {x y : V} (hxy : (x, y) ∈ G.edge) : x ∈ G.carrier :=
  (G.endpoints_mem_carrier (x, y) hxy).1

theorem snd_mem_carrier_of_mem_edge
    (G : LiteralContactTransactionGeometry
      (Gamma := Gamma) (Y := Y) (kappa := kappa))
    {x y : V} (hxy : (x, y) ∈ G.edge) : y ∈ G.carrier :=
  (G.endpoints_mem_carrier (x, y) hxy).2

end LiteralContactTransactionGeometry

namespace GroupedContactSegmentedAssignment

variable {Z : Set Gamma.DPath} {A : SimultaneousAssignment Z Y}
variable {G : Type v}

/-- The canonical carrier of the grouped literal contact relation. -/
def contactCarrier
    (S : GroupedContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily G) : Set V :=
  {x | ∃ e ∈ S.edge, e.1 = x ∨ e.2 = x}

theorem endpoints_mem_contactCarrier
    (S : GroupedContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily G) (e : V × V) (he : e ∈ S.edge) :
    e.1 ∈ S.contactCarrier ∧ e.2 ∈ S.contactCarrier := by
  constructor
  · exact ⟨e, he, Or.inl rfl⟩
  · exact ⟨e, he, Or.inr rfl⟩

/-- The exact relation-level transaction produced by recombined-owner
grouping.  No raw-source contact-disjointness is used. -/
def literalTransactionGeometry
    (S : GroupedContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily G)
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa) :
    LiteralContactTransactionGeometry
      (Gamma := Gamma) (Y := Y) (kappa := kappa) where
  edge := S.edge
  carrier := S.contactCarrier
  edge_subset_imaginaryGraph := S.edge_subset_imaginaryGraph hclosed
  endpoints_mem_carrier := S.endpoints_mem_contactCarrier
  biunique := S.edge_biunique
  acyclic := S.edge_acyclic
  no_reverse_ray := S.edge_no_reverse_ray

@[simp] theorem literalTransactionGeometry_edge
    (S : GroupedContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily G)
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa) :
    (S.literalTransactionGeometry hclosed).edge = S.edge := rfl

@[simp] theorem literalTransactionGeometry_carrier
    (S : GroupedContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily G)
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa) :
    (S.literalTransactionGeometry hclosed).carrier = S.contactCarrier := rfl

end GroupedContactSegmentedAssignment

namespace ContactSegmentedAssignment.TransactionGeometry

variable {Z : Set Gamma.DPath} {A : SimultaneousAssignment Z Y}
variable {S : ContactSegmentedAssignment A X before innerRoof outerRoof
  closureFamily}

/-- The older source-disjoint transaction embeds in the literal
relation-level package.  This adapter lets downstream code consume either
the old special case or the recombined-owner construction through one API. -/
def toLiteralContactTransactionGeometry
    (T : S.TransactionGeometry)
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa)
    (carrier : Set V)
    (hendpoints : ∀ e ∈ T.edge, e.1 ∈ carrier ∧ e.2 ∈ carrier) :
    LiteralContactTransactionGeometry
      (Gamma := Gamma) (Y := Y) (kappa := kappa) where
  edge := T.edge
  carrier := carrier
  edge_subset_imaginaryGraph := T.edge_subset_imaginaryGraph hclosed
  endpoints_mem_carrier := hendpoints
  biunique := T.biunique
  acyclic := T.acyclic
  no_reverse_ray := T.no_reverse_ray

@[simp] theorem toLiteralContactTransactionGeometry_edge
    (T : S.TransactionGeometry)
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa)
    (carrier : Set V)
    (hendpoints : ∀ e ∈ T.edge, e.1 ∈ carrier ∧ e.2 ∈ carrier) :
    (T.toLiteralContactTransactionGeometry hclosed carrier hendpoints).edge =
      T.edge := rfl

@[simp] theorem toLiteralContactTransactionGeometry_carrier
    (T : S.TransactionGeometry)
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa)
    (carrier : Set V)
    (hendpoints : ∀ e ∈ T.edge, e.1 ∈ carrier ∧ e.2 ∈ carrier) :
    (T.toLiteralContactTransactionGeometry hclosed carrier hendpoints).carrier =
      carrier := rfl

end ContactSegmentedAssignment.TransactionGeometry

/-! ## The unconditional real part of a fractured assignment -/

namespace FracturedAssignmentPeel.BracketFracturedAssignment

variable {Z : FracturedWarp Gamma}

/-- All real directed edges contributed by forward links of the literal
fractured assignment.  Backward reference links contribute no edge; this is
the safe-switch deletion semantics, not reversal of a graph edge. -/
def retainedForwardEdges
    (B : FracturedAssignmentPeel.BracketFracturedAssignment Z Y) :
    Set (V × V) :=
  ⋃ s, (B.assignment.assigned s).directionEdges .forward

/-- Bracket provenance puts every retained real edge on the honest
recombined warp, even though the assignment is indexed by literal holes. -/
theorem retainedForwardEdges_subset_familyEdges
    (B : FracturedAssignmentPeel.BracketFracturedAssignment Z Y) :
    B.retainedForwardEdges ⊆ familyEdges Z.edgeWarp := by
  intro e he
  simp only [retainedForwardEdges, Set.mem_iUnion] at he
  obtain ⟨s, he⟩ := he
  simp only [AltPath.directionEdges, Set.mem_iUnion] at he
  obtain ⟨l, hl, hdirection, hel⟩ := he
  have hfragment : IsFragmentOf l.path Z.edgeWarp :=
    (B.bracket_safe s).isBracketAlternating.2 l hl hdirection
  rcases hfragment with ⟨p, hp, hlp⟩
  simp only [familyEdges, Set.mem_iUnion]
  exact ⟨p, hp, hlp.2 hel⟩

/-- Restricting the recombined warp relation preserves local
bi-uniqueness. -/
theorem retainedForwardEdges_biunique
    (B : FracturedAssignmentPeel.BracketFracturedAssignment Z Y) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ B.retainedForwardEdges) := by
  have hfull := Alternating.IsWarp.familyEdges_biUnique Z.edgeWarp_isWarp
  constructor
  · intro a b c hac hbc
    exact hfull.1
      (B.retainedForwardEdges_subset_familyEdges hac)
      (B.retainedForwardEdges_subset_familyEdges hbc)
  · intro a b c hab hac
    exact hfull.2
      (B.retainedForwardEdges_subset_familyEdges hab)
      (B.retainedForwardEdges_subset_familyEdges hac)

/-- A subrelation of a warp edge relation contains no directed cycle. -/
theorem retainedForwardEdges_acyclic
    (B : FracturedAssignmentPeel.BracketFracturedAssignment Z Y) :
    ¬ ContainsDirectedCycle B.retainedForwardEdges := by
  intro hcycle
  exact
    (PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsDirectedCycle
      Z.edgeWarp_isWarp)
    ⟨hcycle.choose,
      hcycle.choose_spec.trans B.retainedForwardEdges_subset_familyEdges⟩

/-- A subrelation of a warp edge relation contains no reverse directed
ray. -/
theorem retainedForwardEdges_no_reverse_ray
    (B : FracturedAssignmentPeel.BracketFracturedAssignment Z Y) :
    ¬ ContainsReverseDirectedRay B.retainedForwardEdges := by
  intro hray
  exact
    (PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsReverseDirectedRay
      Z.edgeWarp_isWarp)
    ⟨hray.choose,
      fun n ↦ B.retainedForwardEdges_subset_familyEdges
        (hray.choose_spec n)⟩

/-- Endpoint carrier of the literal real relation. -/
def retainedForwardCarrier
    (B : FracturedAssignmentPeel.BracketFracturedAssignment Z Y) : Set V :=
  {x | ∃ e ∈ B.retainedForwardEdges, e.1 = x ∨ e.2 = x}

theorem retainedForwardEdges_endpoints
    (B : FracturedAssignmentPeel.BracketFracturedAssignment Z Y)
    (e : V × V) (he : e ∈ B.retainedForwardEdges) :
    e.1 ∈ B.retainedForwardCarrier ∧ e.2 ∈ B.retainedForwardCarrier := by
  exact ⟨⟨e, he, Or.inl rfl⟩, ⟨e, he, Or.inr rfl⟩⟩

/-- Unconditional real transaction geometry of a bracket fractured
assignment.  This is the base relation to which the classified X-clean
imaginary intervals are added. -/
def retainedForwardGeometry
    (B : FracturedAssignmentPeel.BracketFracturedAssignment Z Y) :
    LiteralContactTransactionGeometry
      (Gamma := Gamma) (Y := Y) (kappa := kappa) where
  edge := B.retainedForwardEdges
  carrier := B.retainedForwardCarrier
  edge_subset_imaginaryGraph := by
    intro e he
    exact Or.inl (familyEdges_subset_adj Z.edgeWarp
      (B.retainedForwardEdges_subset_familyEdges he))
  endpoints_mem_carrier := B.retainedForwardEdges_endpoints
  biunique := B.retainedForwardEdges_biunique
  acyclic := B.retainedForwardEdges_acyclic
  no_reverse_ray := B.retainedForwardEdges_no_reverse_ray

@[simp] theorem retainedForwardGeometry_edge
    (B : FracturedAssignmentPeel.BracketFracturedAssignment Z Y) :
    (B.retainedForwardGeometry (kappa := kappa)).edge =
      B.retainedForwardEdges := rfl

@[simp] theorem retainedForwardGeometry_carrier
    (B : FracturedAssignmentPeel.BracketFracturedAssignment Z Y) :
    (B.retainedForwardGeometry (kappa := kappa)).carrier =
      B.retainedForwardCarrier := rfl

end FracturedAssignmentPeel.BracketFracturedAssignment

/-! ## Canonical linkwise classification -/

namespace FracturedAssignmentPeel.BracketFracturedAssignment

variable {Z : FracturedWarp Gamma}

/-- The dependency-free classification of one literal link occurrence.
Forward traversal retains the actual directed path and backward traversal
deletes the reference block. -/
def canonicalLinkClassification
    (l : Link Gamma.graph) :
    SingletonTransactionClassification
      (Y := Y) (X := X) (kappa := kappa) l :=
  SingletonTransactionClassification.literal l

@[simp] theorem canonicalLinkClassification_retainedEdges_forward
    (l : Link Gamma.graph) (hforward : l.direction = .forward) :
    (canonicalLinkClassification
      (Y := Y) (X := X) (kappa := kappa) l).retainedEdges =
        l.path.edgeSet := by
  cases hdirection : l.direction with
  | forward =>
      simp [canonicalLinkClassification,
        SingletonTransactionClassification.literal,
        SingletonTransactionClassification.retainedEdges, hdirection]
  | backward => simp [hdirection] at hforward

@[simp] theorem canonicalLinkClassification_retainedEdges_backward
    (l : Link Gamma.graph) (hbackward : l.direction = .backward) :
    (canonicalLinkClassification
      (Y := Y) (X := X) (kappa := kappa) l).retainedEdges = ∅ := by
  cases hdirection : l.direction with
  | forward => simp [hdirection] at hbackward
  | backward =>
      simp [canonicalLinkClassification,
        SingletonTransactionClassification.literal,
        SingletonTransactionClassification.retainedEdges, hdirection]

/-- Union of the retained relations of every classified literal link
occurrence in the simultaneous assignment.  The occurrence subtype is
important: equal link values in two selected routes remain separately
owned proof occurrences until the relation union is taken. -/
def linkwiseRetainedEdges
    (B : FracturedAssignmentPeel.BracketFracturedAssignment Z Y) :
    Set (V × V) :=
  ⋃ s, ⋃ l : {l : Link Gamma.graph //
      l ∈ (B.assignment.assigned s).links},
    (canonicalLinkClassification
      (Y := Y) (X := X) (kappa := kappa) l.1).retainedEdges

/-- Literal classification has exactly the safe-switch semantics: its
family union is the union of actual forward-link edges. -/
theorem linkwiseRetainedEdges_eq_retainedForwardEdges
    (B : FracturedAssignmentPeel.BracketFracturedAssignment Z Y) :
    B.linkwiseRetainedEdges (X := X) (kappa := kappa) =
      B.retainedForwardEdges := by
  ext e
  constructor
  · intro he
    simp only [linkwiseRetainedEdges, Set.mem_iUnion] at he
    obtain ⟨s, l, he⟩ := he
    cases hdirection : l.1.direction with
    | forward =>
        simp only [retainedForwardEdges, Set.mem_iUnion,
          AltPath.directionEdges]
        exact ⟨s, l.1, l.2, hdirection, by
          rw [canonicalLinkClassification_retainedEdges_forward
            (Y := Y) (X := X) (kappa := kappa) l.1 hdirection] at he
          exact he⟩
    | backward =>
        rw [canonicalLinkClassification_retainedEdges_backward
          (Y := Y) (X := X) (kappa := kappa) l.1 hdirection] at he
        exact he.elim
  · intro he
    simp only [retainedForwardEdges, Set.mem_iUnion,
      AltPath.directionEdges] at he
    obtain ⟨s, l, hl, hforward, he⟩ := he
    simp only [linkwiseRetainedEdges, Set.mem_iUnion]
    refine ⟨s, ⟨l, hl⟩, ?_⟩
    simpa [canonicalLinkClassification_retainedEdges_forward
      (Y := Y) (X := X) (kappa := kappa) l hforward] using he

/-- The completely unconditional linkwise transaction geometry.  This is
the concrete replacement for the old `ContactSegmentation` provider: no
closure of the later linkage and no endpoint-clean cut-piece premise is
used. -/
def canonicalLinkwiseGeometry
    (B : FracturedAssignmentPeel.BracketFracturedAssignment Z Y) :
    LiteralContactTransactionGeometry
      (Gamma := Gamma) (Y := Y) (kappa := kappa) := by
  exact {
    edge := B.linkwiseRetainedEdges (X := X) (kappa := kappa)
    carrier := B.retainedForwardCarrier
    edge_subset_imaginaryGraph := by
      rw [B.linkwiseRetainedEdges_eq_retainedForwardEdges]
      exact (B.retainedForwardGeometry
        (kappa := kappa)).edge_subset_imaginaryGraph
    endpoints_mem_carrier := by
      intro e he
      rw [B.linkwiseRetainedEdges_eq_retainedForwardEdges] at he
      exact B.retainedForwardEdges_endpoints e he
    biunique := by
      rw [B.linkwiseRetainedEdges_eq_retainedForwardEdges]
      exact B.retainedForwardEdges_biunique
    acyclic := by
      rw [B.linkwiseRetainedEdges_eq_retainedForwardEdges]
      exact B.retainedForwardEdges_acyclic
    no_reverse_ray := by
      rw [B.linkwiseRetainedEdges_eq_retainedForwardEdges]
      exact B.retainedForwardEdges_no_reverse_ray }

@[simp] theorem canonicalLinkwiseGeometry_edge
    (B : FracturedAssignmentPeel.BracketFracturedAssignment Z Y) :
    (B.canonicalLinkwiseGeometry
      (X := X) (kappa := kappa)).edge =
      B.linkwiseRetainedEdges (X := X) (kappa := kappa) := rfl

@[simp] theorem canonicalLinkwiseGeometry_carrier
    (B : FracturedAssignmentPeel.BracketFracturedAssignment Z Y) :
    (B.canonicalLinkwiseGeometry
      (X := X) (kappa := kappa)).carrier =
      B.retainedForwardCarrier := rfl

end FracturedAssignmentPeel.BracketFracturedAssignment

/-! ## Splicing the real base and the classified contact shortcuts -/

/-- Exact compatibility data for adding the classified X-clean contact
shortcuts to the unconditional real forward relation.

The two cross-incidence clauses are the only local uniqueness facts not
already supplied by the recombined warp and by grouped contact ownership.
The common rank is deliberately a construction field of the literal-order
compiler: both actual forward edges and shortcut edges must advance in the
same recombined macro order. -/
structure LiteralContactSpliceData
    {Z : FracturedWarp Gamma}
    (B : FracturedAssignmentPeel.BracketFracturedAssignment Z Y)
    (S : GroupedContactSegmentedAssignment B.assignment X before innerRoof
      outerRoof closureFamily G) where
  cross_left : ∀ {a b c},
    (a, c) ∈ B.retainedForwardEdges → (b, c) ∈ S.edge → a = b
  cross_right : ∀ {a b c},
    (a, b) ∈ B.retainedForwardEdges → (a, c) ∈ S.edge → b = c
  rank : V → Nat
  rank_forward : ∀ {a b}, (a, b) ∈ B.retainedForwardEdges →
    rank a < rank b
  rank_contact : ∀ {a b}, (a, b) ∈ S.edge → rank a < rank b

namespace LiteralContactSpliceData

variable {Z : FracturedWarp Gamma}
variable {B : FracturedAssignmentPeel.BracketFracturedAssignment Z Y}
variable {G : Type v}
variable {S : GroupedContactSegmentedAssignment B.assignment X before
  innerRoof outerRoof closureFamily G}

/-- The exact retained relation: actual forward graph edges together with
the classified X-clean contact shortcuts. -/
def edge (_D : LiteralContactSpliceData B S) : Set (V × V) :=
  B.retainedForwardEdges ∪ S.edge

/-- Endpoint carrier of the exact spliced relation. -/
def carrier (_D : LiteralContactSpliceData B S) : Set V :=
  B.retainedForwardCarrier ∪ S.contactCarrier

theorem edge_subset_imaginaryGraph
    (D : LiteralContactSpliceData B S)
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa) :
    D.edge ⊆ {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
  rintro e (he | he)
  · exact Or.inl (familyEdges_subset_adj Z.edgeWarp
      (B.retainedForwardEdges_subset_familyEdges he))
  · exact S.edge_subset_imaginaryGraph hclosed he

theorem endpoints_mem_carrier
    (D : LiteralContactSpliceData B S) (e : V × V) (he : e ∈ D.edge) :
    e.1 ∈ D.carrier ∧ e.2 ∈ D.carrier := by
  rcases he with he | he
  · have h := B.retainedForwardEdges_endpoints e he
    exact ⟨Or.inl h.1, Or.inl h.2⟩
  · have h := S.endpoints_mem_contactCarrier e he
    exact ⟨Or.inr h.1, Or.inr h.2⟩

/-- The two homogeneous uniqueness theorems and the two literal cross
incidence theorems give bi-uniqueness of the exact union. -/
theorem edge_biunique (D : LiteralContactSpliceData B S) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ D.edge) := by
  constructor
  · intro a b c hac hbc
    rcases hac with hac | hac <;> rcases hbc with hbc | hbc
    · exact B.retainedForwardEdges_biunique.1 hac hbc
    · exact D.cross_left hac hbc
    · exact (D.cross_left hbc hac).symm
    · exact S.edge_biunique.1 hac hbc
  · intro a b c hab hac
    rcases hab with hab | hab <;> rcases hac with hac | hac
    · exact B.retainedForwardEdges_biunique.2 hab hac
    · exact D.cross_right hab hac
    · exact (D.cross_right hac hab).symm
    · exact S.edge_biunique.2 hab hac

theorem rank_lt_of_mem_edge (D : LiteralContactSpliceData B S)
    {a b : V} (hab : (a, b) ∈ D.edge) : D.rank a < D.rank b := by
  rcases hab with hab | hab
  · exact D.rank_forward hab
  · exact D.rank_contact hab

theorem edge_acyclic (D : LiteralContactSpliceData B S) :
    ¬ ContainsDirectedCycle D.edge :=
  Alternating.GenericSimultaneousSwitch.not_containsDirectedCycle_of_wellFoundedRank
    D.edge D.rank D.rank_lt_of_mem_edge

theorem edge_no_reverse_ray (D : LiteralContactSpliceData B S) :
    ¬ ContainsReverseDirectedRay D.edge :=
  Alternating.GenericSimultaneousSwitch.not_containsReverseDirectedRay_of_wellFoundedRank
    D.edge D.rank D.rank_lt_of_mem_edge

/-- Compile the exact real-plus-shortcut relation to transaction geometry. -/
def literalTransactionGeometry
    (D : LiteralContactSpliceData B S)
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa) :
    LiteralContactTransactionGeometry
      (Gamma := Gamma) (Y := Y) (kappa := kappa) where
  edge := D.edge
  carrier := D.carrier
  edge_subset_imaginaryGraph := D.edge_subset_imaginaryGraph hclosed
  endpoints_mem_carrier := D.endpoints_mem_carrier
  biunique := D.edge_biunique
  acyclic := D.edge_acyclic
  no_reverse_ray := D.edge_no_reverse_ray

@[simp] theorem literalTransactionGeometry_edge
    (D : LiteralContactSpliceData B S)
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa) :
    (D.literalTransactionGeometry hclosed).edge =
      B.retainedForwardEdges ∪ S.edge := rfl

@[simp] theorem literalTransactionGeometry_carrier
    (D : LiteralContactSpliceData B S)
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa) :
    (D.literalTransactionGeometry hclosed).carrier =
      B.retainedForwardCarrier ∪ S.contactCarrier := rfl

end LiteralContactSpliceData

end LinkageBlueprint
end Blueprint
end Erdos599
