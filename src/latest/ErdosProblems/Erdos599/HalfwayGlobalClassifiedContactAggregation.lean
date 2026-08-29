/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayGlobalClassifiedContactAccounting

/-!
# Aggregating globally reclassified contact pieces

This file lifts the direction-preserving, piecewise limiting-reference
classification to a whole classified contact chain and then to a grouped
assignment.  The resulting relation is the literal forward base together
with precisely the shortcuts which survive the global reclassification.

The boundary conclusions deliberately remember both endpoints of every
deleted shortcut.  The available classification says that one of those
endpoints has a limiting-reference owner; it does not, by itself, say that
the newly exposed root or sink is the covered endpoint.  No full successor,
source-cover, or cross-bi-uniqueness conclusion is asserted here.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder Alternating
open Alternating.RelationDecomposition

universe u v

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {X persistent : Set V} {kappa : Cardinal.{u}}

namespace ClassifiedContactChain

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {Q : AltPath Gamma.graph} {I J : Type v}

/-- The shortcuts which survive piecewise reclassification against the
limiting reference. -/
def limitingShortcutEdges
    (K : ClassifiedContactChain
      (Y := C.selectedReference) (kappa := kappa) Q X I J)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) : Set (V × V) :=
  ⋃ i, (K.piece i).limitingShortcutEdges hSafeRoof

/-- All edge contributions of the reclassified pieces.  Covered pieces
contribute their literal forward edges. -/
def limitingRetainedEdges
    (K : ClassifiedContactChain
      (Y := C.selectedReference) (kappa := kappa) Q X I J)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) : Set (V × V) :=
  ⋃ i, (K.piece i).limitingRetainedEdges hSafeRoof

theorem limitingShortcutEdges_subset_shortcutEdges
    (K : ClassifiedContactChain
      (Y := C.selectedReference) (kappa := kappa) Q X I J)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    K.limitingShortcutEdges hSafeRoof ⊆ K.shortcutEdges := by
  intro e he
  simp only [limitingShortcutEdges, Set.mem_iUnion] at he
  obtain ⟨i, he⟩ := he
  simp only [shortcutEdges, Set.mem_iUnion]
  exact ⟨i, (K.piece i).limitingShortcutEdges_subset_shortcutEdges
    hSafeRoof he⟩

theorem limitingShortcutEdges_subset_imaginaryGraph
    (K : ClassifiedContactChain
      (Y := C.selectedReference) (kappa := kappa) Q X I J)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    K.limitingShortcutEdges hSafeRoof ⊆
      {e | (imaginaryGraph Gamma C.ladder.limitWarp kappa).Adj e.1 e.2} := by
  intro e he
  simp only [limitingShortcutEdges, Set.mem_iUnion] at he
  obtain ⟨i, he⟩ := he
  exact ((K.piece i).globalize hSafeRoof).shortcutEdges_subset_imaginaryGraph
    he

theorem limitingRetainedEdges_subset_originalForward_union_shortcut
    (K : ClassifiedContactChain
      (Y := C.selectedReference) (kappa := kappa) Q X I J)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    K.limitingRetainedEdges hSafeRoof ⊆
      Q.directionEdges .forward ∪ K.shortcutEdges := by
  intro e he
  simp only [limitingRetainedEdges, Set.mem_iUnion] at he
  obtain ⟨i, he⟩ := he
  rcases (K.piece i).limitingRetainedEdges_subset_originalForward_union_shortcut
      hSafeRoof he with he | he
  · exact Or.inl he
  · exact Or.inr (Set.mem_iUnion.2 ⟨i, he⟩)

theorem limitingShortcutEdges_biUnique
    (K : ClassifiedContactChain
      (Y := C.selectedReference) (kappa := kappa) Q X I J)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    Relator.BiUnique
      (fun x y ↦ (x, y) ∈ K.limitingShortcutEdges hSafeRoof) := by
  constructor
  · intro a b c hac hbc
    exact K.shortcutEdges_biUnique.1
      (K.limitingShortcutEdges_subset_shortcutEdges hSafeRoof hac)
      (K.limitingShortcutEdges_subset_shortcutEdges hSafeRoof hbc)
  · intro a b c hab hac
    exact K.shortcutEdges_biUnique.2
      (K.limitingShortcutEdges_subset_shortcutEdges hSafeRoof hab)
      (K.limitingShortcutEdges_subset_shortcutEdges hSafeRoof hac)

theorem contactRank_lt_of_mem_limitingShortcutEdges
    (K : ClassifiedContactChain
      (Y := C.selectedReference) (kappa := kappa) Q X I J)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    {a b : V} (hab : (a, b) ∈ K.limitingShortcutEdges hSafeRoof) :
    K.contactRank a < K.contactRank b :=
  K.contactRank_lt_of_mem_shortcutEdges
    (K.limitingShortcutEdges_subset_shortcutEdges hSafeRoof hab)

theorem limitingShortcutEdges_acyclic
    (K : ClassifiedContactChain
      (Y := C.selectedReference) (kappa := kappa) Q X I J)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    ¬ ContainsDirectedCycle (K.limitingShortcutEdges hSafeRoof) :=
  Alternating.GenericSimultaneousSwitch.not_containsDirectedCycle_of_wellFoundedRank
    (K.limitingShortcutEdges hSafeRoof) K.contactRank
    (K.contactRank_lt_of_mem_limitingShortcutEdges hSafeRoof)

theorem limitingShortcutEdges_no_reverse_ray
    (K : ClassifiedContactChain
      (Y := C.selectedReference) (kappa := kappa) Q X I J)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    ¬ ContainsReverseDirectedRay (K.limitingShortcutEdges hSafeRoof) :=
  Alternating.GenericSimultaneousSwitch.not_containsReverseDirectedRay_of_wellFoundedRank
    (K.limitingShortcutEdges hSafeRoof) K.contactRank
    (K.contactRank_lt_of_mem_limitingShortcutEdges hSafeRoof)

/-- Every deleted local shortcut has a concrete limiting-reference owner at
one of its endpoints. -/
theorem omittedShortcut_covered
    (K : ClassifiedContactChain
      (Y := C.selectedReference) (kappa := kappa) Q X I J)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    {a b : V} (hab : (a, b) ∈ K.shortcutEdges)
    (hnot : (a, b) ∉ K.limitingShortcutEdges hSafeRoof) :
    Nonempty (ClubStageGeometry.LimitingReferenceEndpointOwner C a) ∨
      Nonempty (ClubStageGeometry.LimitingReferenceEndpointOwner C b) := by
  simp only [shortcutEdges, Set.mem_iUnion] at hab
  obtain ⟨i, hab⟩ := hab
  have hpair := (K.piece i).mem_shortcutEdges_eq hab
  have ha : a = K.point (K.source i) := congrArg Prod.fst hpair
  have hb : b = K.point (K.target i) := congrArg Prod.snd hpair
  subst a
  subst b
  have hnotPiece : (K.point (K.source i), K.point (K.target i)) ∉
      (K.piece i).limitingShortcutEdges hSafeRoof := by
    intro h
    apply hnot
    exact Set.mem_iUnion.2 ⟨i, h⟩
  exact ((K.piece i).covered_of_not_mem_limitingShortcut hSafeRoof hab
    hnotPiece).1

end ClassifiedContactChain

namespace ClassifiedContactSegmentation

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {Q : AltPath Gamma.graph}

def limitingShortcutEdges
    (S : ClassifiedContactSegmentation
      (Y := C.selectedReference) (kappa := kappa) Q X persistent)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) : Set (V × V) :=
  match S with
  | .finite T => T.toChain.limitingShortcutEdges hSafeRoof
  | .eventually T => T.toChain.limitingShortcutEdges hSafeRoof
  | .omega T => T.toChain.limitingShortcutEdges hSafeRoof

def limitingRetainedEdges
    (S : ClassifiedContactSegmentation
      (Y := C.selectedReference) (kappa := kappa) Q X persistent)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) : Set (V × V) :=
  match S with
  | .finite T => T.toChain.limitingRetainedEdges hSafeRoof
  | .eventually T =>
      T.toChain.limitingRetainedEdges hSafeRoof ∪
        T.tail.limitingRetainedEdges hSafeRoof
  | .omega T => T.toChain.limitingRetainedEdges hSafeRoof

theorem limitingShortcutEdges_subset_shortcutEdges
    (S : ClassifiedContactSegmentation
      (Y := C.selectedReference) (kappa := kappa) Q X persistent)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    S.limitingShortcutEdges hSafeRoof ⊆ S.shortcutEdges := by
  cases S with
  | finite T => exact T.toChain.limitingShortcutEdges_subset_shortcutEdges hSafeRoof
  | eventually T => exact T.toChain.limitingShortcutEdges_subset_shortcutEdges hSafeRoof
  | omega T => exact T.toChain.limitingShortcutEdges_subset_shortcutEdges hSafeRoof

theorem limitingShortcutEdges_subset_imaginaryGraph
    (S : ClassifiedContactSegmentation
      (Y := C.selectedReference) (kappa := kappa) Q X persistent)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    S.limitingShortcutEdges hSafeRoof ⊆
      {e | (imaginaryGraph Gamma C.ladder.limitWarp kappa).Adj e.1 e.2} := by
  cases S with
  | finite T => exact T.toChain.limitingShortcutEdges_subset_imaginaryGraph hSafeRoof
  | eventually T => exact T.toChain.limitingShortcutEdges_subset_imaginaryGraph hSafeRoof
  | omega T => exact T.toChain.limitingShortcutEdges_subset_imaginaryGraph hSafeRoof

theorem limitingRetainedEdges_subset_originalForward_union_shortcut
    (S : ClassifiedContactSegmentation
      (Y := C.selectedReference) (kappa := kappa) Q X persistent)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    S.limitingRetainedEdges hSafeRoof ⊆
      Q.directionEdges .forward ∪ S.shortcutEdges := by
  cases S with
  | finite T =>
      exact T.toChain.limitingRetainedEdges_subset_originalForward_union_shortcut
        hSafeRoof
  | eventually T =>
      rintro e (he | he)
      · exact T.toChain.limitingRetainedEdges_subset_originalForward_union_shortcut
          hSafeRoof he
      · exact Or.inl (T.tail.limitingRetainedEdges_subset_originalForward
          hSafeRoof he)
  | omega T =>
      exact T.toChain.limitingRetainedEdges_subset_originalForward_union_shortcut
        hSafeRoof

theorem omittedShortcut_covered
    (S : ClassifiedContactSegmentation
      (Y := C.selectedReference) (kappa := kappa) Q X persistent)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    {a b : V} (hab : (a, b) ∈ S.shortcutEdges)
    (hnot : (a, b) ∉ S.limitingShortcutEdges hSafeRoof) :
    Nonempty (ClubStageGeometry.LimitingReferenceEndpointOwner C a) ∨
      Nonempty (ClubStageGeometry.LimitingReferenceEndpointOwner C b) := by
  cases S with
  | finite T => exact T.toChain.omittedShortcut_covered hSafeRoof hab hnot
  | eventually T => exact T.toChain.omittedShortcut_covered hSafeRoof hab hnot
  | omega T => exact T.toChain.omittedShortcut_covered hSafeRoof hab hnot

end ClassifiedContactSegmentation

namespace GroupedClassifiedContactSegmentedAssignment

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {Z : Set Gamma.DPath}
variable {A : SimultaneousAssignment Z C.selectedReference}
variable {G : Type v}

/-- Global shortcuts, still grouped by the actual original-row owner. -/
def limitingShortcutEdges
    (S : GroupedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) : Set (V × V) :=
  ⋃ s, (S.segmentation s).limitingShortcutEdges hSafeRoof

/-- The real base which must be retained independently of the shortcut
classification. -/
def assignedForwardEdges
    (_S : GroupedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G) : Set (V × V) :=
  ⋃ s, (A.assigned s).directionEdges .forward

/-- The local relation before limiting-reference reclassification. -/
def localEdge
    (S : GroupedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G) : Set (V × V) :=
  S.assignedForwardEdges ∪ S.edge

/-- The corrected relation after limiting-reference reclassification. -/
def limitingEdge
    (S : GroupedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) : Set (V × V) :=
  S.assignedForwardEdges ∪ S.limitingShortcutEdges hSafeRoof

theorem limitingShortcutEdges_subset_edge
    (S : GroupedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    S.limitingShortcutEdges hSafeRoof ⊆ S.edge := by
  intro e he
  simp only [limitingShortcutEdges, Set.mem_iUnion] at he
  obtain ⟨s, he⟩ := he
  simp only [edge, Set.mem_iUnion]
  exact ⟨s, (S.segmentation s).limitingShortcutEdges_subset_shortcutEdges
    hSafeRoof he⟩

theorem limitingShortcutEdges_subset_imaginaryGraph
    (S : GroupedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    S.limitingShortcutEdges hSafeRoof ⊆
      {e | (imaginaryGraph Gamma C.ladder.limitWarp kappa).Adj e.1 e.2} := by
  intro e he
  simp only [limitingShortcutEdges, Set.mem_iUnion] at he
  obtain ⟨s, he⟩ := he
  exact (S.segmentation s).limitingShortcutEdges_subset_imaginaryGraph
    hSafeRoof he

theorem limitingEdge_subset_localEdge
    (S : GroupedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    S.limitingEdge hSafeRoof ⊆ S.localEdge := by
  rintro e (he | he)
  · exact Or.inl he
  · exact Or.inr (S.limitingShortcutEdges_subset_edge hSafeRoof he)

theorem omittedShortcut_covered
    (S : GroupedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    {a b : V} (hab : (a, b) ∈ S.edge)
    (hnot : (a, b) ∉ S.limitingShortcutEdges hSafeRoof) :
    Nonempty (ClubStageGeometry.LimitingReferenceEndpointOwner C a) ∨
      Nonempty (ClubStageGeometry.LimitingReferenceEndpointOwner C b) := by
  simp only [edge, Set.mem_iUnion] at hab
  obtain ⟨s, hab⟩ := hab
  have hnotS : (a, b) ∉
      (S.segmentation s).limitingShortcutEdges hSafeRoof := by
    intro h
    apply hnot
    exact Set.mem_iUnion.2 ⟨s, h⟩
  exact (S.segmentation s).omittedShortcut_covered hSafeRoof hab hnotS

/-- A root exposed by global reclassification is either already a root of
the local literal-plus-shortcut relation, or is the head of an omitted
shortcut whose endpoint pair has a limiting-reference owner. -/
theorem limitingRoots_subset_localRoots_union_coveredHeads
    (S : GroupedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (carrier : Set V) :
    {x | x ∈ carrier ∧ ¬ ∃ y, (y, x) ∈ S.limitingEdge hSafeRoof} ⊆
      {x | x ∈ carrier ∧ ¬ ∃ y, (y, x) ∈ S.localEdge} ∪
      {x | x ∈ carrier ∧ ∃ y, (y, x) ∈ S.edge ∧
        (Nonempty (ClubStageGeometry.LimitingReferenceEndpointOwner C y) ∨
          Nonempty (ClubStageGeometry.LimitingReferenceEndpointOwner C x))} := by
  intro x hx
  by_cases hold : ∃ y, (y, x) ∈ S.localEdge
  · right
    obtain ⟨y, hyx⟩ := hold
    rcases hyx with hyx | hyx
    · exact False.elim (hx.2 ⟨y, Or.inl hyx⟩)
    · have hnot : (y, x) ∉ S.limitingShortcutEdges hSafeRoof := by
        intro h
        exact hx.2 ⟨y, Or.inr h⟩
      exact ⟨hx.1, y, hyx, S.omittedShortcut_covered hSafeRoof hyx hnot⟩
  · exact Or.inl ⟨hx.1, hold⟩

/-- Sink counterpart of `limitingRoots_subset_localRoots_union_coveredHeads`.
The pairwise owner disjunction is retained rather than silently identifying
the covered endpoint with the newly exposed sink. -/
theorem limitingSinks_subset_localSinks_union_coveredTails
    (S : GroupedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (carrier : Set V) :
    {x | x ∈ carrier ∧ ¬ ∃ y, (x, y) ∈ S.limitingEdge hSafeRoof} ⊆
      {x | x ∈ carrier ∧ ¬ ∃ y, (x, y) ∈ S.localEdge} ∪
      {x | x ∈ carrier ∧ ∃ y, (x, y) ∈ S.edge ∧
        (Nonempty (ClubStageGeometry.LimitingReferenceEndpointOwner C x) ∨
          Nonempty (ClubStageGeometry.LimitingReferenceEndpointOwner C y))} := by
  intro x hx
  by_cases hold : ∃ y, (x, y) ∈ S.localEdge
  · right
    obtain ⟨y, hxy⟩ := hold
    rcases hxy with hxy | hxy
    · exact False.elim (hx.2 ⟨y, Or.inl hxy⟩)
    · have hnot : (x, y) ∉ S.limitingShortcutEdges hSafeRoof := by
        intro h
        exact hx.2 ⟨y, Or.inr h⟩
      exact ⟨hx.1, y, hxy, S.omittedShortcut_covered hSafeRoof hxy hnot⟩
  · exact Or.inl ⟨hx.1, hold⟩

end GroupedClassifiedContactSegmentedAssignment

#print axioms ClassifiedContactChain.omittedShortcut_covered
#print axioms GroupedClassifiedContactSegmentedAssignment.omittedShortcut_covered
#print axioms GroupedClassifiedContactSegmentedAssignment.limitingRoots_subset_localRoots_union_coveredHeads
#print axioms GroupedClassifiedContactSegmentedAssignment.limitingSinks_subset_localSinks_union_coveredTails

end Erdos599.Blueprint.LinkageBlueprint
