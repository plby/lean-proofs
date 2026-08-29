/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayClosedClassifiedContactSegmentation
import ErdosProblems.Erdos599.HalfwayGlobalClassifiedContactBoundary

/-!
# Global accounting for classified-or-closed contact segmentations

This module globalizes the additive mixed segmentation hierarchy.  A
classified piece is reclassified against the limiting reference exactly as
before.  A piece wholly contained in the closed set is never assigned an
outside classification: it contributes no shortcut and retains its literal
forward edges.

Thus every shortcut, every omitted-shortcut argument, and every exposed
boundary argument still comes from a genuine classified outside piece.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder Alternating
open Alternating.RelationDecomposition

universe u v

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {X persistent : Set V} {kappa : Cardinal.{u}}

namespace ClassifiedOrClosedFiniteContactPiece

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {Q : AltPath Gamma.graph} {u v : V}

/-- The shortcuts which survive limiting-reference reclassification.  A
closed piece has no shortcut before or after reclassification. -/
def limitingShortcutEdges
    (P : ClassifiedOrClosedFiniteContactPiece
      (Y := C.selectedReference) (kappa := kappa) Q X u v)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) : Set (V × V) :=
  match P with
  | .classified R => R.limitingShortcutEdges hSafeRoof
  | .closed _ => ∅

/-- The limiting retained base.  Closed pieces retain their literal forward
edges without passing through an outside classification. -/
def limitingRetainedEdges
    (P : ClassifiedOrClosedFiniteContactPiece
      (Y := C.selectedReference) (kappa := kappa) Q X u v)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) : Set (V × V) :=
  match P with
  | .classified R => R.limitingRetainedEdges hSafeRoof
  | .closed R => R.path.directionEdges .forward

theorem limitingShortcutEdges_subset_shortcutEdges
    (P : ClassifiedOrClosedFiniteContactPiece
      (Y := C.selectedReference) (kappa := kappa) Q X u v)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    P.limitingShortcutEdges hSafeRoof ⊆ P.shortcutEdges := by
  cases P with
  | classified R => exact R.limitingShortcutEdges_subset_shortcutEdges hSafeRoof
  | closed R => exact Set.Subset.rfl

theorem limitingShortcutEdges_subset_imaginaryGraph
    (P : ClassifiedOrClosedFiniteContactPiece
      (Y := C.selectedReference) (kappa := kappa) Q X u v)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    P.limitingShortcutEdges hSafeRoof ⊆
      {e | (imaginaryGraph Gamma C.ladder.limitWarp kappa).Adj e.1 e.2} := by
  cases P with
  | classified R =>
      exact (R.globalize hSafeRoof).shortcutEdges_subset_imaginaryGraph
  | closed R => simp [limitingShortcutEdges]

theorem limitingRetainedEdges_subset_originalForward_union_shortcut
    (P : ClassifiedOrClosedFiniteContactPiece
      (Y := C.selectedReference) (kappa := kappa) Q X u v)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    P.limitingRetainedEdges hSafeRoof ⊆
      Q.directionEdges .forward ∪ P.shortcutEdges := by
  cases P with
  | classified R =>
      exact R.limitingRetainedEdges_subset_originalForward_union_shortcut
        hSafeRoof
  | closed R =>
      intro e he
      exact Or.inl (R.forwardEdges_subset_original he)

theorem limitingRetainedEdges_subset_imaginaryGraph
    (P : ClassifiedOrClosedFiniteContactPiece
      (Y := C.selectedReference) (kappa := kappa) Q X u v)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    P.limitingRetainedEdges hSafeRoof ⊆
      {e | (imaginaryGraph Gamma C.ladder.limitWarp kappa).Adj e.1 e.2} := by
  cases P with
  | classified R => exact R.limitingRetainedEdges_subset_imaginaryGraph hSafeRoof
  | closed R =>
      intro e he
      change e ∈ R.path.directionEdges .forward at he
      have heEdge : e ∈ R.path.edgeSet := by
        simp only [AltPath.directionEdges, Set.mem_iUnion] at he
        obtain ⟨l, hl, _hforward, hel⟩ := he
        rw [R.path.edgeSet_eq_iUnion_links]
        simp only [Set.mem_iUnion]
        exact ⟨l, hl, hel⟩
      exact Or.inl (R.path.edgeSet_subset_adj heEdge)

/-- Any omitted mixed shortcut comes from a genuine classified piece and
therefore has the same limiting-reference endpoint owner as before. -/
theorem covered_of_not_mem_limitingShortcut
    (P : ClassifiedOrClosedFiniteContactPiece
      (Y := C.selectedReference) (kappa := kappa) Q X u v)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (hlocal : (u, v) ∈ P.shortcutEdges)
    (hglobal : (u, v) ∉ P.limitingShortcutEdges hSafeRoof) :
    Nonempty (ClubStageGeometry.LimitingReferenceEndpointOwner C u) ∨
      Nonempty (ClubStageGeometry.LimitingReferenceEndpointOwner C v) := by
  cases P with
  | classified R =>
      exact (R.covered_of_not_mem_limitingShortcut hSafeRoof hlocal hglobal).1
  | closed R => simp [shortcutEdges] at hlocal

/-- Closed pieces need no backward-owner certificate because they create no
shortcut.  Classified pieces retain the literal bracket certificate used by
the endpoint-specific boundary argument. -/
def ClassifiedBackwardLinksOn
    (P : ClassifiedOrClosedFiniteContactPiece
      (Y := C.selectedReference) (kappa := kappa) Q X u v) : Prop :=
  match P with
  | .classified R => BackwardLinksOn C.selectedReference R.path
  | .closed _ => True

theorem terminal_mem_limitWarp_of_omittedShortcut_of_noIncoming
    (P : ClassifiedOrClosedFiniteContactPiece
      (Y := C.selectedReference) (kappa := kappa) Q X u v)
    (hback : P.ClassifiedBackwardLinksOn)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (hlocal : (u, v) ∈ P.shortcutEdges)
    (hglobal : (u, v) ∉ P.limitingShortcutEdges hSafeRoof)
    (hno : ¬ ∃ x, (x, v) ∈ P.path.directionEdges .forward) :
    v ∈ Gamma.vertexSet C.ladder.limitWarp := by
  cases P with
  | classified R =>
      exact R.terminal_mem_limitWarp_of_omittedShortcut_of_noIncoming
        hback hSafeRoof hlocal hglobal hno
  | closed R => simp [shortcutEdges] at hlocal

theorem initial_mem_limitWarp_of_omittedShortcut_of_noOutgoing
    (P : ClassifiedOrClosedFiniteContactPiece
      (Y := C.selectedReference) (kappa := kappa) Q X u v)
    (hback : P.ClassifiedBackwardLinksOn)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (hlocal : (u, v) ∈ P.shortcutEdges)
    (hglobal : (u, v) ∉ P.limitingShortcutEdges hSafeRoof)
    (hno : ¬ ∃ y, (u, y) ∈ P.path.directionEdges .forward) :
    u ∈ Gamma.vertexSet C.ladder.limitWarp := by
  cases P with
  | classified R =>
      exact R.initial_mem_limitWarp_of_omittedShortcut_of_noOutgoing
        hback hSafeRoof hlocal hglobal hno
  | closed R => simp [shortcutEdges] at hlocal

end ClassifiedOrClosedFiniteContactPiece

namespace ClosedClassifiedContactChain

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {Q : AltPath Gamma.graph} {I J : Type v}

def limitingShortcutEdges
    (K : ClosedClassifiedContactChain
      (Y := C.selectedReference) (kappa := kappa) Q X I J)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) : Set (V × V) :=
  ⋃ i, (K.piece i).limitingShortcutEdges hSafeRoof

def limitingRetainedEdges
    (K : ClosedClassifiedContactChain
      (Y := C.selectedReference) (kappa := kappa) Q X I J)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) : Set (V × V) :=
  ⋃ i, (K.piece i).limitingRetainedEdges hSafeRoof

theorem limitingShortcutEdges_subset_shortcutEdges
    (K : ClosedClassifiedContactChain
      (Y := C.selectedReference) (kappa := kappa) Q X I J)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    K.limitingShortcutEdges hSafeRoof ⊆ K.shortcutEdges := by
  intro e he
  simp only [limitingShortcutEdges, Set.mem_iUnion] at he
  obtain ⟨i, he⟩ := he
  exact Set.mem_iUnion.2
    ⟨i, (K.piece i).limitingShortcutEdges_subset_shortcutEdges hSafeRoof he⟩

theorem limitingShortcutEdges_subset_imaginaryGraph
    (K : ClosedClassifiedContactChain
      (Y := C.selectedReference) (kappa := kappa) Q X I J)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    K.limitingShortcutEdges hSafeRoof ⊆
      {e | (imaginaryGraph Gamma C.ladder.limitWarp kappa).Adj e.1 e.2} := by
  intro e he
  simp only [limitingShortcutEdges, Set.mem_iUnion] at he
  obtain ⟨i, he⟩ := he
  exact (K.piece i).limitingShortcutEdges_subset_imaginaryGraph hSafeRoof he

theorem limitingRetainedEdges_subset_originalForward_union_shortcut
    (K : ClosedClassifiedContactChain
      (Y := C.selectedReference) (kappa := kappa) Q X I J)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    K.limitingRetainedEdges hSafeRoof ⊆
      Q.directionEdges .forward ∪ K.shortcutEdges := by
  intro e he
  simp only [limitingRetainedEdges, Set.mem_iUnion] at he
  obtain ⟨i, he⟩ := he
  rcases (K.piece i)
      |>.limitingRetainedEdges_subset_originalForward_union_shortcut
        hSafeRoof he with he | he
  · exact Or.inl he
  · exact Or.inr (Set.mem_iUnion.2 ⟨i, he⟩)

theorem limitingShortcutEdges_biUnique
    (K : ClosedClassifiedContactChain
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
    (K : ClosedClassifiedContactChain
      (Y := C.selectedReference) (kappa := kappa) Q X I J)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    {a b : V} (hab : (a, b) ∈ K.limitingShortcutEdges hSafeRoof) :
    K.contactRank a < K.contactRank b :=
  K.contactRank_lt_of_mem_shortcutEdges
    (K.limitingShortcutEdges_subset_shortcutEdges hSafeRoof hab)

theorem limitingShortcutEdges_acyclic
    (K : ClosedClassifiedContactChain
      (Y := C.selectedReference) (kappa := kappa) Q X I J)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    ¬ ContainsDirectedCycle (K.limitingShortcutEdges hSafeRoof) :=
  Alternating.GenericSimultaneousSwitch.not_containsDirectedCycle_of_wellFoundedRank
    (K.limitingShortcutEdges hSafeRoof) K.contactRank
    (K.contactRank_lt_of_mem_limitingShortcutEdges hSafeRoof)

theorem limitingShortcutEdges_no_reverse_ray
    (K : ClosedClassifiedContactChain
      (Y := C.selectedReference) (kappa := kappa) Q X I J)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    ¬ ContainsReverseDirectedRay (K.limitingShortcutEdges hSafeRoof) :=
  Alternating.GenericSimultaneousSwitch.not_containsReverseDirectedRay_of_wellFoundedRank
    (K.limitingShortcutEdges hSafeRoof) K.contactRank
    (K.contactRank_lt_of_mem_limitingShortcutEdges hSafeRoof)

theorem omittedShortcut_covered
    (K : ClosedClassifiedContactChain
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
  apply (K.piece i).covered_of_not_mem_limitingShortcut hSafeRoof hab
  intro h
  exact hnot (Set.mem_iUnion.2 ⟨i, h⟩)

theorem omittedShortcut_head_mem_limitWarp_of_noIncomingOriginalForward
    (K : ClosedClassifiedContactChain
      (Y := C.selectedReference) (kappa := kappa) Q X I J)
    (hback : ∀ i, (K.piece i).ClassifiedBackwardLinksOn)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    {a b : V} (hab : (a, b) ∈ K.shortcutEdges)
    (hnot : (a, b) ∉ K.limitingShortcutEdges hSafeRoof)
    (hno : ¬ ∃ x, (x, b) ∈ Q.directionEdges .forward) :
    b ∈ Gamma.vertexSet C.ladder.limitWarp := by
  simp only [shortcutEdges, Set.mem_iUnion] at hab
  obtain ⟨i, hab⟩ := hab
  have hpair := (K.piece i).mem_shortcutEdges_eq hab
  have ha : a = K.point (K.source i) := congrArg Prod.fst hpair
  have hb : b = K.point (K.target i) := congrArg Prod.snd hpair
  subst a
  subst b
  apply (K.piece i).terminal_mem_limitWarp_of_omittedShortcut_of_noIncoming
    (hback i) hSafeRoof hab
  · intro h
    exact hnot (Set.mem_iUnion.2 ⟨i, h⟩)
  · rintro ⟨x, hx⟩
    exact hno ⟨x, (K.piece i).forwardEdges_subset_original hx⟩

theorem omittedShortcut_tail_mem_limitWarp_of_noOutgoingOriginalForward
    (K : ClosedClassifiedContactChain
      (Y := C.selectedReference) (kappa := kappa) Q X I J)
    (hback : ∀ i, (K.piece i).ClassifiedBackwardLinksOn)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    {a b : V} (hab : (a, b) ∈ K.shortcutEdges)
    (hnot : (a, b) ∉ K.limitingShortcutEdges hSafeRoof)
    (hno : ¬ ∃ y, (a, y) ∈ Q.directionEdges .forward) :
    a ∈ Gamma.vertexSet C.ladder.limitWarp := by
  simp only [shortcutEdges, Set.mem_iUnion] at hab
  obtain ⟨i, hab⟩ := hab
  have hpair := (K.piece i).mem_shortcutEdges_eq hab
  have ha : a = K.point (K.source i) := congrArg Prod.fst hpair
  have hb : b = K.point (K.target i) := congrArg Prod.snd hpair
  subst a
  subst b
  apply (K.piece i).initial_mem_limitWarp_of_omittedShortcut_of_noOutgoing
    (hback i) hSafeRoof hab
  · intro h
    exact hnot (Set.mem_iUnion.2 ⟨i, h⟩)
  · rintro ⟨y, hy⟩
    exact hno ⟨y, (K.piece i).forwardEdges_subset_original hy⟩

end ClosedClassifiedContactChain

namespace ClosedClassifiedContactSegmentation

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {Q : AltPath Gamma.graph}

def limitingShortcutEdges
    (S : ClosedClassifiedContactSegmentation
      (Y := C.selectedReference) (kappa := kappa) Q X persistent)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) : Set (V × V) :=
  match S with
  | .finite T => T.toChain.limitingShortcutEdges hSafeRoof
  | .eventually T => T.toChain.limitingShortcutEdges hSafeRoof
  | .omega T => T.toChain.limitingShortcutEdges hSafeRoof

def limitingRetainedEdges
    (S : ClosedClassifiedContactSegmentation
      (Y := C.selectedReference) (kappa := kappa) Q X persistent)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) : Set (V × V) :=
  match S with
  | .finite T => T.toChain.limitingRetainedEdges hSafeRoof
  | .eventually T =>
      T.toChain.limitingRetainedEdges hSafeRoof ∪
        T.tail.limitingRetainedEdges hSafeRoof
  | .omega T => T.toChain.limitingRetainedEdges hSafeRoof

def FinitePiecesBackwardLinksOn
    (S : ClosedClassifiedContactSegmentation
      (Y := C.selectedReference) (kappa := kappa) Q X persistent) : Prop :=
  match S with
  | .finite T => ∀ i, (T.piece i).ClassifiedBackwardLinksOn
  | .eventually T => ∀ i, (T.piece i).ClassifiedBackwardLinksOn
  | .omega T => ∀ i, (T.piece i).ClassifiedBackwardLinksOn

theorem limitingShortcutEdges_subset_shortcutEdges
    (S : ClosedClassifiedContactSegmentation
      (Y := C.selectedReference) (kappa := kappa) Q X persistent)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    S.limitingShortcutEdges hSafeRoof ⊆ S.shortcutEdges := by
  cases S with
  | finite T => exact T.toChain.limitingShortcutEdges_subset_shortcutEdges hSafeRoof
  | eventually T =>
      exact T.toChain.limitingShortcutEdges_subset_shortcutEdges hSafeRoof
  | omega T => exact T.toChain.limitingShortcutEdges_subset_shortcutEdges hSafeRoof

theorem limitingShortcutEdges_subset_imaginaryGraph
    (S : ClosedClassifiedContactSegmentation
      (Y := C.selectedReference) (kappa := kappa) Q X persistent)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    S.limitingShortcutEdges hSafeRoof ⊆
      {e | (imaginaryGraph Gamma C.ladder.limitWarp kappa).Adj e.1 e.2} := by
  cases S with
  | finite T => exact T.toChain.limitingShortcutEdges_subset_imaginaryGraph hSafeRoof
  | eventually T =>
      exact T.toChain.limitingShortcutEdges_subset_imaginaryGraph hSafeRoof
  | omega T => exact T.toChain.limitingShortcutEdges_subset_imaginaryGraph hSafeRoof

theorem limitingRetainedEdges_subset_originalForward_union_shortcut
    (S : ClosedClassifiedContactSegmentation
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
      · exact T.toChain
          |>.limitingRetainedEdges_subset_originalForward_union_shortcut
            hSafeRoof he
      · exact Or.inl
          (T.tail.limitingRetainedEdges_subset_originalForward hSafeRoof he)
  | omega T =>
      exact T.toChain.limitingRetainedEdges_subset_originalForward_union_shortcut
        hSafeRoof

theorem omittedShortcut_covered
    (S : ClosedClassifiedContactSegmentation
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

theorem omittedShortcut_head_mem_limitWarp_of_noIncomingOriginalForward
    (S : ClosedClassifiedContactSegmentation
      (Y := C.selectedReference) (kappa := kappa) Q X persistent)
    (hback : S.FinitePiecesBackwardLinksOn)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    {a b : V} (hab : (a, b) ∈ S.shortcutEdges)
    (hnot : (a, b) ∉ S.limitingShortcutEdges hSafeRoof)
    (hno : ¬ ∃ x, (x, b) ∈ Q.directionEdges .forward) :
    b ∈ Gamma.vertexSet C.ladder.limitWarp := by
  cases S with
  | finite T =>
      exact T.toChain.omittedShortcut_head_mem_limitWarp_of_noIncomingOriginalForward
        hback hSafeRoof hab hnot hno
  | eventually T =>
      exact T.toChain.omittedShortcut_head_mem_limitWarp_of_noIncomingOriginalForward
        hback hSafeRoof hab hnot hno
  | omega T =>
      exact T.toChain.omittedShortcut_head_mem_limitWarp_of_noIncomingOriginalForward
        hback hSafeRoof hab hnot hno

theorem omittedShortcut_tail_mem_limitWarp_of_noOutgoingOriginalForward
    (S : ClosedClassifiedContactSegmentation
      (Y := C.selectedReference) (kappa := kappa) Q X persistent)
    (hback : S.FinitePiecesBackwardLinksOn)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    {a b : V} (hab : (a, b) ∈ S.shortcutEdges)
    (hnot : (a, b) ∉ S.limitingShortcutEdges hSafeRoof)
    (hno : ¬ ∃ y, (a, y) ∈ Q.directionEdges .forward) :
    a ∈ Gamma.vertexSet C.ladder.limitWarp := by
  cases S with
  | finite T =>
      exact T.toChain.omittedShortcut_tail_mem_limitWarp_of_noOutgoingOriginalForward
        hback hSafeRoof hab hnot hno
  | eventually T =>
      exact T.toChain.omittedShortcut_tail_mem_limitWarp_of_noOutgoingOriginalForward
        hback hSafeRoof hab hnot hno
  | omega T =>
      exact T.toChain.omittedShortcut_tail_mem_limitWarp_of_noOutgoingOriginalForward
        hback hSafeRoof hab hnot hno

end ClosedClassifiedContactSegmentation

namespace GroupedClosedClassifiedContactSegmentedAssignment

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {Z : Set Gamma.DPath}
variable {A : SimultaneousAssignment Z C.selectedReference}
variable {G : Type v}

def limitingShortcutEdges
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) : Set (V × V) :=
  ⋃ s, (S.segmentation s).limitingShortcutEdges hSafeRoof

def limitingRetainedEdges
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) : Set (V × V) :=
  ⋃ s, (S.segmentation s).limitingRetainedEdges hSafeRoof

def assignedForwardEdges
    (_S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G) : Set (V × V) :=
  ⋃ s, (A.assigned s).directionEdges .forward

def localEdge
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G) : Set (V × V) :=
  S.assignedForwardEdges ∪ S.edge

def limitingEdge
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) : Set (V × V) :=
  S.assignedForwardEdges ∪ S.limitingShortcutEdges hSafeRoof

theorem limitingShortcutEdges_subset_edge
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    S.limitingShortcutEdges hSafeRoof ⊆ S.edge := by
  intro e he
  simp only [limitingShortcutEdges, Set.mem_iUnion] at he
  obtain ⟨s, he⟩ := he
  exact Set.mem_iUnion.2
    ⟨s, (S.segmentation s).limitingShortcutEdges_subset_shortcutEdges
      hSafeRoof he⟩

theorem limitingShortcutEdges_subset_imaginaryGraph
    (S : GroupedClosedClassifiedContactSegmentedAssignment
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

theorem limitingRetainedEdges_subset_assignedForward_union_edge
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    S.limitingRetainedEdges hSafeRoof ⊆ S.assignedForwardEdges ∪ S.edge := by
  intro e he
  simp only [limitingRetainedEdges, Set.mem_iUnion] at he
  obtain ⟨s, he⟩ := he
  rcases (S.segmentation s)
      |>.limitingRetainedEdges_subset_originalForward_union_shortcut
        hSafeRoof he with he | he
  · exact Or.inl (Set.mem_iUnion.2 ⟨s, he⟩)
  · exact Or.inr (Set.mem_iUnion.2 ⟨s, he⟩)

theorem limitingEdge_subset_localEdge
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    S.limitingEdge hSafeRoof ⊆ S.localEdge := by
  rintro e (he | he)
  · exact Or.inl he
  · exact Or.inr (S.limitingShortcutEdges_subset_edge hSafeRoof he)

theorem limitingShortcutEdges_biUnique
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    Relator.BiUnique
      (fun x y ↦ (x, y) ∈ S.limitingShortcutEdges hSafeRoof) := by
  constructor
  · intro a b c hac hbc
    exact S.edge_biUnique.1
      (S.limitingShortcutEdges_subset_edge hSafeRoof hac)
      (S.limitingShortcutEdges_subset_edge hSafeRoof hbc)
  · intro a b c hab hac
    exact S.edge_biUnique.2
      (S.limitingShortcutEdges_subset_edge hSafeRoof hab)
      (S.limitingShortcutEdges_subset_edge hSafeRoof hac)

theorem rank_lt_of_mem_limitingShortcutEdges
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    {a b : V} (hab : (a, b) ∈ S.limitingShortcutEdges hSafeRoof) :
    S.rank a < S.rank b :=
  S.rank_lt_of_mem_edge (S.limitingShortcutEdges_subset_edge hSafeRoof hab)

theorem limitingShortcutEdges_acyclic
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    ¬ ContainsDirectedCycle (S.limitingShortcutEdges hSafeRoof) :=
  Alternating.GenericSimultaneousSwitch.not_containsDirectedCycle_of_wellFoundedRank
    (S.limitingShortcutEdges hSafeRoof) S.rank
    (S.rank_lt_of_mem_limitingShortcutEdges hSafeRoof)

theorem limitingShortcutEdges_no_reverse_ray
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    ¬ ContainsReverseDirectedRay (S.limitingShortcutEdges hSafeRoof) :=
  Alternating.GenericSimultaneousSwitch.not_containsReverseDirectedRay_of_wellFoundedRank
    (S.limitingShortcutEdges hSafeRoof) S.rank
    (S.rank_lt_of_mem_limitingShortcutEdges hSafeRoof)

theorem omittedShortcut_covered
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    {a b : V} (hab : (a, b) ∈ S.edge)
    (hnot : (a, b) ∉ S.limitingShortcutEdges hSafeRoof) :
    Nonempty (ClubStageGeometry.LimitingReferenceEndpointOwner C a) ∨
      Nonempty (ClubStageGeometry.LimitingReferenceEndpointOwner C b) := by
  simp only [edge, Set.mem_iUnion] at hab
  obtain ⟨s, hab⟩ := hab
  apply (S.segmentation s).omittedShortcut_covered hSafeRoof hab
  intro h
  exact hnot (Set.mem_iUnion.2 ⟨s, h⟩)

theorem omittedShortcut_head_mem_limitWarp_of_noIncomingAssignedForward
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hback : ∀ s, (S.segmentation s).FinitePiecesBackwardLinksOn)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    {a b : V} (hab : (a, b) ∈ S.edge)
    (hnot : (a, b) ∉ S.limitingShortcutEdges hSafeRoof)
    (hno : ¬ ∃ x, (x, b) ∈ S.assignedForwardEdges) :
    b ∈ Gamma.vertexSet C.ladder.limitWarp := by
  simp only [edge, Set.mem_iUnion] at hab
  obtain ⟨s, hab⟩ := hab
  apply (S.segmentation s)
    |>.omittedShortcut_head_mem_limitWarp_of_noIncomingOriginalForward
      (hback s) hSafeRoof hab
  · intro h
    exact hnot (Set.mem_iUnion.2 ⟨s, h⟩)
  · rintro ⟨x, hx⟩
    exact hno ⟨x, Set.mem_iUnion.2 ⟨s, hx⟩⟩

theorem omittedShortcut_tail_mem_limitWarp_of_noOutgoingAssignedForward
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hback : ∀ s, (S.segmentation s).FinitePiecesBackwardLinksOn)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    {a b : V} (hab : (a, b) ∈ S.edge)
    (hnot : (a, b) ∉ S.limitingShortcutEdges hSafeRoof)
    (hno : ¬ ∃ y, (a, y) ∈ S.assignedForwardEdges) :
    a ∈ Gamma.vertexSet C.ladder.limitWarp := by
  simp only [edge, Set.mem_iUnion] at hab
  obtain ⟨s, hab⟩ := hab
  apply (S.segmentation s)
    |>.omittedShortcut_tail_mem_limitWarp_of_noOutgoingOriginalForward
      (hback s) hSafeRoof hab
  · intro h
    exact hnot (Set.mem_iUnion.2 ⟨s, h⟩)
  · rintro ⟨y, hy⟩
    exact hno ⟨y, Set.mem_iUnion.2 ⟨s, hy⟩⟩

theorem limitingRoots_subset_localRoots_union_limitWarp
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hback : ∀ s, (S.segmentation s).FinitePiecesBackwardLinksOn)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (carrier : Set V) :
    {x | x ∈ carrier ∧ ¬ ∃ y, (y, x) ∈ S.limitingEdge hSafeRoof} ⊆
      {x | x ∈ carrier ∧ ¬ ∃ y, (y, x) ∈ S.localEdge} ∪
      (carrier ∩ Gamma.vertexSet C.ladder.limitWarp) := by
  intro x hx
  by_cases hold : ∃ y, (y, x) ∈ S.localEdge
  · right
    obtain ⟨y, hyx⟩ := hold
    rcases hyx with hyx | hyx
    · exact False.elim (hx.2 ⟨y, Or.inl hyx⟩)
    · have hnot : (y, x) ∉ S.limitingShortcutEdges hSafeRoof := by
        intro h
        exact hx.2 ⟨y, Or.inr h⟩
      have hnoForward : ¬ ∃ z, (z, x) ∈ S.assignedForwardEdges := by
        rintro ⟨z, hzx⟩
        exact hx.2 ⟨z, Or.inl hzx⟩
      exact ⟨hx.1,
        S.omittedShortcut_head_mem_limitWarp_of_noIncomingAssignedForward
          hback hSafeRoof hyx hnot hnoForward⟩
  · exact Or.inl ⟨hx.1, hold⟩

theorem limitingSinks_subset_localSinks_union_limitWarp
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hback : ∀ s, (S.segmentation s).FinitePiecesBackwardLinksOn)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (carrier : Set V) :
    {x | x ∈ carrier ∧ ¬ ∃ y, (x, y) ∈ S.limitingEdge hSafeRoof} ⊆
      {x | x ∈ carrier ∧ ¬ ∃ y, (x, y) ∈ S.localEdge} ∪
      (carrier ∩ Gamma.vertexSet C.ladder.limitWarp) := by
  intro x hx
  by_cases hold : ∃ y, (x, y) ∈ S.localEdge
  · right
    obtain ⟨y, hxy⟩ := hold
    rcases hxy with hxy | hxy
    · exact False.elim (hx.2 ⟨y, Or.inl hxy⟩)
    · have hnot : (x, y) ∉ S.limitingShortcutEdges hSafeRoof := by
        intro h
        exact hx.2 ⟨y, Or.inr h⟩
      have hnoForward : ¬ ∃ z, (x, z) ∈ S.assignedForwardEdges := by
        rintro ⟨z, hxz⟩
        exact hx.2 ⟨z, Or.inl hxz⟩
      exact ⟨hx.1,
        S.omittedShortcut_tail_mem_limitWarp_of_noOutgoingAssignedForward
          hback hSafeRoof hxy hnot hnoForward⟩
  · exact Or.inl ⟨hx.1, hold⟩

theorem union_limitingRoots_subset_union_localRoots_union_limitWarp
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hback : ∀ s, (S.segmentation s).FinitePiecesBackwardLinksOn)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (inside : Set (V × V)) (carrier : Set V) :
    {x | x ∈ carrier ∧
      ¬ ∃ y, (y, x) ∈ inside ∪ S.limitingEdge hSafeRoof} ⊆
      {x | x ∈ carrier ∧ ¬ ∃ y, (y, x) ∈ inside ∪ S.localEdge} ∪
      (carrier ∩ Gamma.vertexSet C.ladder.limitWarp) := by
  intro x hx
  have hxLimiting :
      x ∈ {x | x ∈ carrier ∧
        ¬ ∃ y, (y, x) ∈ S.limitingEdge hSafeRoof} := by
    refine ⟨hx.1, ?_⟩
    rintro ⟨y, hyx⟩
    exact hx.2 ⟨y, Or.inr hyx⟩
  rcases S.limitingRoots_subset_localRoots_union_limitWarp
      hback hSafeRoof carrier hxLimiting with hlocal | href
  · apply Or.inl
    refine ⟨hlocal.1, ?_⟩
    rintro ⟨y, hyx⟩
    rcases hyx with hyx | hyx
    · exact hx.2 ⟨y, Or.inl hyx⟩
    · exact hlocal.2 ⟨y, hyx⟩
  · exact Or.inr href

theorem union_limitingSinks_subset_union_localSinks_union_limitWarp
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hback : ∀ s, (S.segmentation s).FinitePiecesBackwardLinksOn)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (inside : Set (V × V)) (carrier : Set V) :
    {x | x ∈ carrier ∧
      ¬ ∃ y, (x, y) ∈ inside ∪ S.limitingEdge hSafeRoof} ⊆
      {x | x ∈ carrier ∧ ¬ ∃ y, (x, y) ∈ inside ∪ S.localEdge} ∪
      (carrier ∩ Gamma.vertexSet C.ladder.limitWarp) := by
  intro x hx
  have hxLimiting :
      x ∈ {x | x ∈ carrier ∧
        ¬ ∃ y, (x, y) ∈ S.limitingEdge hSafeRoof} := by
    refine ⟨hx.1, ?_⟩
    rintro ⟨y, hxy⟩
    exact hx.2 ⟨y, Or.inr hxy⟩
  rcases S.limitingSinks_subset_localSinks_union_limitWarp
      hback hSafeRoof carrier hxLimiting with hlocal | href
  · apply Or.inl
    refine ⟨hlocal.1, ?_⟩
    rintro ⟨y, hxy⟩
    rcases hxy with hxy | hxy
    · exact hx.2 ⟨y, Or.inl hxy⟩
    · exact hlocal.2 ⟨y, hxy⟩
  · exact Or.inr href

end GroupedClosedClassifiedContactSegmentedAssignment

#print axioms ClassifiedOrClosedFiniteContactPiece.covered_of_not_mem_limitingShortcut
#print axioms ClosedClassifiedContactChain.limitingShortcutEdges_biUnique
#print axioms ClosedClassifiedContactSegmentation.omittedShortcut_covered
#print axioms GroupedClosedClassifiedContactSegmentedAssignment.limitingRoots_subset_localRoots_union_limitWarp
#print axioms GroupedClosedClassifiedContactSegmentedAssignment.union_limitingSinks_subset_union_localSinks_union_limitWarp

end Erdos599.Blueprint.LinkageBlueprint
