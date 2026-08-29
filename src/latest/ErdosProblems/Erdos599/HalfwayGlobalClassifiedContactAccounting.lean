/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayGlobalLocalReferenceClassification
import ErdosProblems.Erdos599.HalfwayClassifiedContactSegmentation
import ErdosProblems.Erdos599.HalfwayLiteralContactGeometry

/-!
# Accounting for limiting-reference contact reclassification

When a selected-reference imaginary contact becomes covered by the limiting
reference, deleting its shortcut is sound only if the literal forward edges
of that same contact piece are retained.  `ClassifiedFiniteContactPiece`
contains the exact direction-preserving inclusion which the weaker contact
segmentation interface omits.  This file globalizes that classification and
records the resulting edge accounting without asserting source coverage or a
complete moving successor.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder Alternating
open Alternating.RelationDecomposition

universe u v

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {X : Set V} {kappa : Cardinal.{u}}

namespace ClassifiedFiniteContactPiece

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {Q : AltPath Gamma.graph} {u v : V}

/-- Reclassify one direction-preserving contact piece against the limiting
reference.  Existing selected-reference owners are extended to their unique
limiting owners; a locally imaginary piece uses the genuine exception split. -/
noncomputable def globalize
    (P : ClassifiedFiniteContactPiece
      (Y := C.selectedReference) (kappa := kappa) Q X u v)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    ClubStageGeometry.LimitingFiniteContactClassification C X P.path u v :=
  match P.classification with
  | .imaginary h =>
      (C.globalizeLocalImaginary (X := X) (Q := P.path) hSafeRoof h).some
  | .initialCovered R =>
      .initialCovered
        (C.limitingReferenceEndpointOwner_of_selected R.mem R.contains).some
  | .terminalCovered R =>
      .terminalCovered
        (C.limitingReferenceEndpointOwner_of_selected R.mem R.contains).some

/-- The actual relation retained by the globally reclassified piece. -/
def limitingRetainedEdges
    (P : ClassifiedFiniteContactPiece
      (Y := C.selectedReference) (kappa := kappa) Q X u v)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) : Set (V × V) :=
  (P.globalize hSafeRoof).retainedEdges

/-- The shortcut part of the globally reclassified piece. -/
def limitingShortcutEdges
    (P : ClassifiedFiniteContactPiece
      (Y := C.selectedReference) (kappa := kappa) Q X u v)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) : Set (V × V) :=
  (P.globalize hSafeRoof).shortcutEdges

theorem limitingRetainedEdges_subset_imaginaryGraph
    (P : ClassifiedFiniteContactPiece
      (Y := C.selectedReference) (kappa := kappa) Q X u v)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    P.limitingRetainedEdges hSafeRoof ⊆
      {e | (imaginaryGraph Gamma C.ladder.limitWarp kappa).Adj e.1 e.2} :=
  (P.globalize hSafeRoof).retainedEdges_subset_imaginaryGraph

/-- Globalization never invents a shortcut not already present in the local
classified contact chain. -/
theorem limitingShortcutEdges_subset_shortcutEdges
    (P : ClassifiedFiniteContactPiece
      (Y := C.selectedReference) (kappa := kappa) Q X u v)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    P.limitingShortcutEdges hSafeRoof ⊆ P.shortcutEdges := by
  cases hlocal : P.classification with
  | imaginary h =>
      intro e he
      cases hglobal : P.globalize hSafeRoof with
      | imaginary _ =>
          simpa [limitingShortcutEdges, hglobal, shortcutEdges, hlocal,
            ClubStageGeometry.LimitingFiniteContactClassification.shortcutEdges]
            using he
      | initialCovered _ =>
          simp [limitingShortcutEdges, hglobal,
            ClubStageGeometry.LimitingFiniteContactClassification.shortcutEdges]
            at he
      | terminalCovered _ =>
          simp [limitingShortcutEdges, hglobal,
            ClubStageGeometry.LimitingFiniteContactClassification.shortcutEdges]
            at he
  | initialCovered R =>
      intro e he
      simp [limitingShortcutEdges, globalize, hlocal,
        ClubStageGeometry.LimitingFiniteContactClassification.shortcutEdges]
        at he
  | terminalCovered R =>
      intro e he
      simp [limitingShortcutEdges, globalize, hlocal,
        ClubStageGeometry.LimitingFiniteContactClassification.shortcutEdges]
        at he

/-- Exact accounting law: a global shortcut remains one of the old contact
shortcuts, while every covered branch contributes only direction-preserving
literal forward edges of the original assigned route. -/
theorem limitingRetainedEdges_subset_originalForward_union_shortcut
    (P : ClassifiedFiniteContactPiece
      (Y := C.selectedReference) (kappa := kappa) Q X u v)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    P.limitingRetainedEdges hSafeRoof ⊆
      Q.directionEdges .forward ∪ P.shortcutEdges := by
  intro e he
  rcases (P.globalize hSafeRoof).retainedEdges_subset_originalForward_union_shortcut
      he with hforward | hshortcut
  · exact Or.inl (P.forwardEdges_subset_original hforward)
  · exact Or.inr (P.limitingShortcutEdges_subset_shortcutEdges hSafeRoof
      hshortcut)

/-- If the local shortcut is not retained globally, the concrete global
classification exposes a limiting-reference owner at one endpoint and the
piece retains precisely its literal forward edges. -/
theorem covered_of_not_mem_limitingShortcut
    (P : ClassifiedFiniteContactPiece
      (Y := C.selectedReference) (kappa := kappa) Q X u v)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (hlocal : (u, v) ∈ P.shortcutEdges)
    (hglobal : (u, v) ∉ P.limitingShortcutEdges hSafeRoof) :
    (Nonempty (ClubStageGeometry.LimitingReferenceEndpointOwner C u) ∨
       Nonempty (ClubStageGeometry.LimitingReferenceEndpointOwner C v)) ∧
      P.limitingRetainedEdges hSafeRoof =
        P.path.directionEdges .forward := by
  cases hP : P.globalize hSafeRoof with
  | imaginary h =>
      exfalso
      apply hglobal
      simp [limitingShortcutEdges, hP,
        ClubStageGeometry.LimitingFiniteContactClassification.shortcutEdges]
  | initialCovered R =>
      exact ⟨Or.inl ⟨R⟩, by
        simp [limitingRetainedEdges, hP,
          ClubStageGeometry.LimitingFiniteContactClassification.retainedEdges]⟩
  | terminalCovered R =>
      exact ⟨Or.inr ⟨R⟩, by
        simp [limitingRetainedEdges, hP,
          ClubStageGeometry.LimitingFiniteContactClassification.retainedEdges]⟩

end ClassifiedFiniteContactPiece

namespace ClassifiedInfiniteContactTail

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {Q : AltPath Gamma.graph} {persistent : Set V} {u : V}

/-- Infinite-tail counterpart of finite contact globalization. -/
noncomputable def globalize
    (T : ClassifiedInfiniteContactTail
      (Y := C.selectedReference) (kappa := kappa) Q X persistent u)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    ClubStageGeometry.LimitingInfiniteContactClassification
      C X persistent T.path u :=
  match T.classification with
  | .popular h =>
      (C.globalizeLocalPopular (X := X) (Q := T.path) hSafeRoof h).some
  | .initialCovered R =>
      .initialCovered
        (C.limitingReferenceEndpointOwner_of_selected R.mem R.contains).some

def limitingRetainedEdges
    (T : ClassifiedInfiniteContactTail
      (Y := C.selectedReference) (kappa := kappa) Q X persistent u)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) : Set (V × V) :=
  (T.globalize hSafeRoof).retainedEdges

theorem limitingRetainedEdges_subset_originalForward
    (T : ClassifiedInfiniteContactTail
      (Y := C.selectedReference) (kappa := kappa) Q X persistent u)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    T.limitingRetainedEdges hSafeRoof ⊆ Q.directionEdges .forward :=
  (T.globalize hSafeRoof).retainedEdges_subset_originalForward.trans
    T.forwardEdges_subset_original

theorem limitingRetainedEdges_subset_imaginaryGraph
    (T : ClassifiedInfiniteContactTail
      (Y := C.selectedReference) (kappa := kappa) Q X persistent u)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    T.limitingRetainedEdges hSafeRoof ⊆
      {e | (imaginaryGraph Gamma C.ladder.limitWarp kappa).Adj e.1 e.2} := by
  intro e he
  have heForward : e ∈ T.path.directionEdges .forward :=
    (T.globalize hSafeRoof).retainedEdges_subset_originalForward he
  have heEdge : e ∈ T.path.edgeSet := by
    simp only [AltPath.directionEdges, Set.mem_iUnion] at heForward
    obtain ⟨l, hl, _hforward, hel⟩ := heForward
    rw [T.path.edgeSet_eq_iUnion_links]
    simp only [Set.mem_iUnion]
    exact ⟨l, hl, hel⟩
  exact Or.inl (T.path.edgeSet_subset_adj heEdge)

end ClassifiedInfiniteContactTail

#print axioms ClassifiedFiniteContactPiece.covered_of_not_mem_limitingShortcut
#print axioms ClassifiedFiniteContactPiece.limitingRetainedEdges_subset_originalForward_union_shortcut
#print axioms ClassifiedInfiniteContactTail.limitingRetainedEdges_subset_originalForward

end Erdos599.Blueprint.LinkageBlueprint
