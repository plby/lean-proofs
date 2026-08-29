/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayGlobalClassifiedContactBoundary
import ErdosProblems.Erdos599.FracturedProjectionFiniteProvenance

/-!
# Restricting compressed backward provenance to contact pieces

Cutting a compressed alternating trace at closing-set contacts can split a
link.  Edge-set containment alone therefore does not transport
`BackwardLinksOn`.  The exact restriction datum says that every backward
link of a child piece is a finite subpath of a backward link of the parent
compressed trace.  Indexed backward provenance then supplies the unique
selected-reference owner of that parent link.

The final theorem specializes this generic restriction to
`finiteTraceCompression_indexedBackwardProvenance`; the contact splitter
only has to retain the literal link restriction map.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder Alternating

universe u v w

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {X persistent : Set V} {kappa : Cardinal.{u}}

/-- Every backward link of `child` is cut from one backward link of
`parent`. -/
def BackwardLinksRestrictTo
    (child parent : AltPath Gamma.graph) : Prop :=
  ∀ l ∈ child.links, l.direction = .backward →
    ∃ r ∈ parent.links, r.direction = .backward ∧
      l.path.support ⊆ r.path.support ∧
      l.path.edgeSet ⊆ r.path.edgeSet

/-- Indexed unique-owner provenance on the parent restricts to ordinary
`BackwardLinksOn` on every literal child. -/
theorem backwardLinksOn_of_restrictTo_of_indexedProvenance
    {child parent : AltPath Gamma.graph} {I : Type w}
    (hrestrict : BackwardLinksRestrictTo child parent)
    (P : parent.IndexedBackwardProvenance Y I) :
    BackwardLinksOn Y child := by
  intro l hl hldir
  obtain ⟨r, hr, hrdir, hlr⟩ := hrestrict l hl hldir
  rw [P.links_eq_range] at hr
  obtain ⟨i, rfl⟩ := hr
  refine ⟨P.owner i hrdir, P.owner_mem i hrdir, ?_⟩
  have hro := P.isSubpath i hrdir
  exact ⟨hlr.1.trans hro.1, hlr.2.trans hro.2⟩

namespace ClassifiedContactSegmentation

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {Q parent : AltPath Gamma.graph}

/-- Link-level restriction data for every finite classified contact piece.
Infinite tails create no shortcut and are irrelevant to this certificate. -/
def FinitePiecesBackwardLinksRestrictTo
    (S : ClassifiedContactSegmentation
      (Y := C.selectedReference) (kappa := kappa) Q X persistent)
    (parent : AltPath Gamma.graph) : Prop :=
  match S with
  | .finite T => ∀ i, BackwardLinksRestrictTo (T.piece i).path parent
  | .eventually T =>
      ∀ i, BackwardLinksRestrictTo (T.piece i).path parent
  | .omega T => ∀ i, BackwardLinksRestrictTo (T.piece i).path parent

/-- The splitter's literal link restriction and the parent's indexed owner
provenance discharge the exact boundary predicate used by the global
classified transaction. -/
theorem finitePiecesBackwardLinksOn_of_indexedProvenance
    (S : ClassifiedContactSegmentation
      (Y := C.selectedReference) (kappa := kappa) Q X persistent)
    {I : Type w}
    (hrestrict : S.FinitePiecesBackwardLinksRestrictTo parent)
    (P : parent.IndexedBackwardProvenance C.selectedReference I) :
    S.FinitePiecesBackwardLinksOn := by
  cases S with
  | finite T =>
      intro i
      exact backwardLinksOn_of_restrictTo_of_indexedProvenance
        (hrestrict i) P
  | eventually T =>
      intro i
      exact backwardLinksOn_of_restrictTo_of_indexedProvenance
        (hrestrict i) P
  | omega T =>
      intro i
      exact backwardLinksOn_of_restrictTo_of_indexedProvenance
        (hrestrict i) P

end ClassifiedContactSegmentation

namespace FracturedAssignmentPeel

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {Z : FracturedWarp Gamma} {Y₀ : Set Gamma.DPath}
variable {Q₀ : FiniteTrace (FracturedDuplication.web Gamma Z).graph}

/-- Actual compressed-trace specialization.  The equality records the
stage compiler's identification of the peeled active reference with the
selected finite ladder reference; no claim is made that the global limiting
reference is finite. -/
theorem finiteTraceCompression_finitePiecesBackwardLinksOn
    (hQ₀ : IsBracketSafe (activeLiftedPaths Z)
      (FracturedDuplication.liftedReference Z (activeReference Z Y₀))
        (.finite Q₀))
    (hY₀ : Gamma.IsWarp Y₀)
    (hlast : Q₀.lastLink.direction = .forward)
    (href : activeReference Z Y₀ = C.selectedReference)
    (S : ClassifiedContactSegmentation
      (Y := C.selectedReference) (kappa := kappa)
      (finiteTraceCompression Z Q₀).path X persistent)
    (hrestrict : S.FinitePiecesBackwardLinksRestrictTo
      (finiteTraceCompression Z Q₀).path) :
    S.FinitePiecesBackwardLinksOn := by
  let P := finiteTraceCompression_indexedBackwardProvenance
    Z Q₀ hQ₀ hY₀ hlast
  rw [href] at P
  exact S.finitePiecesBackwardLinksOn_of_indexedProvenance hrestrict P

end FracturedAssignmentPeel

#print axioms backwardLinksOn_of_restrictTo_of_indexedProvenance
#print axioms ClassifiedContactSegmentation.finitePiecesBackwardLinksOn_of_indexedProvenance
#print axioms FracturedAssignmentPeel.finiteTraceCompression_finitePiecesBackwardLinksOn

end Erdos599.Blueprint.LinkageBlueprint
