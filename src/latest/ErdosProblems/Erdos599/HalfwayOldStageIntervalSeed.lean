/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayOldStageIntervalTransaction
import ErdosProblems.Erdos599.Halfway930ContactClosureSeed

/-!
# The source-free closure seed for the old-stage interval transaction

The component exchange in `OldStageIntervalTransaction` changes only a
`kappa`-small set of old-stage alternating components.  The global selected
reference is not indexed by the old frontier, so inserting those old-stage
vertices alone would lose the source/marker prefix provenance.  The honest
global seed instead inserts every complete selected-reference component
which touches an exceptional old-stage component.

Warp disjointness makes this family of complete components `kappa`-small,
and the selected-reference roof theorem keeps it inside the selected later
roof.  Unioning it with `continuation930ContactSeed` gives the exact
source-free seed shared by the coupled 9.30 and interval 9.31 transactions.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Ladder

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace OldStageIntervalTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {z : V}

/-- Complete selected-reference components which meet a component changed by
the old-stage interval exchange. -/
def exceptionalReferenceSeed (T : OldStageIntervalTransaction C z) : Set V :=
  meetingVertices Gamma C.selectedReference T.exceptionalComponents

/-- The complete local exceptional carrier together with every selected-
reference component which it touches.  Keeping both summands is essential:
the first retains the changed old-stage interval itself, while the second
retains the global reference provenance at every contact. -/
def exceptionalIntervalSeed (T : OldStageIntervalTransaction C z) : Set V :=
  T.exceptionalComponents ∪ T.exceptionalReferenceSeed

/-- The joint closure seed for a coupled 9.30 continuation and the selected
9.31 old-stage interval. -/
def contactIntervalSeed
    (T : OldStageIntervalTransaction C z)
    (W : LinkageBlueprint Gamma C.selectedReference kappa) : Set V :=
  continuation930ContactSeed C W ∪ T.exceptionalIntervalSeed

/-- Add the interval-exception provenance to any already selected coupled
closure seed.  This is the form used after Assertion 9.30 has adjoined its
chosen safe hammock member to `continuation930ContactSeed`. -/
def augmentedIntervalSeed
    (T : OldStageIntervalTransaction C z) (baseSeed : Set V) : Set V :=
  baseSeed ∪ T.exceptionalIntervalSeed

/-- The complete selected-reference components meeting the exceptional
interval components still have size at most `kappa`. -/
theorem mk_exceptionalReferenceSeed_le
    (T : OldStageIntervalTransaction C z) :
    #T.exceptionalReferenceSeed ≤ kappa := by
  exact mk_meetingVertices_le Gamma C.selectedReference
    T.exceptionalComponents C.selectedReference_isWarp C.capacity_infinite
    T.exceptionalComponents_card

/-- Exceptional reference components stay below the selected later
frontier. -/
theorem exceptionalReferenceSeed_subset_outerRoof
    (T : OldStageIntervalTransaction C z)
    (href : ∀ p ∈ C.selectedReference, p.support ⊆ C.outerRoof) :
    T.exceptionalReferenceSeed ⊆ C.outerRoof := by
  exact meetingVertices_subset_roof Gamma C.selectedReference
    T.exceptionalComponents C.outerRoof href

/-- The full exceptional interval seed stays below the selected later
frontier. -/
theorem exceptionalIntervalSeed_subset_outerRoof
    (T : OldStageIntervalTransaction C z)
    (href : ∀ p ∈ C.selectedReference, p.support ⊆ C.outerRoof) :
    T.exceptionalIntervalSeed ⊆ C.outerRoof := by
  exact Set.union_subset T.exceptionalComponents_subset_outerRoof
    (T.exceptionalReferenceSeed_subset_outerRoof href)

/-- The full exceptional interval seed is still `kappa`-small. -/
theorem mk_exceptionalIntervalSeed_le
    (T : OldStageIntervalTransaction C z) :
    #T.exceptionalIntervalSeed ≤ kappa := by
  exact (Cardinal.mk_union_le _ _).trans
    (Cardinal.add_le_of_le C.capacity_infinite
      T.exceptionalComponents_card T.mk_exceptionalReferenceSeed_le)

/-- The joint 9.30/9.31 seed is small without any cardinal bound on the
ambient source or the full old frontier. -/
theorem mk_contactIntervalSeed_le
    (T : OldStageIntervalTransaction C z)
    (W : LinkageBlueprint Gamma C.selectedReference kappa)
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent) :
    #(T.contactIntervalSeed W) ≤ kappa := by
  exact (Cardinal.mk_union_le _ _).trans
    (Cardinal.add_le_of_le C.capacity_infinite
      (continuation930ContactSeed.mk_le C W hW)
      T.mk_exceptionalIntervalSeed_le)

/-- General cardinal form for a coupled seed which already contains the
selected 9.30 path carrier. -/
theorem mk_augmentedIntervalSeed_le
    (T : OldStageIntervalTransaction C z) {baseSeed : Set V}
    (hbase : #baseSeed ≤ kappa) :
    #(T.augmentedIntervalSeed baseSeed) ≤ kappa := by
  exact (Cardinal.mk_union_le _ _).trans
    (Cardinal.add_le_of_le C.capacity_infinite hbase
      T.mk_exceptionalIntervalSeed_le)

/-- The joint seed is roofed whenever the existing coupled seed and the
selected reference are roofed. -/
theorem contactIntervalSeed_subset_outerRoof
    (T : OldStageIntervalTransaction C z)
    (W : LinkageBlueprint Gamma C.selectedReference kappa)
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent)
    (hbefore : C.before ⊆ C.outerRoof)
    (href : ∀ p ∈ C.selectedReference, p.support ⊆ C.outerRoof) :
    T.contactIntervalSeed W ⊆ C.outerRoof := by
  exact Set.union_subset
    (continuation930ContactSeed.subset_outerRoof C W hW hbefore href)
    (T.exceptionalIntervalSeed_subset_outerRoof href)

/-- General roof form for a coupled seed which already contains the selected
9.30 path carrier. -/
theorem augmentedIntervalSeed_subset_outerRoof
    (T : OldStageIntervalTransaction C z) {baseSeed : Set V}
    (hbase : baseSeed ⊆ C.outerRoof)
    (href : ∀ p ∈ C.selectedReference, p.support ⊆ C.outerRoof) :
    T.augmentedIntervalSeed baseSeed ⊆ C.outerRoof := by
  exact Set.union_subset hbase
    (T.exceptionalIntervalSeed_subset_outerRoof href)

/-- The previously selected coupled seed is retained literally. -/
theorem baseSeed_subset_augmentedIntervalSeed
    (T : OldStageIntervalTransaction C z) (baseSeed : Set V) :
    baseSeed ⊆ T.augmentedIntervalSeed baseSeed :=
  Set.subset_union_left

/-- The coupled 9.30 contact seed is retained literally. -/
theorem continuation930ContactSeed_subset_contactIntervalSeed
    (T : OldStageIntervalTransaction C z)
    (W : LinkageBlueprint Gamma C.selectedReference kappa) :
    continuation930ContactSeed C W ⊆ T.contactIntervalSeed W :=
  Set.subset_union_left

/-- Every vertex in a changed old-stage interval component is retained by
the joint seed. -/
theorem exceptionalComponents_subset_augmentedIntervalSeed
    (T : OldStageIntervalTransaction C z) (baseSeed : Set V) :
    T.exceptionalComponents ⊆ T.augmentedIntervalSeed baseSeed := by
  intro x hx
  exact Set.mem_union_right _ (Set.mem_union_left _ hx)

/-- Every selected-reference path touching an exceptional interval component
is swallowed in full by the joint seed. -/
theorem reference_support_subset_contactIntervalSeed
    (T : OldStageIntervalTransaction C z)
    (W : LinkageBlueprint Gamma C.selectedReference kappa)
    {p : Gamma.DPath} (hp : p ∈ C.selectedReference)
    (hcontact : (p.support ∩ T.exceptionalComponents).Nonempty) :
    p.support ⊆ T.contactIntervalSeed W := by
  exact (support_subset_meetingVertices Gamma C.selectedReference
    T.exceptionalComponents hp hcontact).trans
      (Set.subset_union_right.trans Set.subset_union_right)

end OldStageIntervalTransaction

#print axioms OldStageIntervalTransaction.mk_contactIntervalSeed_le
#print axioms OldStageIntervalTransaction.mk_augmentedIntervalSeed_le
#print axioms OldStageIntervalTransaction.contactIntervalSeed_subset_outerRoof
#print axioms OldStageIntervalTransaction.reference_support_subset_contactIntervalSeed

end LinkageBlueprint
end Blueprint
end Erdos599
