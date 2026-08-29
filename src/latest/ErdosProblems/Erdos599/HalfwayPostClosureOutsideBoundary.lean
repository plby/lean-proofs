/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureCutFragments
import ErdosProblems.Erdos599.OutsideReferenceCore
import ErdosProblems.Erdos599.BoundarySimultaneousAssignment
import ErdosProblems.Erdos599.HalfwayLinkageFirstBoundary

/-!
# Reference boundary of a post-closure fractured row

In Assertion 9.31 the closing set is fixed before the later finite linkage is
chosen.  The later linkage can therefore cross the closing set, and its
literal outside family consists of the pieces obtained by cutting at those
crossings.  It would be false to assume that the closing set is closed under
the later linkage.

The boundary statement needed for the fractured assignment uses much less.
It is enough that every reference member disjoint from the closing set is an
actual member of the later linkage.  At a point of such a reference member,
a cut initial cannot be an exit point and a cut terminal cannot be an entry
point.  The remaining no-incoming/no-outgoing alternatives are then genuine
initials/terminals of the later warp; warp uniqueness identifies their later
owner with the retained reference member.

Thus no containment of the full reference warp in the later linkage, and no
closure of the later linkage under the cut, occurs in this file.
-/

noncomputable section

open Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V}
variable {Y W : Set Gamma.DPath} {X : Set V}

/-- Absorbing the carrier of every reference member omitted from the later
row is a concrete sufficient condition for outside-reference retention.
This is the form supplied by a genuine symmetric-difference closure: no
member disjoint from `X` can belong to the omitted side. -/
theorem outsideReference_subset_of_sdiff_vertexSet_subset
    (hmissing : Gamma.vertexSet (Y \ W) ⊆ X) :
    outsideReference Y X ⊆ outsideReference W X := by
  intro p hp
  refine ⟨?_, hp.2⟩
  by_contra hpW
  have hpInitialX : p.initial ∈ X :=
    hmissing ⟨p, ⟨hp.1, hpW⟩, p.initial_mem_support⟩
  exact Set.disjoint_left.1 hp.2 p.initial_mem_support hpInitialX

/-- Away from the cutting set, every literal cut initial is already an
initial of the original later row.  This gives a useful necessary test for
any proposed reference family: its outside initials cannot be imported from
an unrelated source boundary. -/
theorem cutInitial_sdiff_subset_initialSet
    (hW : Gamma.IsWarp W) :
    CutSplit.initialVertices (outsideCarrier W X)
          (outsideFamilyEdges W X) X \ X ⊆
      Gamma.initialSet W := by
  rintro x ⟨hxCut, hxNotX⟩
  rcases hxCut with hxExit | hxOutside
  · exact False.elim (hxNotX hxExit.1)
  · rw [isWarp_initialSet_eq_noIncoming hW]
    refine ⟨FocusedInsideCut.outsideCarrier_subset_vertexSet W X
      hxOutside.1, ?_⟩
    rintro ⟨y, hyx⟩
    apply hxOutside.2.2
    exact ⟨y, hyx, fun hboth ↦ hxNotX hboth.2⟩

/-- The same necessary initial-boundary test for the concrete projected
holes. -/
theorem OutsideSplitWarp.SplitProjectedOutsideFracturedWarp.initialSet_sdiff_subset_original
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
      (Gamma := Gamma) W X)
    (hW : Gamma.IsWarp W) :
    Gamma.initialSet F.outside.holes.paths \ X ⊆
      Gamma.initialSet W := by
  rw [F.outside.initialSet_eq]
  exact cutInitial_sdiff_subset_initialSet hW

/-- Consequently, if an outside reference is claimed to have all its
initials among the literal holes, those initials must already be initials of
the original later row.  For a raw `T_alpha`--`T_beta` interval linkage this
forces the reference initials onto `T_alpha`; a full global or stage-prefix
reference normally fails this test. -/
theorem OutsideSplitWarp.SplitProjectedOutsideFracturedWarp.outsideReference_initialSet_subset_original_of_holes
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
      (Gamma := Gamma) W X)
    (hW : Gamma.IsWarp W)
    (hinitial : Gamma.initialSet (outsideReference Y X) ⊆
      Gamma.initialSet F.outside.holes.paths) :
    Gamma.initialSet (outsideReference Y X) ⊆ Gamma.initialSet W := by
  intro x hx
  apply F.initialSet_sdiff_subset_original hW
  refine ⟨hinitial hx, ?_⟩
  obtain ⟨p, hpOutside, hpx⟩ := hx
  have hxSupport : x ∈ p.support := by
    rw [← hpx]
    exact p.initial_mem_support
  exact fun hxX ↦ Set.disjoint_left.1 hpOutside.2 hxSupport hxX

/-- A literal cut initial that lies on a retained outside-reference member
is an initial of that member.  The only reference-to-row assumption is the
retention of the outside reference itself. -/
theorem cutInitial_inter_outsideReference_subset
    (hW : Gamma.IsWarp W)
    (hsub : outsideReference Y X ⊆ outsideReference W X) :
    CutSplit.initialVertices (outsideCarrier W X)
          (outsideFamilyEdges W X) X ∩
        Gamma.vertexSet (outsideReference Y X) ⊆
      Gamma.initialSet (outsideReference Y X) := by
  rintro x ⟨hxCut, q, hqOutside, hxq⟩
  have hqW : q ∈ W := (hsub hqOutside).1
  have hxNotX : x ∉ X :=
    Set.disjoint_left.1 hqOutside.2 hxq
  have hxWInitial : x ∈ Gamma.initialSet W := by
    rw [isWarp_initialSet_eq_noIncoming hW]
    refine ⟨⟨q, hqW, hxq⟩, ?_⟩
    rintro ⟨y, hyx⟩
    rcases hxCut with hxExit | hxOutside
    · exact hxNotX hxExit.1
    · apply hxOutside.2.2
      exact ⟨y, hyx, fun hboth ↦ hxNotX hboth.2⟩
  obtain ⟨p, hpW, hpx⟩ := hxWInitial
  have hpq : p = q :=
    DWeb.IsWarp.eq_of_mem_support hW hpW hqW
      (hpx.symm ▸ p.initial_mem_support) hxq
  subst q
  exact ⟨p, hqOutside, hpx⟩

/-- A literal cut terminal that lies on a retained outside-reference member
is a finite terminal of that member. -/
theorem cutTerminal_inter_outsideReference_subset
    (hW : Gamma.IsWarp W)
    (hsub : outsideReference Y X ⊆ outsideReference W X) :
    CutSplit.terminalVertices (outsideCarrier W X)
          (outsideFamilyEdges W X) X ∩
        Gamma.vertexSet (outsideReference Y X) ⊆
      Gamma.terminalFrontier (outsideReference Y X) := by
  rintro x ⟨hxCut, q, hqOutside, hxq⟩
  have hqW : q ∈ W := (hsub hqOutside).1
  have hxNotX : x ∉ X :=
    Set.disjoint_left.1 hqOutside.2 hxq
  have hxWTerminal : x ∈ Gamma.terminalFrontier W := by
    rw [isWarp_terminalFrontier_eq_noOutgoing hW]
    refine ⟨⟨q, hqW, hxq⟩, ?_⟩
    rintro ⟨y, hxy⟩
    rcases hxCut with hxEntry | hxOutside
    · exact hxNotX hxEntry.1
    · apply hxOutside.2.2
      exact ⟨y, hxy, fun hboth ↦ hxNotX hboth.1⟩
  exact ⟨q, hqOutside,
    DWeb.IsWarp.terminal_eq_of_mem_support_mem_terminalFrontier
      Gamma hW hqW hxq hxWTerminal⟩

/-- Every initial of the retained outside reference is a literal initial of
the post-cut family.  This is the source inclusion needed by the fractured
assignment theorem. -/
theorem outsideReference_initial_subset_cutInitial_of_subset
    (hW : Gamma.IsWarp W)
    (hsub : outsideReference Y X ⊆ outsideReference W X) :
    Gamma.initialSet (outsideReference Y X) ⊆
      CutSplit.initialVertices (outsideCarrier W X)
        (outsideFamilyEdges W X) X := by
  rintro x ⟨p, hpOutside, rfl⟩
  have hpW : p ∈ W := (hsub hpOutside).1
  have hxNotX : p.initial ∉ X :=
    Set.disjoint_left.1 hpOutside.2 p.initial_mem_support
  apply Or.inr
  refine ⟨Or.inl ⟨⟨p, hpW, p.initial_mem_support⟩, hxNotX⟩,
    hxNotX, ?_⟩
  rintro ⟨y, hyxOutside⟩
  apply isWarp_noIncoming_familyEdges_of_mem_initialSet hW
    ⟨p, hpW, rfl⟩
  exact ⟨y, outsideFamilyEdges_subset W X hyxOutside⟩

/-- The concrete literal holes have the exact boundary alignment with every
outside reference retained by the original later row. -/
theorem OutsideSplitWarp.SplitProjectedOutsideFracturedWarp.boundaryAligned_outsideReference
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
      (Gamma := Gamma) W X)
    (hW : Gamma.IsWarp W)
    (hsub : outsideReference Y X ⊆ outsideReference W X) :
    BoundaryAligned F.outside.holes.paths (outsideReference Y X) := by
  constructor
  · rw [F.outside.initialSet_eq]
    exact cutInitial_inter_outsideReference_subset hW hsub
  · rw [F.outside.terminalFrontier_eq]
    exact cutTerminal_inter_outsideReference_subset hW hsub

/-- The initial set of the retained outside reference is contained in the
initial set of the concrete literal holes. -/
theorem OutsideSplitWarp.SplitProjectedOutsideFracturedWarp.outsideReference_initialSet_subset
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
      (Gamma := Gamma) W X)
    (hW : Gamma.IsWarp W)
    (hsub : outsideReference Y X ⊆ outsideReference W X) :
    Gamma.initialSet (outsideReference Y X) ⊆
      Gamma.initialSet F.outside.holes.paths := by
  rw [F.outside.initialSet_eq]
  exact outsideReference_initial_subset_cutInitial_of_subset hW hsub

/-- Boundary data obtained directly from absorption of the omitted
reference carrier.  This is the non-provider interface intended for the
finite selected interval reference once its symmetric-difference carrier
has been inserted into `X`. -/
theorem OutsideSplitWarp.SplitProjectedOutsideFracturedWarp.boundaryData_of_sdiff_vertexSet_subset
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
      (Gamma := Gamma) W X)
    (hW : Gamma.IsWarp W)
    (hmissing : Gamma.vertexSet (Y \ W) ⊆ X) :
    BoundaryAligned F.outside.holes.paths (outsideReference Y X) ∧
      Gamma.initialSet (outsideReference Y X) ⊆
        Gamma.initialSet F.outside.holes.paths := by
  have hsub : outsideReference Y X ⊆ outsideReference W X :=
    outsideReference_subset_of_sdiff_vertexSet_subset hmissing
  exact ⟨F.boundaryAligned_outsideReference hW hsub,
    F.outsideReference_initialSet_subset hW hsub⟩

#print axioms outsideReference_subset_of_sdiff_vertexSet_subset
#print axioms cutInitial_sdiff_subset_initialSet
#print axioms OutsideSplitWarp.SplitProjectedOutsideFracturedWarp.initialSet_sdiff_subset_original
#print axioms OutsideSplitWarp.SplitProjectedOutsideFracturedWarp.outsideReference_initialSet_subset_original_of_holes
#print axioms cutInitial_inter_outsideReference_subset
#print axioms cutTerminal_inter_outsideReference_subset
#print axioms outsideReference_initial_subset_cutInitial_of_subset
#print axioms OutsideSplitWarp.SplitProjectedOutsideFracturedWarp.boundaryAligned_outsideReference
#print axioms OutsideSplitWarp.SplitProjectedOutsideFracturedWarp.outsideReference_initialSet_subset
#print axioms OutsideSplitWarp.SplitProjectedOutsideFracturedWarp.boundaryData_of_sdiff_vertexSet_subset

end LinkageBlueprint
end Blueprint
end Erdos599
