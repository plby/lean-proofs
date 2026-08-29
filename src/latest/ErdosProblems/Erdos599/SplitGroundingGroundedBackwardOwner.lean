/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedBackwardGrounded

/-!
# Exact limiting-ladder owner of a canonical grounded backward edge

A selected backward edge and an ambient limiting-ladder edge cannot belong
to different ladder members: the limiting ladder is a warp, and the shared
edge supplies a shared support vertex.  This elementary uniqueness fact is
the bridge from finite/blocking root failures to the concrete selected
request which deleted their incoming edge.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open Alternating GroundingErasedDecode GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev GroundedOwnerIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev GroundedOwnerControls :=
  L.splitGroundedCanonicalControls hL hground S

/-- Exact owner provenance for a canonical selected backward edge which is
also known to lie on a specified limiting-ladder member. -/
theorem exists_splitGroundedCanonicalBackwardEdge_owner_eq
    {e : V × V}
    (heSelected : e ∈ erasedSelectedDirectionEdgesAt
      (GroundedOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
      (GroundedOwnerControls (L := L) (hL := hL)
        (hground := hground) (S := S)) ∅ .backward)
    (Y : Gamma.DPath) (hY : Y ∈ L.limitWarp)
    (heY : e ∈ Y.edgeSet) :
    ∃ (c : ActiveControlRequestAt
          (GroundedOwnerIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (GroundedOwnerControls (L := L) (hL := hL)
            (hground := hground) (S := S)) ∅)
        (l : Link Gamma.graph),
      l ∈ (selectedErasedCompression
        (GroundedOwnerIndexed (L := L) (hL := hL)
          (hground := hground)) S
        (GroundedOwnerControls (L := L) (hL := hL)
          (hground := hground) (S := S))
        (chosenRequest c.1)).path.links ∧
      l.direction = .backward ∧ e ∈ l.path.edgeSet ∧
      l.path.IsSubpathOf Y := by
  simp only [erasedSelectedDirectionEdgesAt, Set.mem_iUnion] at heSelected
  obtain ⟨c, hec⟩ := heSelected
  simp only [AltPath.directionEdges, Set.mem_iUnion] at hec
  obtain ⟨l, hl, hldir, hel⟩ := hec
  obtain ⟨parent, hparent, hsub⟩ :=
    selectedErasedCompression_backwardLinksOn
      (GroundedOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
      (GroundedOwnerControls (L := L) (hL := hL)
        (hground := hground) (S := S))
      (chosenRequest c.1) l hl hldir
  have hparent' : parent ∈ L.limitWarp := by
    simpa only [splitGroundedPopularAuxiliaryInput, limitWarp] using hparent
  have heParent : e ∈ parent.edgeSet := hsub.2 hel
  have hparentY : parent = Y :=
    Alternating.DWeb.IsWarp.eq_of_mem_support
      (hL.legal.warpStages (Ladder.finalStage kappa))
      hparent' hY
      (parent.edgeSet_subset_support_prod heParent).1
      (Y.edgeSet_subset_support_prod heY).1
  subst parent
  exact ⟨c, l, hl, hldir, hel, hsub⟩

/-- The owner of a selected backward edge on a grounded limiting-ladder
member is itself that grounded member. -/
theorem exists_splitGroundedCanonicalBackwardEdge_groundedOwner
    {e : V × V}
    (heSelected : e ∈ erasedSelectedDirectionEdgesAt
      (GroundedOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
      (GroundedOwnerControls (L := L) (hL := hL)
        (hground := hground) (S := S)) ∅ .backward)
    (Y : Gamma.DPath) (hY : Y ∈ L.limitWarp)
    (hYGrounded : PopularAuxiliary.IsGroundedPath Gamma Y)
    (heY : e ∈ Y.edgeSet) :
    ∃ (c : ActiveControlRequestAt
          (GroundedOwnerIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (GroundedOwnerControls (L := L) (hL := hL)
            (hground := hground) (S := S)) ∅)
        (l : Link Gamma.graph),
      l ∈ (selectedErasedCompression
        (GroundedOwnerIndexed (L := L) (hL := hL)
          (hground := hground)) S
        (GroundedOwnerControls (L := L) (hL := hL)
          (hground := hground) (S := S))
        (chosenRequest c.1)).path.links ∧
      l.direction = .backward ∧ e ∈ l.path.edgeSet ∧
      l.path.IsSubpathOf Y ∧ PopularAuxiliary.IsGroundedPath Gamma Y := by
  obtain ⟨c, l, hl, hldir, hel, hsub⟩ :=
    exists_splitGroundedCanonicalBackwardEdge_owner_eq
      heSelected Y hY heY
  exact ⟨c, l, hl, hldir, hel, hsub, hYGrounded⟩

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.exists_splitGroundedCanonicalBackwardEdge_owner_eq
#print axioms
  Erdos599.DWeb.KappaLadder.exists_splitGroundedCanonicalBackwardEdge_groundedOwner
