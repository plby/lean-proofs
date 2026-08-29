/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayInsideCutSplice
import ErdosProblems.Erdos599.HalfwayLiteralContactCompletion

/-!
# The literal inside-plus-linkwise survivor relation

The outside-reference repair of Assertion 9.31 leaves two kinds of actual
row edges: the part of the later linkage wholly inside the closed set and
the forward links retained by the simultaneous assignment on its literal
outside fragments.  Both are subrelations of the same honest later-linkage
warp.  Their union therefore inherits local bi-uniqueness and all three
directed obstructions directly from that warp; no false disjointness of raw
fractured sources is required.

This file packages that union as `LiteralContactTransactionGeometry` and
constructs its exact finite-character real-warp realization.  The remaining
outside-reference edges and any genuine Claim-2 shortcuts can subsequently
be adjoined by a switching/shortcut compiler, but this literal row core is
already the part which controls all surviving original edges.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {W : Set Gamma.DPath} {X : Set V}
variable {F : OutsideFracturedWarp W X}
variable {B : FracturedAssignmentPeel.BracketFracturedAssignment F.holes Y}

/-- The actual row edges surviving in the inside family and in every
forward link of the literal outside-fragment assignment. -/
def insideLinkwiseEdges
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (B : FracturedAssignmentPeel.BracketFracturedAssignment F.holes Y) :
    Set (V × V) :=
  I.insideFamily.edgeSet ∪ B.retainedForwardEdges

/-- Endpoint carrier of the literal row survivor relation.  The inside
carrier deliberately retains the cut attachment vertices even if they are
isolated in the edge union. -/
def insideLinkwiseCarrier
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (B : FracturedAssignmentPeel.BracketFracturedAssignment F.holes Y) :
    Set V :=
  I.insideFamily.vertexSet ∪ B.retainedForwardCarrier

namespace CanonicalInsideCut

/-- Every literal inside/linkwise survivor edge is an edge of the honest
later-linkage row. -/
theorem insideLinkwiseEdges_subset_familyEdges
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (B : FracturedAssignmentPeel.BracketFracturedAssignment F.holes Y) :
    insideLinkwiseEdges I B ⊆ familyEdges W := by
  intro e he
  rcases he with he | he
  · rw [I.edgeSet_eq] at he
    exact he.1
  · apply outsideFamilyEdges_subset W X
    rw [← F.edgeWarp_familyEdges]
    exact B.retainedForwardEdges_subset_familyEdges he

theorem insideLinkwiseEdges_endpoints
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (B : FracturedAssignmentPeel.BracketFracturedAssignment F.holes Y)
    (e : V × V) (he : e ∈ insideLinkwiseEdges I B) :
    e.1 ∈ insideLinkwiseCarrier I B ∧
      e.2 ∈ insideLinkwiseCarrier I B := by
  rcases he with he | he
  · have h := edgeSet_endpoints_mem_vertexSet I.insideFamily he
    exact ⟨Or.inl h.1, Or.inl h.2⟩
  · have h := B.retainedForwardEdges_endpoints e he
    exact ⟨Or.inr h.1, Or.inr h.2⟩

/-- The row warp proves local bi-uniqueness across the inside/linkwise
boundary as well as within each half. -/
theorem insideLinkwiseEdges_biunique
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (B : FracturedAssignmentPeel.BracketFracturedAssignment F.holes Y)
    (hW : Gamma.IsWarp W) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ insideLinkwiseEdges I B) := by
  have hsub := I.insideLinkwiseEdges_subset_familyEdges B
  have hfull := Alternating.IsWarp.familyEdges_biUnique hW
  constructor
  · intro a b c hac hbc
    exact hfull.1 (hsub hac) (hsub hbc)
  · intro a b c hab hac
    exact hfull.2 (hsub hab) (hsub hac)

theorem insideLinkwiseEdges_acyclic
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (B : FracturedAssignmentPeel.BracketFracturedAssignment F.holes Y)
    (hW : Gamma.IsWarp W) :
    ¬ ContainsDirectedCycle (insideLinkwiseEdges I B) := by
  rintro ⟨c, hc⟩
  exact
    (PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsDirectedCycle
      hW)
    ⟨c, hc.trans (I.insideLinkwiseEdges_subset_familyEdges B)⟩

theorem insideLinkwiseEdges_no_reverse_ray
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (B : FracturedAssignmentPeel.BracketFracturedAssignment F.holes Y)
    (hW : Gamma.IsWarp W) :
    ¬ ContainsReverseDirectedRay (insideLinkwiseEdges I B) := by
  rintro ⟨r, hr⟩
  exact
    (PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsReverseDirectedRay
      hW)
    ⟨r, fun n ↦ I.insideLinkwiseEdges_subset_familyEdges B (hr n)⟩

/-- The checked transaction geometry of the literal row survivor core. -/
def insideLinkwiseGeometry
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (B : FracturedAssignmentPeel.BracketFracturedAssignment F.holes Y)
    (hW : Gamma.IsWarp W) :
    LiteralContactTransactionGeometry
      (Gamma := Gamma) (Y := Y) (kappa := kappa) where
  edge := insideLinkwiseEdges I B
  carrier := insideLinkwiseCarrier I B
  edge_subset_imaginaryGraph := by
    intro e he
    exact Or.inl (familyEdges_subset_adj W
      (I.insideLinkwiseEdges_subset_familyEdges B he))
  endpoints_mem_carrier := I.insideLinkwiseEdges_endpoints B
  biunique := I.insideLinkwiseEdges_biunique B hW
  acyclic := I.insideLinkwiseEdges_acyclic B hW
  no_reverse_ray := I.insideLinkwiseEdges_no_reverse_ray B hW

@[simp] theorem insideLinkwiseGeometry_edge
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (B : FracturedAssignmentPeel.BracketFracturedAssignment F.holes Y)
    (hW : Gamma.IsWarp W) :
    (I.insideLinkwiseGeometry B hW).edge = insideLinkwiseEdges I B := rfl

@[simp] theorem insideLinkwiseGeometry_carrier
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (B : FracturedAssignmentPeel.BracketFracturedAssignment F.holes Y)
    (hW : Gamma.IsWarp W) :
    (I.insideLinkwiseGeometry B hW).carrier =
      insideLinkwiseCarrier I B := rfl

/-- The row itself supplies the finite-character containing warp required by
the generic exact real-warp compiler. -/
theorem exists_insideLinkwiseRealWarp
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (B : FracturedAssignmentPeel.BracketFracturedAssignment F.holes Y)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W) :
    Nonempty (LiteralContactRealWarp (I.insideLinkwiseGeometry B hW)) := by
  apply LiteralContactTransactionGeometry.exists_realWarp_of_realEdges_subset_finiteWarp
    (I.insideLinkwiseGeometry B hW) W hW hWfinite
  intro e he
  exact I.insideLinkwiseEdges_subset_familyEdges B he.1

end CanonicalInsideCut

end LinkageBlueprint
end Blueprint
end Erdos599
