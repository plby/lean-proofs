/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.BoundarySimultaneousAssignment
import ErdosProblems.Erdos599.HalfwayOutsideReferenceClaim2
import ErdosProblems.Erdos599.HalfwayLinkageFirstBoundary

/-!
# Macro-owned assignment on a row-closed outside subwarp

When the later row is closed under `X`, the honest outside subfamily is a
warp, so Theorem 4.12 can be applied directly without first forgetting its
rooted macro-orbit provenance through a fractured projection.  If the later
row contains the reference row, the outside reference is a subwarp of the
outside later row and their boundary alignment follows from warp
disjointness.

The selected macro-owned assignment is made relative to the outside
reference and then lifted to the full reference.  Its assigned routes remain
wholly disjoint from `X`.  This is the retained provenance needed by the
simultaneous survivor-switch construction.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y W : Set Gamma.DPath}
variable {X : Set V} {kappa : Cardinal.{u}}

/-- Local unfractured presentation of a warp.  This file deliberately does
not import the obsolete aggregate which used to provide the same helper. -/
private def fracturedWarpOfWarp (Z : Set Gamma.DPath)
    (hZ : Gamma.IsWarp Z) : FracturedWarp Gamma where
  paths := Z
  edgeWarp := Z
  edgeWarp_isWarp := hZ
  same_edges := rfl
  allowed_intersection := by
    intro p hp q hq hpq hmeet
    exact (hmeet (hZ hp hq hpq)).elim

/-- Finite terminals of an outside subwarp are finite terminals of the full
warp. -/
theorem terminalFrontier_outsideReference_subset :
    Gamma.terminalFrontier (outsideReference W X) ⊆
      Gamma.terminalFrontier W := by
  rintro x ⟨p, hp, hpx⟩
  exact ⟨p, hp.1, hpx⟩

/-- If `Y ⊆ W`, their honest outside subwarps have the exact boundary
alignment required by the macro-owned Theorem 4.12 construction. -/
theorem boundaryAligned_outsideReference_of_subset
    (hW : Gamma.IsWarp W)
    (hsub : outsideReference Y X ⊆ outsideReference W X) :
    BoundaryAligned (outsideReference W X) (outsideReference Y X) := by
  constructor
  · rintro x ⟨⟨p, hpW, rfl⟩, q, hqY, hxp⟩
    have hpq : p = q :=
      DWeb.IsWarp.eq_of_mem_support hW hpW.1 (hsub hqY).1
        p.initial_mem_support hxp
    subst q
    exact ⟨p, ⟨hqY.1, hpW.2⟩, rfl⟩
  · rintro x ⟨⟨p, hpW, hpterminal⟩, q, hqY, hxp⟩
    have hpq : p = q :=
      DWeb.IsWarp.eq_of_mem_support hW hpW.1 (hsub hqY).1
        (Gamma.terminal_mem_support hpterminal) hxp
    subst q
    exact ⟨p, ⟨hqY.1, hpW.2⟩, hpterminal⟩

/-- Inclusion of the reference outside subwarp in the later outside
subwarp. -/
theorem outsideReference_subset_of_subset (hYW : Y ⊆ W) :
    outsideReference Y X ⊆ outsideReference W X :=
  fun _ hp ↦ ⟨hYW hp.1, hp.2⟩

/-! The full-reference lift is recorded as a separate structure because the
macro-owned source type is larger than the final full-reference source type. -/

/-- Macro provenance together with the actual full-reference bracket
assignment used by Claim 2. -/
structure OutsideMacroFullAssignment where
  provenance : MacroOwnedBracketSimultaneousAssignment
    (outsideReference W X) (outsideReference Y X)
  provenance_avoids : ∀ s, Disjoint (provenance.assigned s).vertexSet X
  full : BracketSimultaneousAssignment (outsideReference W X) Y
  full_assigned : ∀ s,
    full.assigned s = provenance.assigned
      (SimultaneousAssignment.toOutsideSource (X := X) s)
  full_avoids : ∀ s, Disjoint (full.assigned s).vertexSet X

namespace OutsideMacroFullAssignment

/-- The full assignment as the exact `SimultaneousAssignment` consumed by
Claim 2 and the inside-splice compiler. -/
def assignment
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X)) :
    SimultaneousAssignment (outsideReference W X) Y :=
  A.full.toSimultaneousAssignment

@[simp] theorem assignment_assigned
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X))
    (s : {z // z ∈ Gamma.initialSet (outsideReference W X) \
      Gamma.initialSet Y}) :
    A.assignment.assigned s = A.full.assigned s := rfl

/-- Exact full-reference Claim 2 context from ordinary row endpoint
locations and whole-route avoidance. -/
def closureContext
    {before innerRoof outerRoof : Set V}
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (hsource : Gamma.initialSet W \ Gamma.initialSet Y ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \ Gamma.vertexSet Y ⊆
      before ∩ outerRoof) :
    AssignmentClosureContext
      (Zf := fracturedWarpOfWarp (outsideReference W X)
        (outsideReference_isWarp hW))
      A.assignment X before innerRoof outerRoof := by
  refine {
    eligible_finite := ?_
    eligible_infinite := ?_
    interior_disjoint_finite := ?_
    interior_disjoint_infinite := ?_
    outside := ?_ }
  · intro s v hv
    refine ⟨hsource ⟨initialSet_outsideReference_subset s.property.1,
      s.property.2⟩, ?_⟩
    exact hterminal ⟨terminalFrontier_outsideReference_subset
      (A.assignment.finite_terminal_mem s hv).1,
      (A.assignment.finite_terminal_mem s hv).2⟩
  · intro s _hinfinite
    exact ⟨hsource ⟨initialSet_outsideReference_subset s.property.1,
      s.property.2⟩, trivial⟩
  · intro s v _hterminal
    apply Set.disjoint_of_subset_left _ (A.full_avoids s)
    exact fun _ hx ↦ hx.1
  · intro s _hinfinite
    apply Set.disjoint_of_subset_left _ (A.full_avoids s)
    exact fun _ hx ↦ hx.1
  · intro s hsubset
    exact Set.disjoint_left.1 (A.full_avoids s)
      (A.assignment.assigned s).initial_mem_vertexSet
      (hsubset (A.assignment.assigned s).initial_mem_vertexSet)

/-- Claim 2 for the retained macro-owned full assignment. -/
theorem classified
    {before innerRoof outerRoof persistent : Set V}
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (hsource : Gamma.initialSet W \ Gamma.initialSet Y ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \ Gamma.vertexSet Y ⊆
      before ∩ outerRoof)
    (hclosed : HammockClosedUpTo Gamma Y X
      before innerRoof outerRoof kappa) :
    (∀ s v, (A.assignment.assigned s).terminal? = some v →
        IsImaginaryEdge Gamma Y kappa s.1 v) ∧
      (∀ s, (A.assignment.assigned s).IsInfinite →
        IsPopular Gamma Y persistent kappa s.1) :=
  by
    let hA := A.closureContext hW hsource hterminal
    constructor
    · intro s v hterm
      exact isImaginaryEdge_of_closed hclosed
        (hA.eligible_finite s v hterm) (A.assignment.safe s)
        (A.assignment.starts_at s) hterm
        (hA.interior_disjoint_finite s v hterm) (hA.outside s)
    · intro s hinfinite
      exact isPopular_of_closed_infinite hclosed
        (hA.eligible_infinite s hinfinite) (A.assignment.safe s)
        (A.assignment.starts_at s) hinfinite
        (hA.interior_disjoint_infinite s hinfinite) (hA.outside s)

end OutsideMacroFullAssignment

/-- Direct construction of the macro-owned assignment and its full-reference
lift. -/
theorem exists_outsideMacroFullAssignment
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hsub : outsideReference Y X ⊆ outsideReference W X)
    (hYclosed : ClosedUnderPaths Gamma Y X) :
    Nonempty (OutsideMacroFullAssignment
      (Y := Y) (W := W) (X := X)) := by
  have hZ : Gamma.IsWarp (outsideReference W X) :=
    outsideReference_isWarp hW
  have hZfinite : Gamma.HasFiniteCharacter (outsideReference W X) :=
    outsideReference_finiteCharacter hWfinite
  have hYout : Gamma.IsWarp (outsideReference Y X) :=
    outsideReference_isWarp hY
  have hYoutfinite :
      Gamma.HasFiniteCharacter (outsideReference Y X) :=
    outsideReference_finiteCharacter hYfinite
  let M := (boundaryMacroOwnedBracketSimultaneousAssignment Gamma
    (outsideReference W X) (outsideReference Y X)
    (boundaryAligned_outsideReference_of_subset hW hsub)
    hZ hYout hZfinite hYoutfinite
    (by
      rintro x ⟨p, hp, rfl⟩
      exact ⟨p, hsub hp, rfl⟩)).some
  have havoid : ∀ s, Disjoint (M.assigned s).vertexSet X := by
    intro s
    apply disjoint_vertexSet_of_bracketSafe_outsideReference
      (Y := Y) (U := outsideReference W X)
      (M.bracket_safe s)
    · intro hinitialX
      have hsX : s.1 ∈ X := M.starts_at s ▸ hinitialX
      obtain ⟨p, hpout, hpinitial⟩ := s.property.1
      exact Set.disjoint_left.1 hpout.2
        (hpinitial ▸ p.initial_mem_support) hsX
    · exact vertexSet_outsideReference_disjoint
  let L := M.toSimultaneousAssignment.liftOutsideReference
    hYclosed hY havoid
  let LB : BracketSimultaneousAssignment (outsideReference W X) Y := {
    toSimultaneousAssignment := L
    bracket_safe := fun s ↦
      (M.bracket_safe
        (SimultaneousAssignment.toOutsideSource (X := X) s)).lift_outsideReference
          hYclosed hY
          (havoid (SimultaneousAssignment.toOutsideSource (X := X) s)) }
  exact ⟨{
    provenance := M
    provenance_avoids := havoid
    full := LB
    full_assigned := by
      intro s
      rfl
    full_avoids := by
      intro s
      exact havoid
        (SimultaneousAssignment.toOutsideSource (X := X) s) }⟩

end LinkageBlueprint
end Blueprint
end Erdos599
