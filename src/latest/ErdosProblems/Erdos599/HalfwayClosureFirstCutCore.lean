/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCutFracturedProjection
import ErdosProblems.Erdos599.HalfwayClosedEndpointPairing
import ErdosProblems.Erdos599.FracturedAssignmentPeel

/-!
# Dependency-minimal selected-cut records

This focused module contains only the post-closure replacement and selected
cut records used by the contact-segmentation construction.  It deliberately
omits the legacy global replacement adapter and the stage scheduler.
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
variable {kappa theta : Cardinal.{u}}

/-! ## Post-closure first-hit replacement -/

/-- The exact source-specific operation still required after the ordinary
fractured assignment has been projected.

For every assigned path it chooses a safe path with the same initial and the
same optional terminal, but whose interior avoids the already constructed
closed set and which genuinely leaves it.  The shared terminal map is what
makes simultaneous finite-terminal injectivity automatic.  Unlike the false
generic implication from bracket safeness, this record states precisely the
first-hit/last-exit conclusion which the Section 9 cut argument must prove. -/
structure ClosedSetAvoidingReplacement
    {Z : Set Gamma.DPath}
    (A : SimultaneousAssignment Z Y) (X : Set V) where
  path : ∀ s : {x // x ∈ Gamma.initialSet Z \ Gamma.initialSet Y},
    AltPath Gamma.graph
  starts_at : ∀ s, (path s).initial = s.1
  safe : ∀ s, IsSafe Y (path s)
  terminal_eq : ∀ s, (path s).terminal? = (A.assigned s).terminal?
  interior_disjoint_finite : ∀ s v,
    (path s).terminal? = some v →
      Disjoint (hammockInterior s.1 (.vertex v) (path s)) X
  interior_disjoint_infinite : ∀ s,
    (path s).IsInfinite →
      Disjoint (hammockInterior s.1 .infinity (path s)) X
  outside : ∀ s, ¬ (path s).vertexSet ⊆ X

namespace ClosedSetAvoidingReplacement

variable {Z : Set Gamma.DPath}
variable {A : SimultaneousAssignment Z Y} {X : Set V}

private theorem replacement_infinite_iff
    (R : ClosedSetAvoidingReplacement A X) (s) :
    (R.path s).IsInfinite ↔ (A.assigned s).IsInfinite := by
  rw [AltPath.isInfinite_iff_terminal?_eq_none,
    AltPath.isInfinite_iff_terminal?_eq_none, R.terminal_eq]

/-- Replace all assigned paths simultaneously while retaining the original
endpoint injection. -/
noncomputable def assignment (R : ClosedSetAvoidingReplacement A X) :
    SimultaneousAssignment Z Y where
  assigned := R.path
  starts_at := R.starts_at
  safe := R.safe
  leaving := by
    intro s
    rcases A.leaving s with hinfinite | ⟨v, hterm, hvY⟩
    · exact Or.inl ((R.replacement_infinite_iff s).2 hinfinite)
    · exact Or.inr ⟨v, (R.terminal_eq s).trans hterm, hvY⟩
  maximal := by
    intro s
    rcases A.maximal s with hinfinite | ⟨v, hv, hterm⟩
    · exact Or.inl ((R.replacement_infinite_iff s).2 hinfinite)
    · exact Or.inr ⟨v, hv, (R.terminal_eq s).trans hterm⟩
  finite_terminals_injective := by
    intro s t v hs ht
    apply A.finite_terminals_injective
    · rw [← R.terminal_eq s]
      exact hs
    · rw [← R.terminal_eq t]
      exact ht

/-- The first-hit/last-exit replacement is exactly enough to build the
selected outside assignment; eligibility is supplied separately by the cut
boundary when compiling `AssignmentClosureContext`. -/
def outsideAssignment
    {W : Set Gamma.DPath} {F : OutsideFracturedWarp W X}
    {A : SimultaneousAssignment F.holes.paths Y}
    (R : ClosedSetAvoidingReplacement A X) :
    OutsideAssignment (Y := Y) F := by
  let B := R.assignment
  refine {
    assignment := B
    finite_meets_closure := ?_
    infinite_meets_closure := ?_
    leaves_closure := R.outside }
  · intro s v hterm x hx
    by_contra hxend
    have hxInterior :
        x ∈ hammockInterior s.1 (.vertex v) (R.path s) := by
      refine ⟨hx.1, ?_⟩
      simpa [hammockEndpoints] using hxend
    exact Set.disjoint_left.1 (R.interior_disjoint_finite s v hterm)
      hxInterior hx.2
  · intro s hinfinite x hx
    by_contra hxend
    have hxInterior :
        x ∈ hammockInterior s.1 .infinity (R.path s) := by
      refine ⟨hx.1, ?_⟩
      simpa [hammockEndpoints] using hxend
    exact Set.disjoint_left.1 (R.interior_disjoint_infinite s hinfinite)
      hxInterior hx.2

end ClosedSetAvoidingReplacement

/-- The cut-dependent data selected after the closing set is known.  This is
exactly a `ClosedFracturedReplacementRequest` without duplicating the already
available `HammockClosedUpTo` proof. -/
structure SelectedClosedFracturedCut
    (X before innerRoof outerRoof : Set V) where
  fractured : FracturedWarp Gamma
  boundary_aligned : BoundaryAligned fractured.paths Y
  finite_character : Gamma.HasFiniteCharacter fractured.paths
  recombined_finite_character :
    Gamma.HasFiniteCharacter fractured.edgeWarp
  reference_initials :
    Gamma.initialSet Y ⊆ Gamma.initialSet fractured.paths
  assignment : SimultaneousAssignment fractured.paths Y
  assignment_closure :
    AssignmentClosureContext assignment X before innerRoof outerRoof

namespace SelectedClosedFracturedCut

/-- An already constructed literal outside cut supplies the selected package
without any arbitrary-`X` quantification. -/
def ofOutsideCutConstruction
    {W : Set Gamma.DPath} {X before innerRoof outerRoof : Set V}
    (D : OutsideCutConstruction
      (Gamma := Gamma) (Y := Y) W X before innerRoof outerRoof) :
    SelectedClosedFracturedCut
      (Gamma := Gamma) (Y := Y) X before innerRoof outerRoof where
  fractured := D.fractured
  boundary_aligned := D.boundaryAligned
  finite_character := D.finiteCharacter
  recombined_finite_character := D.edgeWarpFiniteCharacter
  reference_initials := D.referenceInitials
  assignment := D.assignment
  assignment_closure := D.assignmentClosure

/-- Construct all path-level cut geometry from the actual row.  The only
remaining inputs are the two genuinely source-specific facts: the boundary
of this closed slice and one selected assignment with the required
closed-set avoidance. -/
theorem exists_of_literalOutsideCut
    {W : Set Gamma.DPath} {X before innerRoof outerRoof : Set V}
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W)
    (boundary : ∀ F :
      OutsideSplitWarp.SplitProjectedOutsideFracturedWarp W X,
      OutsideCutBoundary (Y := Y) W X before innerRoof outerRoof)
    (assigned : ∀ F :
      OutsideSplitWarp.SplitProjectedOutsideFracturedWarp W X,
      OutsideAssignment (Y := Y) F.outside) :
    Nonempty (SelectedClosedFracturedCut
      (Gamma := Gamma) (Y := Y) X before innerRoof outerRoof) := by
  obtain ⟨F⟩ := exists_splitProjectedOutsideFracturedWarp W X hW hfinite
  let D : OutsideCutConstruction
      (Gamma := Gamma) (Y := Y) W X before innerRoof outerRoof := {
    outside := F.outside
    boundary := boundary F
    assigned := assigned F }
  exact ⟨ofOutsideCutConstruction D⟩

/-- First-hit form of the literal cut constructor.  An ordinary projected
assignment is not required to avoid `X`; the source-specific replacement
does so while preserving its endpoint map, and therefore preserves the
simultaneous assignment axioms automatically. -/
theorem exists_of_literalOutsideCut_and_avoidingReplacement
    {W : Set Gamma.DPath} {X before innerRoof outerRoof : Set V}
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W)
    (boundary : ∀ F :
      OutsideSplitWarp.SplitProjectedOutsideFracturedWarp W X,
      OutsideCutBoundary (Y := Y) W X before innerRoof outerRoof)
    (baseAssignment : ∀ F :
      OutsideSplitWarp.SplitProjectedOutsideFracturedWarp W X,
      SimultaneousAssignment F.outside.holes.paths Y)
    (avoid : ∀ F :
      OutsideSplitWarp.SplitProjectedOutsideFracturedWarp W X,
      ClosedSetAvoidingReplacement (baseAssignment F) X) :
    Nonempty (SelectedClosedFracturedCut
      (Gamma := Gamma) (Y := Y) X before innerRoof outerRoof) := by
  apply exists_of_literalOutsideCut hW hfinite boundary
  intro F
  exact (avoid F).outsideAssignment

end SelectedClosedFracturedCut

end LinkageBlueprint
end Blueprint
end Erdos599
