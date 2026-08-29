/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.OutsideDuplicatedProjection
import ErdosProblems.Erdos599.Blueprint931

/-!
# Closure-adapted occurrence assignments for Assertion 9.31

The closing set in Assertion 9.31 splits the selected row: its paths are
allowed to cross the set, and their outside fragments are precisely the
first warp to which the assignment theorem is applied.  Thus closure of the
set under the unsplit row is not a legitimate hypothesis.

The exact source-level input is instead an assignment on all literal holes
together with its `AssignmentClosureContext`.  That context permits contact
with the closing set at the prescribed endpoints while excluding interior
contact.  This file embeds the assigned paths in the plain copies of the
duplicated occurrence web and transfers the closure context field-for-field.
No connector is contracted and no whole-route disjointness is assumed.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint

open DirectedPath _root_.Erdos599.Alternating
open _root_.Erdos599.Alternating.FracturedDuplication

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {Y : Set Gamma.DPath}

/-- An occurrence endpoint map together with the genuine projected paths
and closure geometry which realize it.  Endpoint contact with `X` is
allowed exactly as prescribed by the hammock endpoints. -/
structure OutsideDuplicatedProjection
    (Zf : FracturedWarp Gamma) (Y : Set Gamma.DPath)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (X before innerRoof outerRoof : Set V) where
  duplicated : DuplicatedFracturedAssignment Zf Y
  projection : CompressedFracturedAssignment.ProjectionClosureContext
    duplicated hYfinite X before innerRoof outerRoof

namespace OutsideDuplicatedProjection

variable {Zf : FracturedWarp Gamma}
variable {hYfinite : Gamma.HasFiniteCharacter Y}
variable {X before innerRoof outerRoof : Set V}

/-- Plain-lift a selected full-holes assignment while retaining its exact
interior-disjoint closure certificate.  This is the source-instantiable
replacement for the false `ClosedUnderPaths Gamma W X` route. -/
noncomputable def ofAssignmentClosureContext
    (A : SimultaneousAssignment Zf.paths Y)
    (hA : AssignmentClosureContext A X before innerRoof outerRoof) :
    OutsideDuplicatedProjection Zf Y hYfinite X
      before innerRoof outerRoof := by
  let D := DuplicatedFracturedAssignment.ofSimultaneousPlain A
  refine {
    duplicated := D
    projection := {
      projected := A.assigned
      starts_at := A.starts_at
      safe := A.safe
      finite_ends_at := ?_
      infinite := ?_
      eligible_finite := ?_
      eligible_infinite := ?_
      interior_disjoint_finite := ?_
      interior_disjoint_infinite := ?_
      outside := hA.outside }
  }
  · intro s v hterminal
    simpa only [D, endAt_ofSimultaneousPlain] using hterminal
  · intro s hinfinite
    rw [AltPath.isInfinite_iff_terminal?_eq_none]
    simpa only [D, endAt_ofSimultaneousPlain] using hinfinite
  · intro s v hterminal
    apply hA.eligible_finite s v
    simpa only [D, endAt_ofSimultaneousPlain] using hterminal
  · intro s hinfinite
    apply hA.eligible_infinite s
    rw [AltPath.isInfinite_iff_terminal?_eq_none]
    simpa only [D, endAt_ofSimultaneousPlain] using hinfinite
  · intro s v hterminal
    apply hA.interior_disjoint_finite s v
    simpa only [D, endAt_ofSimultaneousPlain] using hterminal
  · intro s hinfinite
    apply hA.interior_disjoint_infinite s
    rw [AltPath.isInfinite_iff_terminal?_eq_none]
    simpa only [D, endAt_ofSimultaneousPlain] using hinfinite

/-- Claim 2 for the occurrence endpoint map, proved from the selected
full-holes assignment's actual closure context. -/
theorem classified
    {persistent : Set V} {kappa : Cardinal.{u}}
    (P : OutsideDuplicatedProjection Zf Y hYfinite X
      before innerRoof outerRoof)
    (hclosed : HammockClosedUpTo Gamma Y X
      before innerRoof outerRoof kappa) :
    (∀ s v, P.duplicated.endAt hYfinite s = some v →
      IsImaginaryEdge Gamma Y kappa s.1 v) ∧
    (∀ s, P.duplicated.endAt hYfinite s = none →
      IsPopular Gamma Y persistent kappa s.1) :=
  CompressedFracturedAssignment.classify_of_projectionClosureContext
    (persistent := persistent) P.duplicated hYfinite hclosed P.projection

/-- A selected full-holes assignment with its genuine closure certificate
produces the classified occurrence endpoint data required by Assertion
9.31.  In particular, no closure of an unsplit row under `X` is assumed. -/
theorem exists_classifiedOutsideDuplicatedProjection
    {Zf : FracturedWarp Gamma}
    {X before innerRoof outerRoof persistent : Set V}
    {kappa : Cardinal.{u}}
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (A : SimultaneousAssignment Zf.paths Y)
    (hA : AssignmentClosureContext A X before innerRoof outerRoof)
    (hclosed : HammockClosedUpTo Gamma Y X
      before innerRoof outerRoof kappa) :
    ∃ P : OutsideDuplicatedProjection Zf Y hYfinite X
        before innerRoof outerRoof,
      (∀ s v, P.duplicated.endAt hYfinite s = some v →
        IsImaginaryEdge Gamma Y kappa s.1 v) ∧
      (∀ s, P.duplicated.endAt hYfinite s = none →
        IsPopular Gamma Y persistent kappa s.1) := by
  let P := OutsideDuplicatedProjection.ofAssignmentClosureContext
    (hYfinite := hYfinite) A hA
  exact ⟨P, P.classified hclosed⟩

end OutsideDuplicatedProjection
end Blueprint
end Erdos599
