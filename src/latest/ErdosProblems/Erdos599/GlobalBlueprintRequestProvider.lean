/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GlobalBlueprintReplacement

/-!
# A canonical closed fractured-replacement request

This file isolates the strongest unconditional constructor permitted by the
current `ClosedFracturedReplacementRequestProvider` interface.  When the
reference warp itself runs from the source side to the target side, regard it
as an honest fractured warp.  Its initial set is already covered by the
reference warp, so the simultaneous-assignment domain is empty.  Consequently
all assignment-closure obligations are vacuous, and choosing an empty inner
roof makes the hammock-closure obligation vacuous as well.

This construction is deliberately kept separate from the geometric
replacement compiler.  It exposes an important feature of the current API:
the request provider does not state that its fractured family contains, or is
otherwise related to, the scheduled real terminal.  Any such relationship
needed to resolve that terminal must therefore be supplied by the
`WholeFamilySpliceRelationCompiler`.
-/

noncomputable section

open Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

/-! ## A scheduled strengthening of the request API -/

/-- Source-faithful strengthening of a closed replacement request.  The
scheduled terminal is required to be an uncovered source of the fractured
family, so the simultaneous assignment actually contains a path assigned to
that vertex.  The existing `ClosedFracturedReplacementRequestProvider` omits
this relationship and therefore also admits the vacuous canonical provider
constructed below. -/
structure ScheduledClosedFracturedReplacementRequest
    (W : LinkageBlueprint Gamma Y kappa) (u : V)
    (persistent : Set V) where
  request : ClosedFracturedReplacementRequest
    (Gamma := Gamma) (Y := Y) (kappa := kappa) persistent
  scheduled_uncovered : u ∈
    Gamma.initialSet request.fractured.paths \ Gamma.initialSet Y

/-- The repaired provider interface: every scheduled real terminal receives
a closed fractured request in whose assignment domain it occurs. -/
def ScheduledClosedFracturedReplacementRequestProvider
    (T Z persistent : Set V) : Prop :=
  ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint T Z persistent → persistent ⊆ T →
      u ∈ W.realPart.terminals →
        Nonempty (ScheduledClosedFracturedReplacementRequest W u persistent)

/-- Forgetting the scheduled-source witness recovers the original provider
interface. -/
theorem closedProvider_of_scheduledProvider
    {T Z persistent : Set V}
    (hprovider : ScheduledClosedFracturedReplacementRequestProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent) :
    ClosedFracturedReplacementRequestProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent := by
  intro W u hW hpersistent hu
  exact (hprovider W u hW hpersistent hu).map
    ScheduledClosedFracturedReplacementRequest.request

/-- An honest warp is, tautologically, a fractured warp with the same path
family as its edge-warp realization. -/
def honestFracturedWarp (hYwarp : Gamma.IsWarp Y) :
    FracturedWarp Gamma where
  paths := Y
  edgeWarp := Y
  edgeWarp_isWarp := hYwarp
  same_edges := rfl
  allowed_intersection := by
    intro p hp q hq hpq hmeet
    exact (hmeet (hYwarp hp hq hpq)).elim

@[simp] theorem honestFracturedWarp_paths (hYwarp : Gamma.IsWarp Y) :
    (honestFracturedWarp hYwarp).paths = Y :=
  rfl

/-- The assignment domain for the honest reference request is empty. -/
private theorem false_of_honest_assignment_source
    (hYwarp : Gamma.IsWarp Y)
    (s : {z : V // z ∈ Gamma.initialSet (honestFracturedWarp hYwarp).paths \
      Gamma.initialSet Y}) : False := by
  exact s.property.2 s.property.1

/-- The reference warp gives a canonical closed fractured request whenever it
already has the endpoint properties required by Theorem 4.12.

The four closure sets are empty.  Hammock eligibility is then impossible,
and every field of `AssignmentClosureContext` is vacuous because the
assignment has no sources. -/
def canonicalClosedFracturedReplacementRequest
    (hYwarp : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hYsource : Gamma.initialSet Y ⊆ Gamma.source)
    (hYtarget : Gamma.terminalFrontier Y ⊆ Gamma.target)
    (persistent : Set V) :
    ClosedFracturedReplacementRequest
      (Gamma := Gamma) (Y := Y) (kappa := kappa) persistent where
  fractured := honestFracturedWarp hYwarp
  closureSet := ∅
  before := ∅
  innerRoof := ∅
  outerRoof := ∅
  source_side := hYsource
  target_side := hYtarget
  finite_character := hYfinite
  reference_initials := Subset.rfl
  closed := by
    intro u e heligible
    exact (heligible.1.2 : u ∈ (∅ : Set V)).elim
  closure_facts := by
    intro A
    refine
      { eligible_finite := ?_
        eligible_infinite := ?_
        interior_disjoint_finite := ?_
        interior_disjoint_infinite := ?_
        outside := ?_ }
    · intro s v _hterminal
      exact (false_of_honest_assignment_source hYwarp s).elim
    · intro s _hinfinite
      exact (false_of_honest_assignment_source hYwarp s).elim
    · intro s v _hterminal
      exact (false_of_honest_assignment_source hYwarp s).elim
    · intro s _hinfinite
      exact (false_of_honest_assignment_source hYwarp s).elim
    · intro s
      exact (false_of_honest_assignment_source hYwarp s).elim

/-- The canonical request is uniform in the scheduled blueprint and terminal,
so it supplies the current request-provider interface without any additional
choice or closure hypothesis. -/
theorem closedFracturedReplacementRequestProvider_of_referenceWarp
    (hYwarp : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hYsource : Gamma.initialSet Y ⊆ Gamma.source)
    (hYtarget : Gamma.terminalFrontier Y ⊆ Gamma.target)
    (T Z persistent : Set V) :
    ClosedFracturedReplacementRequestProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent := by
  intro W u _hW _hpersistent _hu
  exact ⟨canonicalClosedFracturedReplacementRequest
    hYwarp hYfinite hYsource hYtarget persistent⟩

/-- With the canonical request, the global replacement theorem no longer
needs a separate request-provider hypothesis.  The remaining inputs are the
actual simultaneous-assignment theorem and the whole-family splice compiler,
which is where the scheduled terminal must be used. -/
theorem stable934Compiler_of_referenceWarpSplice
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hYsource : Gamma.initialSet Y ⊆ Gamma.source)
    (hYtarget : Gamma.terminalFrontier Y ⊆ Gamma.target)
    (hassignment : FracturedSimultaneousAssignmentStatement Gamma)
    {T Z persistent B : Set V}
    (hsplice : WholeFamilySpliceRelationCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B := by
  apply stable934Compiler_of_globalFracturedSplice
      hGamma hYwarp hYfinite hassignment
  · exact closedFracturedReplacementRequestProvider_of_referenceWarp
      hYwarp hYfinite hYsource hYtarget T Z persistent
  · exact hsplice

end LinkageBlueprint
end Blueprint
end Erdos599
