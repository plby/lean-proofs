/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedCanonicalBoundary
import ErdosProblems.Erdos599.FracturedCanonicalOccurrenceProjection
import ErdosProblems.Erdos599.ColouredFracturedPeelPromotion

/-!
# Safe projection of canonical fractured occurrence words

The canonical role lift is first projected against the peeled reference
`activeReference Z Y`.  The boundary geometry discharges the exposed-endpoint
and isolated-singleton obligations of the literal projection theorem.  The
peeled word is then retyped, without changing any occurrence, to the full
reference `Y` using `ColouredFracturedPeelPromotion`.

The forward family of every output is the original honest edge warp
`Z.edgeWarp`; no projected current fractured family is introduced.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.FracturedCanonicalSafeProjection

open Set DirectedPath Alternating
open Alternating.FracturedDuplication
open Alternating.FracturedCanonicalFiniteLift
open Alternating.FracturedCanonicalReferenceLift
open Alternating.FracturedCanonicalOccurrenceProjection
open FracturedAssignmentPeel
open FracturedCanonicalBoundary
open ColouredSafeReverseReachability

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- The actual finite downstairs word.  Projection is performed against the
peeled reference and promotion changes only its reference type. -/
def finiteSafeProjection (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (Q : FiniteColouredOccurrenceWord
      (canonicalActiveLift Z) (canonicalPeeledReferenceLift Z Y)) :
    FiniteColouredOccurrenceWord Z.edgeWarp Y :=
  promoteFiniteReference
    (finiteProjection Z (activeReference_hasFiniteCharacter Z hYfinite) Q)
    (familyEdges_activeReference Z).subset

@[simp] theorem finiteSafeProjection_first
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (Q : FiniteColouredOccurrenceWord
      (canonicalActiveLift Z) (canonicalPeeledReferenceLift Z Y)) :
    (finiteSafeProjection Z hYfinite Q).vertex 0 = project (Q.vertex 0) := by
  change (finiteProjection Z
    (activeReference_hasFiniteCharacter Z hYfinite) Q).vertex 0 = _
  exact finiteProjection_first Z
    (activeReference_hasFiniteCharacter Z hYfinite) Q

@[simp] theorem finiteSafeProjection_last
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (Q : FiniteColouredOccurrenceWord
      (canonicalActiveLift Z) (canonicalPeeledReferenceLift Z Y)) :
    (finiteSafeProjection Z hYfinite Q).vertex
        (Fin.last (finiteSafeProjection Z hYfinite Q).length) =
      project (Q.vertex (Fin.last Q.length)) := by
  change (finiteProjection Z
    (activeReference_hasFiniteCharacter Z hYfinite) Q).vertex
      (Fin.last (finiteProjection Z
        (activeReference_hasFiniteCharacter Z hYfinite) Q).length) = _
  exact finiteProjection_last Z
    (activeReference_hasFiniteCharacter Z hYfinite) Q

/-- Full-reference interval safeness of the actual finite projection. -/
theorem finiteSafeProjection_isIntervalSafe
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths)
    (hnoJunction :
      NoJunctionOnReference Z (activeReference Z Y))
    (Q : FiniteColouredOccurrenceWord
      (canonicalActiveLift Z) (canonicalPeeledReferenceLift Z Y))
    (hQ : Q.IsIntervalSafe)
    (hfirstForward : Q.vertex 0 ∈
      (web Gamma Z).initialSet (canonicalActiveLift Z))
    (hfirstReference : Q.vertex 0 ∉
      (web Gamma Z).initialSet (canonicalPeeledReferenceLift Z Y))
    (hlastForward : Q.vertex (Fin.last Q.length) ∈
      (web Gamma Z).terminalFrontier (canonicalActiveLift Z))
    (hlastReference : Q.vertex (Fin.last Q.length) ∉
      (web Gamma Z).vertexSet (canonicalPeeledReferenceLift Z Y)) :
    (finiteSafeProjection Z hYfinite Q).IsIntervalSafe := by
  let Ya := activeReference Z Y
  have hYa : Gamma.IsWarp Ya := activeReference_isWarp Z hY
  have hYafin : Gamma.HasFiniteCharacter Ya :=
    activeReference_hasFiniteCharacter Z hYfinite
  have hfirstFull : project (Q.vertex 0) ∉ Gamma.vertexSet Y :=
    project_not_mem_vertexSet_of_initial_sdiff Z hboundary hYfinite
      hfirstForward hfirstReference
  have hlastFull :
      project (Q.vertex (Fin.last Q.length)) ∉ Gamma.vertexSet Y :=
    project_not_mem_vertexSet_of_terminal_sdiff Z hboundary hY hYfinite
      hsource hnoJunction hlastForward hlastReference
  have hisolatedFull : ∀ {x y : V},
      (x, y) ∈ properImage Q.forwardEdges →
        x ∉ isolatedVertices Y ∧ y ∉ isolatedVertices Y := by
    intro x y hxy
    apply intervalSafe_properForwardImage_endpoints_not_isolated
      Z hsource hnoJunction Q hQ
    simpa [properImage, FiniteColouredOccurrenceWord.mapEdge] using hxy
  have hprojected :
      (finiteProjection Z hYafin Q).IsIntervalSafe := by
    apply finiteProjection_isIntervalSafe Z hYa hYafin Q hQ
    · rintro ⟨p, hp, hmem⟩
      exact hfirstFull ⟨p, activeReference_subset Z Y hp, hmem⟩
    · rintro ⟨p, hp, hmem⟩
      exact hlastFull ⟨p, activeReference_subset Z Y hp, hmem⟩
    · intro x y hxy
      have hfull := hisolatedFull hxy
      exact ⟨fun hx ↦ hfull.1 ((activeReference_subset Z Y) hx),
        fun hy ↦ hfull.2 ((activeReference_subset Z Y) hy)⟩
  exact finite_promotePeeledReference_isIntervalSafe Z
    (finiteProjection Z hYafin Q) hprojected

/-- The selected finite endpoint remains an actual downstairs active
fractured terminal outside the full reference carrier. -/
theorem finiteSafeProjection_terminal_mem
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths)
    (hnoJunction :
      NoJunctionOnReference Z (activeReference Z Y))
    (Q : FiniteColouredOccurrenceWord
      (canonicalActiveLift Z) (canonicalPeeledReferenceLift Z Y))
    (hlastForward : Q.vertex (Fin.last Q.length) ∈
      (web Gamma Z).terminalFrontier (canonicalActiveLift Z))
    (hlastReference : Q.vertex (Fin.last Q.length) ∉
      (web Gamma Z).vertexSet (canonicalPeeledReferenceLift Z Y)) :
    (finiteSafeProjection Z hYfinite Q).vertex
        (Fin.last (finiteSafeProjection Z hYfinite Q).length) ∈
      Gamma.terminalFrontier (activePaths Z) \ Gamma.vertexSet Y := by
  rw [finiteSafeProjection_last]
  constructor
  · rcases terminal_data_canonicalActiveLift Z hlastForward with
      ⟨x, hx, heq⟩
    simpa [heq] using hx
  · exact project_not_mem_vertexSet_of_terminal_sdiff Z hboundary hY
      hYfinite hsource hnoJunction hlastForward hlastReference

/-- The actual infinite downstairs word, promoted unchanged from the peeled
reference to the full reference. -/
def infiniteSafeProjection (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hY : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (Q : InfiniteColouredOccurrenceWord
      (canonicalActiveLift Z) (canonicalPeeledReferenceLift Z Y)) :
    InfiniteColouredOccurrenceWord Z.edgeWarp Y :=
  promoteInfiniteReference
    (infiniteProjection Z (activeReference_isWarp Z hY)
      (activeReference_hasFiniteCharacter Z hYfinite) Q)
    (familyEdges_activeReference Z).subset

@[simp] theorem infiniteSafeProjection_first
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hY : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (Q : InfiniteColouredOccurrenceWord
      (canonicalActiveLift Z) (canonicalPeeledReferenceLift Z Y)) :
    (infiniteSafeProjection Z hY hYfinite Q).vertex 0 =
      project (Q.vertex 0) := by
  change (infiniteProjection Z (activeReference_isWarp Z hY)
    (activeReference_hasFiniteCharacter Z hYfinite) Q).vertex 0 = _
  exact infiniteProjection_first Z (activeReference_isWarp Z hY)
    (activeReference_hasFiniteCharacter Z hYfinite) Q

/-- Full-reference interval safeness of the actual infinite projection. -/
theorem infiniteSafeProjection_isIntervalSafe
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths)
    (hnoJunction :
      NoJunctionOnReference Z (activeReference Z Y))
    (Q : InfiniteColouredOccurrenceWord
      (canonicalActiveLift Z) (canonicalPeeledReferenceLift Z Y))
    (hQ : Q.IsIntervalSafe)
    (hfirstForward : Q.vertex 0 ∈
      (web Gamma Z).initialSet (canonicalActiveLift Z))
    (hfirstReference : Q.vertex 0 ∉
      (web Gamma Z).initialSet (canonicalPeeledReferenceLift Z Y)) :
    (infiniteSafeProjection Z hY hYfinite Q).IsIntervalSafe := by
  let Ya := activeReference Z Y
  have hYa : Gamma.IsWarp Ya := activeReference_isWarp Z hY
  have hYafin : Gamma.HasFiniteCharacter Ya :=
    activeReference_hasFiniteCharacter Z hYfinite
  have hfirstFull : project (Q.vertex 0) ∉ Gamma.vertexSet Y :=
    project_not_mem_vertexSet_of_initial_sdiff Z hboundary hYfinite
      hfirstForward hfirstReference
  have hisolatedFull : ∀ {x y : V},
      (x, y) ∈ properImage Q.forwardEdges →
        x ∉ isolatedVertices Y ∧ y ∉ isolatedVertices Y := by
    intro x y hxy
    apply properForwardImage_endpoints_not_isolated Z hsource hnoJunction
      Q.forwardEdges_subset_familyEdges hQ.endpoint_pure
    simpa [properImage, FiniteColouredOccurrenceWord.mapEdge] using hxy
  have hprojected :
      (infiniteProjection Z hYa hYafin Q).IsIntervalSafe := by
    apply infiniteProjection_isIntervalSafe Z hYa hYafin Q hQ
    · rintro ⟨p, hp, hmem⟩
      exact hfirstFull ⟨p, activeReference_subset Z Y hp, hmem⟩
    · intro x y hxy
      have hfull := hisolatedFull hxy
      exact ⟨fun hx ↦ hfull.1 ((activeReference_subset Z Y) hx),
        fun hy ↦ hfull.2 ((activeReference_subset Z Y) hy)⟩
  exact infinite_promotePeeledReference_isIntervalSafe Z
    (infiniteProjection Z hYa hYafin Q) hprojected

#print axioms finiteSafeProjection_isIntervalSafe
#print axioms finiteSafeProjection_terminal_mem
#print axioms infiniteSafeProjection_isIntervalSafe

end Erdos599.Blueprint.LinkageBlueprint.FracturedCanonicalSafeProjection
