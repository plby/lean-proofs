/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureOutsideLocalMatchingOrbitRoof
import ErdosProblems.Erdos599.HalfwayPostClosureOutsideReferenceEmbedding

/-!
# Claim 2 for the actual outside-local matching orbit

All closing-set, roof, endpoint, eligibility, and nondegeneracy inputs are
consequences of the actual post-closure interval transaction.  The only
remaining input is internal safeness of the compiled outside-local orbit.
The finite-reference embedding then transports it to the limiting reference
before applying the endpoint-covered form of Claim 2.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment

open DirectedPath _root_.Erdos599.Alternating
open _root_.Erdos599.TwoWarpMatchingTraversal

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z
  Rlimit.toDynamicMoving931GlobalClosure}

/-- The actual distinct first-return orbit satisfies every finite Claim-2
premise except internal safeness.  That one local premise is transported to
the genuine limiting warp by the interval-reference embedding. -/
theorem classify_actualOutsideLocalFirstReturn
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    (P : FinitePortPrefix T.interval.ambientInterval
      (outsideReference T.intervalReference Rlimit.closedSet) x)
    (hinterior : ∀ i : Fin (P.lastIndex + 1),
      0 < i.1 → i.1 < P.lastIndex →
        P.projectedVertex i ∉ Rlimit.closedSet)
    (hterminalX : P.projectedVertex
      ⟨P.lastIndex, Nat.lt_succ_self _⟩ ∈ Rlimit.closedSet)
    (hterminalNe : P.projectedVertex
      ⟨P.lastIndex, Nat.lt_succ_self _⟩ ≠ x)
    (hInternal : x ∉ Gamma.vertexSet C.ladder.limitWarp →
      P.projectedVertex ⟨P.lastIndex, Nat.lt_succ_self _⟩ ∉
        Gamma.vertexSet C.ladder.limitWarp →
      InternallySafe
        (outsideReference T.intervalReference Rlimit.closedSet)
        (P.altPath
          (M.actualOutsideLocalFirstReturn_projectedRoot_unique
            hx P hinterior hterminalNe))) :
    Nonempty (FiniteSegmentClassification
      (Y := C.ladder.limitWarp) (X := Rlimit.closedSet) (kappa := kappa)
      (P.altPath
        (M.actualOutsideLocalFirstReturn_projectedRoot_unique
          hx P hinterior hterminalNe))
      x (P.projectedVertex
        ⟨P.lastIndex, Nat.lt_succ_self _⟩)) := by
  let hrootUnique :=
    M.actualOutsideLocalFirstReturn_projectedRoot_unique
      hx P hinterior hterminalNe
  let Q := P.altPath hrootUnique
  apply classifyFinite Rlimit.hammock_closed Rlimit.reference_closed
      (fun _ _ ↦ M.actualOutsideLocalFirstReturn_hammockEligible
        hx P hterminalX)
      (fun hxY hvY ↦ T.internallySafe_limitWarp_of_outsideIntervalReference
        (hInternal hxY hvY))
  · exact P.altPath_initial hrootUnique
  · exact P.altPath_terminal hrootUnique
  · exact M.outsideLocalFirstReturn_hammockInterior_disjoint
      hx P hinterior hrootUnique
  · exact M.outsideLocalFirstReturn_altPath_not_subset_closedSet
      hx P hrootUnique
  · exact fun _ ↦ M.assignmentSource_mem_closedSet hx
  · exact fun _ ↦ hterminalX

/-- Infinite analogue: once the occurrence-aware compiler proves local
internal safeness, the actual no-return orbit is classified as either a
limiting popular end or a closed initial reference owner. -/
theorem classify_actualOutsideLocalInfinite
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    (P : InfinitePortPrefix T.interval.ambientInterval
      (outsideReference T.intervalReference Rlimit.closedSet) x)
    (houtside : ∀ n, 0 < n →
      P.projectedVertex n ∉ Rlimit.closedSet)
    (hInternal : x ∉ Gamma.vertexSet C.ladder.limitWarp →
      InternallySafe
        (outsideReference T.intervalReference Rlimit.closedSet)
        (P.altPath (M.assignmentSource_mem_closedSet hx) houtside
          T.interval.ambientInterval_linkage.isWarp
          T.interval.ambientInterval_linkage.finiteCharacter
          (T.intervalReference_isLinkageBetween.isWarp.subset
            (outsideReference_subset
              (Y := T.intervalReference) (X := Rlimit.closedSet))))) :
    Nonempty (InfiniteSegmentClassification
      (Y := C.ladder.limitWarp) (X := Rlimit.closedSet) (kappa := kappa)
      C.persistent
      (P.altPath (M.assignmentSource_mem_closedSet hx) houtside
        T.interval.ambientInterval_linkage.isWarp
        T.interval.ambientInterval_linkage.finiteCharacter
        (T.intervalReference_isLinkageBetween.isWarp.subset
          (outsideReference_subset
            (Y := T.intervalReference) (X := Rlimit.closedSet)))) x) := by
  let hrootX := M.assignmentSource_mem_closedSet hx
  let hW : Gamma.IsWarp T.interval.ambientInterval :=
    T.interval.ambientInterval_linkage.isWarp
  let hWfinite : Gamma.HasFiniteCharacter T.interval.ambientInterval :=
    T.interval.ambientInterval_linkage.finiteCharacter
  let hY : Gamma.IsWarp
      (outsideReference T.intervalReference Rlimit.closedSet) :=
    T.intervalReference_isLinkageBetween.isWarp.subset
      (outsideReference_subset
        (Y := T.intervalReference) (X := Rlimit.closedSet))
  let Q := P.altPath hrootX houtside hW hWfinite hY
  apply classifyInfinite Rlimit.hammock_closed Rlimit.reference_closed
      (fun _ ↦ M.actualOutsideLocalInfinite_hammockEligible hx P)
      (fun hxY ↦ T.internallySafe_limitWarp_of_outsideIntervalReference
        (hInternal hxY))
  · exact P.altPath_initial hrootX houtside hW hWfinite hY
  · change True
    exact True.intro
  · exact M.outsideLocalInfiniteOrbit_hammockInterior_disjoint hx P houtside
  · exact M.outsideLocalInfiniteOrbit_altPath_not_subset_closedSet hx P houtside
  · exact fun _ ↦ M.assignmentSource_mem_closedSet hx

#print axioms classify_actualOutsideLocalFirstReturn
#print axioms classify_actualOutsideLocalInfinite

end Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment
