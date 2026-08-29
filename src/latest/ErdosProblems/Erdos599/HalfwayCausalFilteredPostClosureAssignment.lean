/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCausalNondegenerateHammockRows
import ErdosProblems.Erdos599.HalfwayFilteredMovingBetaLimit
import ErdosProblems.Erdos599.HalfwayCausalSafeCurrentPath
import ErdosProblems.Erdos599.HalfwayPostClosureMacroCompressorAssignment
import ErdosProblems.Erdos599.DeferredLegalLimitHitClosure
import ErdosProblems.Erdos599.HalfwayMovingReferenceReservoir

/-!
# The actual causal transaction with filtered closure retained

The stronger closure is constructed from the actual causal global carrier,
then carried through the moving-beta sequence before the interval is chosen.
The final record stores it on the same literal closing set as the macro
assignment. It does not assert switching safety of the old macro producer.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating Ladder
open _root_.Erdos599.CardinalInduction

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

structure CausalFilteredPostClosureMacroAssignment
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (globalZ base : Set V) (z : V) where
  safe : SafeCurrentStageTargetPath C z
  closure : LimitMoving931GlobalClosure C globalZ
    (base ∪ Gamma.vertexSet safe.ambientFamily)
  filtered_closed : FiniteFilteredHammockClosedUpTo Gamma C.ladder.limitWarp
    closure.closedSet closure.closedSet C.ladder.limitStrictRoof C.ladder.limitRoof
      (CoherentNondegenerateHammockTracker.CapturedByStageRoof C.ladder) kappa
  transaction : PostClosureIntervalTransaction C globalZ
    (base ∪ Gamma.vertexSet safe.ambientFamily) z
    closure.toDynamicMoving931GlobalClosure
  transaction_safe : transaction.safe = safe
  assignment : PostClosureMacroCompressorAssignment transaction

namespace CausalSection9Rows

theorem exists_filteredLimitMoving931GlobalClosure
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hC : C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed)
    (X0 : Set V)
    (hX0 : X0 ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed)
    (hX0card : #X0 ≤ kappa) :
    ∃ R : LimitMoving931GlobalClosure C
        (globalCarrier Gamma kappa hkappa hGamma seed hseed) X0,
      FiniteFilteredHammockClosedUpTo Gamma C.ladder.limitWarp
        R.closedSet R.closedSet C.ladder.limitStrictRoof C.ladder.limitRoof
          (CoherentNondegenerateHammockTracker.CapturedByStageRoof C.ladder) kappa := by
  have href : ClosedUnderPaths Gamma C.ladder.limitWarp
      (globalCarrier Gamma kappa hkappa hGamma seed hseed) := by
    simpa only [hC] using
      (reference_closed (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed)
  apply FilteredMovingBetaOmegaClosure.exists_limitClosure_for_movingReferenceDifference
    C (globalCarrier Gamma kappa hkappa hGamma seed hseed) X0
      (CoherentNondegenerateHammockTracker.CapturedByStageRoof C.ladder)
  · simpa only [hC] using
      (globalCarrier_subset_limitRoof
        (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed)
  · simpa only [hC] using
      (hammockClosed_limitWarp
        (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed)
  · simpa only [hC] using
      (finiteFilteredHammockClosed_limitWarp
        (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed)
  · exact href
  · exact hX0
  · exact hX0card
  · apply C.movingReferenceDifference_subset_of_recorded_marker_closed
    · intro a p hp
      apply chosen_support_subset_globalCarrier
        (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed
      simpa only [hC] using hp
    · simpa only [hC] using
        (markerSet_subset_globalCarrier
          (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed)
    · exact href
  · exact C.limitHitClosure

/-- The filtered certificate and the macro assignment are built in one
source-ordered transaction; neither is transported from an unrelated
choice of the closing set. -/
theorem exists_causalFilteredPostClosureMacroAssignment
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hC : C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed)
    (base : Set V)
    (hbase : base ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed)
    (hbaseCard : #base ≤ kappa) {z : V}
    (hz : z ∈ C.newSlice ∩ globalCarrier Gamma kappa hkappa hGamma seed hseed)
    (hext : ProtectedCardinalAssembly.ExtensionThroughFor Gamma kappa) :
    Nonempty (CausalFilteredPostClosureMacroAssignment C
      (globalCarrier Gamma kappa hkappa hGamma seed hseed) base z) := by
  obtain ⟨P, hPglobal, hPcard⟩ := exists_safeCurrentStageTargetPath_in_globalCarrier
    hkappa hGamma hseed C hC hz
  let X0 := base ∪ Gamma.vertexSet P.ambientFamily
  have hX0global : X0 ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed :=
    Set.union_subset hbase hPglobal
  have hX0card : #X0 ≤ kappa :=
    (Cardinal.mk_union_le base (Gamma.vertexSet P.ambientFamily)).trans
      (Cardinal.add_le_of_le hkappa hbaseCard hPcard)
  obtain ⟨R, hRfiltered⟩ := exists_filteredLimitMoving931GlobalClosure
    hkappa hGamma hseed C hC X0 hX0global hX0card
  let R0 := R.toDynamicMoving931GlobalClosure
  have hzOld : z ∈ R0.capturedGeometry.oldSlice := by
    simpa only [DynamicMoving931GlobalClosure.capturedGeometry_oldSlice] using hz.1
  obtain ⟨⟨I, hI⟩⟩ :=
    R0.capturedGeometry.exists_oldStageIntervalTransaction_of_safe_extensionThrough
      hext (P.toCaptured R0) hzOld
  let T : PostClosureIntervalTransaction C
      (globalCarrier Gamma kappa hkappa hGamma seed hseed) X0 z R0 := {
    safe := P
    safe_seeded := Set.subset_union_right
    safe_vertices_closed := Set.subset_union_right.trans R0.seed_subset
    interval := I
    interval_safe_eq := hI.1
    interval_reference_missing := hI.2 }
  obtain ⟨A⟩ := T.exists_macroCompressorAssignment
  exact ⟨{
    safe := P
    closure := R
    filtered_closed := hRfiltered
    transaction := T
    transaction_safe := rfl
    assignment := A }⟩

#print axioms exists_filteredLimitMoving931GlobalClosure
#print axioms exists_causalFilteredPostClosureMacroAssignment

end CausalSection9Rows
end Erdos599.Blueprint.LinkageBlueprint
