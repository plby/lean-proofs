/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCausalSafeCurrentPath
import ErdosProblems.Erdos599.HalfwayCausalMovingLimitClosure
import ErdosProblems.Erdos599.HalfwayPostClosureCompressorAssignment

/-!
# The actual causal safe-path, closure, interval and assignment pipeline

Choose the registered safe target path first.  Add its carrier to the small
seed, construct the exact moving-stage closure, and only then construct the
finite interval linkage and its compressor-realized fractured assignment.
The interval retains that same preselected path literally.  The lower
extension-through clause remains explicit; no half-way engine is assumed.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder
open _root_.Erdos599.CardinalInduction

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- A source-ordered transaction, retaining its preselected safe path and
all actual compressor witnesses for the later fractured assignment. -/
structure CausalPostClosureAssignment
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (globalZ base : Set V) (z : V) where
  safe : SafeCurrentStageTargetPath C z
  closure : LimitMoving931GlobalClosure C globalZ
    (base ∪ Gamma.vertexSet safe.ambientFamily)
  transaction : PostClosureIntervalTransaction C globalZ
    (base ∪ Gamma.vertexSet safe.ambientFamily) z
    closure.toDynamicMoving931GlobalClosure
  transaction_safe : transaction.safe = safe
  assignment : PostClosureCompressorAssignment transaction

namespace CausalSection9Rows

/-- The full pre-segmentation producer for the actual causal ladder.
Only the already established lower extension clause is used to complete the
interval after closing. -/
theorem exists_causalPostClosureAssignment
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hC : C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed)
    (base : Set V)
    (hbase : base ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed)
    (hbaseCard : #base ≤ kappa) {z : V}
    (hz : z ∈ C.newSlice ∩ globalCarrier Gamma kappa hkappa hGamma seed hseed)
    (hext : ProtectedCardinalAssembly.ExtensionThroughFor Gamma kappa) :
    Nonempty (CausalPostClosureAssignment C
      (globalCarrier Gamma kappa hkappa hGamma seed hseed) base z) := by
  obtain ⟨P, hPglobal, hPcard⟩ := exists_safeCurrentStageTargetPath_in_globalCarrier
    hkappa hGamma hseed C hC hz
  let X0 := base ∪ Gamma.vertexSet P.ambientFamily
  have hX0global : X0 ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed :=
    Set.union_subset hbase hPglobal
  have hX0card : #X0 ≤ kappa :=
    (Cardinal.mk_union_le base (Gamma.vertexSet P.ambientFamily)).trans
      (Cardinal.add_le_of_le hkappa hbaseCard hPcard)
  obtain ⟨R⟩ := exists_limitMoving931GlobalClosure hkappa hGamma hseed
    C hC X0 hX0global hX0card
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
  obtain ⟨A⟩ := T.exists_compressorAssignment
  exact ⟨{
    safe := P
    closure := R
    transaction := T
    transaction_safe := rfl
    assignment := A }⟩

#print axioms exists_causalPostClosureAssignment

end CausalSection9Rows
end Erdos599.Blueprint.LinkageBlueprint
