/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFiniteCertifiedClassifiedProducer
import ErdosProblems.Erdos599.HalfwayPostClosureActualFiniteSegmentation

/-!
# Certified actual finite post-closure segmentation

This additive producer chooses the deterministic endpoint-case segmentation.
Thus every contributed shortcut retains the exposed safeness and geometry of
the literal compressor break interval.  The older existence theorem remains
unchanged and no property is inferred from one of its arbitrary witnesses.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z
  Rlimit.toDynamicMoving931GlobalClosure}

/-- The actual finite compressor branch, with exact coordinates and a
certificate for every piece which contributes a shortcut. -/
theorem exists_actualFiniteClosedClassifiedContactSegmentation_with_certificates
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    (S : RunCompressor.FiniteInput Gamma.graph)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .finite S.toFiniteRunWalk.toFiniteTrace) :
    ∃ D : FiniteClosedClassifiedContactSegmentation
        (Y := C.ladder.limitWarp) (kappa := kappa)
        (AltPath.finite S.toFiniteRunWalk.toFiniteTrace) Rlimit.closedSet,
      ∃ hcount : D.count = S.finiteWalk.breakCount Rlimit.closedSet,
        D.toChain.contactSet ⊆ Rlimit.closedSet ∧
        (∀ i, D.point i = S.finiteWalk.breakPoint Rlimit.closedSet
          (Fin.cast (congrArg (fun n : Nat ↦ n + 1) hcount) i)) ∧
        (∀ i : Fin D.count, (D.piece i).path =
          S.breakIntervalPath Rlimit.closedSet (Fin.cast hcount i)) ∧
        ∀ (i : Fin D.count) e, e ∈ (D.piece i).shortcutEdges →
          D.point i.castSucc ∉ Gamma.vertexSet C.ladder.limitWarp ∧
          D.point i.succ ∉ Gamma.vertexSet C.ladder.limitWarp ∧
          IsSafe C.ladder.limitWarp (D.piece i).path ∧
          HammockEligible Rlimit.closedSet C.ladder.limitStrictRoof
            C.ladder.limitRoof (D.point i.castSucc) (.vertex (D.point i.succ)) ∧
          Disjoint (hammockInterior (D.point i.castSucc)
            (.vertex (D.point i.succ)) (D.piece i).path) Rlimit.closedSet ∧
          ¬(D.piece i).path.vertexSet ⊆ Rlimit.closedSet := by
  have hsX : s.1 ∈ Rlimit.closedSet :=
    T.uncovered_initials_subset_closedSet Rlimit A.fractured s.2
  have hstart := A.assignment.produced.bracket.assignment.starts_at s
  rw [hS] at hstart
  have hinitial : S.vertex 0 ∈ Rlimit.closedSet := by
    rw [← hstart] at hsX
    have hsX' : S.toFiniteRunWalk.vertex 0 ∈ Rlimit.closedSet := by
      simpa only [AltPath.initial, FiniteRunWalk.toFiniteTrace_initial] using hsX
    change S.toFiniteRunWalk.vertex 0 ∈ Rlimit.closedSet
    exact hsX'
  have hterminalEq :
      (A.assignment.produced.bracket.assignment.assigned s).terminal? =
        some (S.vertex S.lastEdge) := by
    rw [hS]
    simp only [AltPath.terminal?, FiniteRunWalk.toFiniteTrace_terminal,
      S.toFiniteRunWalk_final_last]
    rfl
  have hterminal : S.vertex S.lastEdge ∈ Rlimit.closedSet :=
    A.finite_terminal_mem_closedSet s hterminalEq
  have hpoint : ∀ i,
      S.finiteWalk.breakPoint Rlimit.closedSet i ∈ Rlimit.closedSet := by
    intro i
    apply S.finiteWalk.breakPoint_mem_of_endpoints_mem Rlimit.closedSet
    · exact hinitial
    · rw [S.finiteWalk_finalPosition]
      exact hterminal
  obtain ⟨D, hcount, hpoints, hrest⟩ :=
    FiniteBreakMixedPiece.exists_finiteClosedClassifiedContactSegmentation_with_certificates
      S Rlimit.closedSet Rlimit.hammock_closed Rlimit.reference_closed
      (fun i _ _ ↦
        A.finite_breakInterval_hammockEligible s S hS hinitial hterminal i)
      (fun i _ _ ↦ A.finite_breakInterval_internallySafe s S hS i)
      (fun i _ ↦ hpoint i.castSucc) (fun i _ ↦ hpoint i.succ)
  have hpaths := hrest.1
  have hcert := hrest.2
  refine ⟨D, hcount, ?_, hpoints, hpaths, hcert⟩
  rintro x ⟨i, rfl⟩
  change D.point i ∈ Rlimit.closedSet
  rw [hpoints i]
  exact hpoint _

#print axioms
  exists_actualFiniteClosedClassifiedContactSegmentation_with_certificates

end Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment
