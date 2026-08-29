/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureActualFiniteCertifiedSegmentation
import ErdosProblems.Erdos599.HalfwayPostClosureFiniteBreakDegeneracy
import ErdosProblems.Erdos599.CoherentNondegenerateHammockLargeDiagnostic

/-!
# Actual certified finite pieces: degeneracy or a filtered large witness

The deterministic finite producer retains the individual interval's safety,
exposed endpoints, and outside-carrier proof. The actual captured roof supplies
the filter. Inserting this very interval into the filtered maximal family
gives degeneracy or a successor-sized filtered hammock. No arbitrary
classification choice or unrelated degenerate witness is used.
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

/-- A finite segmentation with literal coordinates and the actual
degenerate-or-large alternative for each contributed shortcut. -/
theorem exists_actualFiniteSegmentation_with_filtered_alternative
    (A : PostClosureCompressorAssignment T)
    (hfiltered : FiniteFilteredHammockClosedUpTo Gamma C.ladder.limitWarp
      Rlimit.closedSet Rlimit.closedSet C.ladder.limitStrictRoof C.ladder.limitRoof
        (CoherentNondegenerateHammockTracker.CapturedByStageRoof C.ladder) kappa)
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
          IsSafe C.ladder.limitWarp (D.piece i).path ∧
          CoherentNondegenerateHammockTracker.CapturedByStageRoof C.ladder
            (D.piece i).path ∧
          (IsDegenerate C.ladder.limitWarp (D.piece i).path (.vertex e.2) ∨
            HasFilteredNondegenerateHammockCard Gamma C.ladder.limitWarp
              e.1 (.vertex e.2)
              (CoherentNondegenerateHammockTracker.CapturedByStageRoof C.ladder)
              (succ kappa)) := by
  obtain ⟨D, hcount, hcontacts, hpoints, hpaths, hcert⟩ :=
    A.exists_actualFiniteClosedClassifiedContactSegmentation_with_certificates s S hS
  refine ⟨D, hcount, hcontacts, hpoints, hpaths, ?_⟩
  intro i e he
  have heq := (D.piece i).mem_shortcutEdges_eq he
  subst e
  obtain ⟨_huOff, _hvOff, hsafe, helig, hdisj, houtside⟩ := hcert i _ he
  have hcaptured : CoherentNondegenerateHammockTracker.CapturedByStageRoof C.ladder
      (D.piece i).path := by
    rw [hpaths i]
    exact A.finite_breakInterval_capturedByStageRoof s S hS (Fin.cast hcount i)
  refine ⟨hsafe, hcaptured, ?_⟩
  by_cases hdeg : IsDegenerate C.ladder.limitWarp (D.piece i).path
      (.vertex (D.point i.succ))
  · exact Or.inl hdeg
  · right
    have hne : D.point i.castSucc ≠ D.point i.succ := by
      intro heq
      have hi := congrArg Fin.val (D.point_injective heq)
      simp only [Fin.val_castSucc, Fin.val_succ] at hi
      omega
    obtain ⟨H, hH, hHX⟩ := hfiltered _ _ hne helig
    exact hH.exists_filteredCard_succ_of_outside hHX hsafe
      (D.piece i).starts_at (D.piece i).ends_at hdeg hcaptured hdisj houtside

/-- Forgetting only the filter yields the original strong-edge predicate;
therefore a non-strong shortcut in the certified segmentation has its
particular piece degenerate. -/
theorem isDegenerate_of_filtered_alternative_of_not_strong
    {Q : AltPath Gamma.graph} {u₀ v : V}
    (halt : IsDegenerate C.ladder.limitWarp Q (.vertex v) ∨
      HasFilteredNondegenerateHammockCard Gamma C.ladder.limitWarp
        u₀ (.vertex v)
        (CoherentNondegenerateHammockTracker.CapturedByStageRoof C.ladder)
        (succ kappa))
    (hnot : ¬IsStrongImaginaryEdge Gamma C.ladder.limitWarp kappa u₀ v) :
    IsDegenerate C.ladder.limitWarp Q (.vertex v) := by
  rcases halt with hdeg | ⟨H, hH, hcard⟩
  · exact hdeg
  · exact (hnot ⟨H, hH.1, hcard⟩).elim

#print axioms exists_actualFiniteSegmentation_with_filtered_alternative
#print axioms isDegenerate_of_filtered_alternative_of_not_strong

end Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment
