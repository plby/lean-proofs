/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedFixedSafeAssignmentCutGeometry
import ErdosProblems.Erdos599.ColouredSafePostClosureEndpointExposure

/-!
# The actual simultaneous assignment in a native post-closure transaction

Pure interval boundaries supply the hypotheses of the fixed-original
assignment theorem. Cut certificates and global endpoint alternatives refer
to the same terminal-injective family. Covered endpoint owners remain
explicit alternatives; they are not classified as imaginary edges here.
-/

namespace Erdos599.Blueprint.LinkageBlueprint

open Set Cardinal Order DirectedPath
open _root_.Erdos599.Alternating
open ColouredSafeReverseReachability ColouredSafeMovingStages
open FracturedFixedSafeAssignment

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {seed : Set V} {z : V} {R : LimitClosure C seed}

namespace NativePostClosureIntervalTransaction

/-- The selected finite-edge endpoints lie in the actual native closed set.
This is a carrier statement, not an acyclicity or imaginary-edge assertion. -/
theorem fixedAssignment_finiteEdges_subset_closed
    (T : NativePostClosureIntervalTransaction C seed z R)
    (F : OutsideFracturedWarp T.interval.ambientInterval R.closedSet)
    (A : Assignment F.holes (outsideReference T.intervalReference R.closedSet)) :
    A.toCompressed.finiteEdges ⊆ R.closedSet ×ˢ R.closedSet := by
  rintro ⟨u, v⟩ ⟨s, hsv, rfl⟩
  have ht := A.finite_terminal s hsv
  exact ⟨T.uncovered_initials_subset_closedSet F s.2,
    T.finite_terminal_mem_closedSet F ht.1 ht.2⟩

/-- Construct the simultaneous assignment on the actual completed interval
row, with cut avoidance and endpoint alternatives retained for every chosen
word. All finite-terminal distinctness is part of the returned `Assignment`. -/
theorem exists_fixedOutsideAssignment
    (T : NativePostClosureIntervalTransaction C seed z R)
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
      (Gamma := Gamma) T.interval.ambientInterval R.closedSet)
    (hsub : HasHereditarySubdivisionIncidence Gamma.graph) :
    ∃ A : Assignment F.outside.holes (outsideReference T.intervalReference R.closedSet),
      (∀ s, HasCutGeometry R.closedSet (A.assigned s)) ∧
      (∀ s : Source F.outside.holes (outsideReference T.intervalReference R.closedSet),
        s.1 ∈ R.closedSet) ∧
      (∀ s t, (A.assigned s).terminal? = some t → t ∈ R.closedSet) ∧
      ∀ s,
        (∃ B : CurrentSafeOccurrence F.outside.holes.edgeWarp C.ladder.limitWarp s.1,
          B.forwardEdges = (A.assigned s).forwardEdges ∧
          B.vertexSet = (A.assigned s).vertexSet ∧
          B.terminal? = (A.assigned s).terminal?) ∨
        (∃ p ∈ C.ladder.limitWarp, s.1 ∈ p.support ∧ p.support ⊆ R.closedSet) ∨
        ∃ t, (A.assigned s).terminal? = some t ∧
          ∃ p ∈ C.ladder.limitWarp, t ∈ p.support ∧ p.support ⊆ R.closedSet := by
  obtain ⟨hboundary, hsource⟩ := T.boundaryData_of_interval_purity F
  have hLocalWarp : Gamma.IsWarp (outsideReference T.intervalReference R.closedSet) :=
    outsideReference_isWarp T.intervalReference_isLinkageBetween.isWarp
  have hLocalFinite : Gamma.HasFiniteCharacter
      (outsideReference T.intervalReference R.closedSet) :=
    outsideReference_finiteCharacter T.intervalReference_isLinkageBetween.finiteCharacter
  obtain ⟨A, hA⟩ := exists_outside_assignment_with_cutGeometry F.outside hsub
    hboundary hLocalWarp hLocalFinite hsource vertexSet_outsideReference_disjoint.symm
  refine ⟨A, hA, ?_, ?_, ?_⟩
  · intro s
    exact T.uncovered_initials_subset_closedSet F.outside s.2
  · intro s t ht
    have hterm := A.finite_terminal s ht
    exact T.finite_terminal_mem_closedSet F.outside hterm.1 hterm.2
  · intro s
    exact T.globalOccurrence_or_closedEndpointOwner F.outside s.2 (A.assigned s)
      (fun _ ht ↦ A.finite_terminal s ht) (hA s).finite_cut (hA s).infinite_cut

end NativePostClosureIntervalTransaction

#print axioms NativePostClosureIntervalTransaction.fixedAssignment_finiteEdges_subset_closed
#print axioms NativePostClosureIntervalTransaction.exists_fixedOutsideAssignment

end Erdos599.Blueprint.LinkageBlueprint
