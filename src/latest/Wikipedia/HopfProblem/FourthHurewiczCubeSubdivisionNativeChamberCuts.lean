import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeChamberCutsBased
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeCutFinite

/-!
# Native class subdivision by one chamber insertion

The consecutive graph slices are literally the extended inserted charts.
Finite native subdivision and reversal of the insertion ranks therefore
give the one-step class identity for the original extended chamber loop.
-/

noncomputable section

open scoped Topology unitInterval BigOperators

namespace Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision

variable {m n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}

/-- Each actual graph slice equals the inserted chamber with reversed rank. -/
theorem extendedChamberCut_slice_eq (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (h : m + 1 ≤ n) (e : Equiv.Perm (Fin m))
    (chart : NativeChamberChart e) (j : Fin (m + 1)) :
    sliceLoop (extendedChamberLoop p hp (Nat.le_of_succ_le h) chart) (chamberCutIndex h)
      (extendedChamberCutSequence h e chart j.castSucc)
      (extendedChamberCutSequence h e chart j.succ)
      (extendedChamberCutSequence_based p hp h e chart j.castSucc)
      (extendedChamberCutSequence_based p hp h e chart j.succ) =
      extendedChamberLoop p hp h (insertChamberChart e j.rev chart) := by
  apply GenLoop.ext
  intro u
  rw [sliceLoop_apply, extendedChamberLoop_apply, extendedChamberCutSequence_castSucc,
    extendedChamberCutSequence_succ,
    extendCubeMap_update_outside (Nat.le_of_succ_le h) chart.toContinuousMap u
      (chamberCutIndex h) (le_refl m)]
  exact congrArg p (extend_insertChamberMap h e j.rev chart u).symm

/-- The native extended-chamber class is the sum over all genuine next-coordinate insertions. -/
theorem nativeClass_extendedChamber_eq_sum_insertions [Nontrivial (Fin n)]
    (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p) (h : m + 1 ≤ n)
    {e : Equiv.Perm (Fin m)} (chart : NativeChamberChart e) :
    nativeClass (extendedChamberLoop p hp (Nat.le_of_succ_le h) chart) =
      ∑ r : Fin (m + 1), nativeClass
        (extendedChamberLoop p hp h (insertChamberChart e r chart)) := by
  have hcut := finiteCuts_class (extendedChamberLoop p hp (Nat.le_of_succ_le h) chart)
    (chamberCutIndex h) (m + 1) (extendedChamberCutSequence h e chart)
    (extendedChamberCutSequence_based p hp h e chart)
    (extendedChamberCutSequence_independent h e chart)
    (extendedChamberCutSequence_zero h e chart) (extendedChamberCutSequence_last h e chart)
  have hrev : nativeClass (extendedChamberLoop p hp (Nat.le_of_succ_le h) chart) =
      ∑ j : Fin (m + 1), nativeClass
        (extendedChamberLoop p hp h (insertChamberChart e j.rev chart)) := by
    simpa only [extendedChamberCut_slice_eq p hp h e chart] using hcut
  exact hrev.trans (chamberCuts_sum_rev
    (fun r => nativeClass (extendedChamberLoop p hp h (insertChamberChart e r chart))))

end Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision
