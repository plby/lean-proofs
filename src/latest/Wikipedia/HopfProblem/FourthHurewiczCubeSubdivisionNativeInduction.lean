import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeChamberCuts
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeChamberDuffy

/-!
# Native subdivision by successive coordinate insertion

Each stage cuts one additional coordinate into the gaps of the previously
ordered coordinates. Genuine relative homotopies replace the inserted
charts by canonical charts with the same face conditions. The insertion
equivalence accounts for all permutations in every dimension.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision

variable {n : ℕ} [Nontrivial (Fin n)]
variable {X : Type*} [TopologicalSpace X] {x : X}

/-- After inserting the first `m` coordinates, the original class is the
sum of the actual extended chamber classes, indexed by all permutations. -/
theorem nativeClass_eq_sum_partialChambers (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (m : ℕ) (h : m ≤ n) :
    nativeClass p = ∑ e : Equiv.Perm (Fin m),
      nativeClass (extendedChamberLoop p hp h (orderedDuffyChart e)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [sum_insertPermutation]
      calc
        nativeClass p = ∑ e : Equiv.Perm (Fin m),
            nativeClass (extendedChamberLoop p hp (Nat.le_of_succ_le h)
              (orderedDuffyChart e)) := ih (Nat.le_of_succ_le h)
        _ = ∑ e : Equiv.Perm (Fin m), ∑ r : Fin (m + 1),
            nativeClass (extendedChamberLoop p hp h
              (orderedDuffyChart (insertPermutation e r))) := by
          apply Finset.sum_congr rfl
          intro e _
          rw [nativeClass_extendedChamber_eq_sum_insertions p hp h (orderedDuffyChart e)]
          apply Finset.sum_congr rfl
          intro r _
          exact nativeClass_extendedChamber_eq p hp h
            (insertChamberChart e r (orderedDuffyChart e))
            (orderedDuffyChart (insertPermutation e r))

end Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision
