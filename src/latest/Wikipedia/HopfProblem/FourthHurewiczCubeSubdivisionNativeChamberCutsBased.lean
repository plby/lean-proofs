import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeChamberCutsMaps
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeChamberExtension
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeCutBasic

/-!
# The actual independent based graphs for chamber insertion

Every interior endpoint agrees with one old physical coordinate after the
extended chart is applied. The extreme endpoints are zero and one. Thus
the required graph equations follow from the original cube's based faces.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision

variable {m n : ℕ}

theorem extendedChamberCutSequence_independent (h : m + 1 ≤ n)
    (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin (m + 2)) :
    CutIndependent (chamberCutIndex h) (extendedChamberCutSequence h e chart j) := by
  intro u v
  change chamberCutSequence e chart j
      (cubeRestriction (Nat.le_of_succ_le h) (Function.update u (chamberCutIndex h) v)) =
    chamberCutSequence e chart j (cubeRestriction (Nat.le_of_succ_le h) u)
  rw [cubeRestriction_update_outside (Nat.le_of_succ_le h) u (chamberCutIndex h) (le_refl m) v]

variable {X : Type*} [TopologicalSpace X] {x : X}

theorem extendedChamberCutSequence_based (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (h : m + 1 ≤ n) (e : Equiv.Perm (Fin m))
    (chart : NativeChamberChart e) (j : Fin (m + 2)) :
    CutBased (extendedChamberLoop p hp (Nat.le_of_succ_le h) chart) (chamberCutIndex h)
      (extendedChamberCutSequence h e chart j) := by
  intro u
  rw [extendedChamberLoop_apply,
    extendCubeMap_update_outside (Nat.le_of_succ_le h) chart.toContinuousMap u
      (chamberCutIndex h) (le_refl m)]
  refine Fin.cases ?_ (fun r => ?_) j
  · rw [extendedChamberCutSequence_zero]
    exact p.property _ ⟨chamberCutIndex h, Or.inl (Function.update_self _ _ _)⟩
  · rw [extendedChamberCutSequence_succ]
    by_cases hr : 0 < r.rev.val
    · let k : Fin m := ⟨r.rev.val - 1, by have := r.rev.isLt; omega⟩
      have hk : r.rev.val = k.val + 1 := by
        change r.rev.val = (r.rev.val - 1) + 1
        omega
      rw [chamberUpper_of_rank e r.rev chart (cubeRestriction (Nat.le_of_succ_le h) u) k hk]
      apply hp _ (chamberCutIndex h) (Fin.castLE (Nat.le_of_succ_le h) (e k))
        (chamberCutIndex_ne_castLE h (e k)).symm
      rw [Function.update_self, Function.update_of_ne (chamberCutIndex_ne_castLE h (e k)),
        extendCubeMap_castLE]
    · have hr0 : r.rev.val = 0 := by omega
      rw [chamberUpper_first e r.rev chart (cubeRestriction (Nat.le_of_succ_le h) u) hr0]
      exact p.property _ ⟨chamberCutIndex h, Or.inr (Function.update_self _ _ _)⟩

end Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision
