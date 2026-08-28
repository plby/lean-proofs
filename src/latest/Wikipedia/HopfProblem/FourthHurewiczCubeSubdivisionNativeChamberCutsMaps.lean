import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeChamberCutsEndpoints
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeExtension
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeChamberCharts

/-!
# Actual ambient coordinate formulas for a chamber insertion

Extending an inserted chamber changes exactly the new physical coordinate.
The old-coordinate restriction ignores that coordinate, so the ambient cut
endpoints are independent of it.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision

variable {m n : ℕ}

def chamberCutIndex (h : m + 1 ≤ n) : Fin n := Fin.castLE h (Fin.last m)

@[simp] theorem chamberCutIndex_val (h : m + 1 ≤ n) : (chamberCutIndex h).val = m := rfl

theorem chamberCutIndex_ne_castLE (h : m + 1 ≤ n) (j : Fin m) :
    Fin.castLE (Nat.le_of_succ_le h) j ≠ chamberCutIndex h := by
  intro he
  have hv := congrArg Fin.val he
  exact (Nat.ne_of_lt j.isLt) hv

@[simp] theorem chamberOldCoordinates_cubeRestriction (h : m + 1 ≤ n)
    (u : NativeCube (Fin n)) :
    chamberOldCoordinates (cubeRestriction h u) = cubeRestriction (Nat.le_of_succ_le h) u := rfl

/-- The extended inserted chart is literally an update of the old extended chart. -/
theorem extend_insertChamberMap (h : m + 1 ≤ n) (e : Equiv.Perm (Fin m))
    (r : Fin (m + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) :
    extendCubeMap h (insertChamberMap e r chart) u =
      Function.update (extendCubeMap (Nat.le_of_succ_le h) chart.toContinuousMap u)
        (chamberCutIndex h)
        (Set.Icc.convexComb
          (chamberLower e r chart (cubeRestriction (Nat.le_of_succ_le h) u))
          (chamberUpper e r chart (cubeRestriction (Nat.le_of_succ_le h) u))
          (u (chamberCutIndex h))) := by
  funext j
  by_cases hjm : j.val < m
  · let k : Fin m := ⟨j.val, hjm⟩
    have hk : Fin.castLE h k.castSucc = j := Fin.ext rfl
    have hk' : Fin.castLE h k.castSucc = Fin.castLE (Nat.le_of_succ_le h) k := Fin.ext rfl
    have hji : j ≠ chamberCutIndex h := by
      rw [← hk, hk']
      exact chamberCutIndex_ne_castLE h k
    rw [Function.update_of_ne hji, ← hk, extendCubeMap_castLE,
      insertChamberMap_apply_castSucc, chamberOldCoordinates_cubeRestriction, hk',
      extendCubeMap_castLE]
  · by_cases hji : j = chamberCutIndex h
    · subst j
      rw [Function.update_self]
      change extendCubeMap h (insertChamberMap e r chart) u (Fin.castLE h (Fin.last m)) = _
      rw [extendCubeMap_castLE, insertChamberMap_apply_last,
        chamberOldCoordinates_cubeRestriction]
      rfl
    · have hjval : j.val ≠ m := fun he => hji (Fin.ext he)
      have hmj : m + 1 ≤ j.val := by omega
      rw [extendCubeMap_outside h _ u j hmj, Function.update_of_ne hji,
        extendCubeMap_outside (Nat.le_of_succ_le h) _ u j (Nat.le_of_succ_le hmj)]

/-- The ascending cut sequence pulled back to the actual ambient cube. -/
def extendedChamberCutSequence (h : m + 1 ≤ n) (e : Equiv.Perm (Fin m))
    (chart : NativeChamberChart e) : Fin (m + 2) → C(NativeCube (Fin n), I) :=
  fun j => (chamberCutSequence e chart j).comp (cubeRestriction (Nat.le_of_succ_le h))

@[simp] theorem extendedChamberCutSequence_zero (h : m + 1 ≤ n) (e : Equiv.Perm (Fin m))
    (chart : NativeChamberChart e) (u : NativeCube (Fin n)) :
    extendedChamberCutSequence h e chart 0 u = 0 := rfl

@[simp] theorem extendedChamberCutSequence_last (h : m + 1 ≤ n) (e : Equiv.Perm (Fin m))
    (chart : NativeChamberChart e) (u : NativeCube (Fin n)) :
    extendedChamberCutSequence h e chart (Fin.last (m + 1)) u = 1 :=
  chamberCutSequence_last e chart _

theorem extendedChamberCutSequence_castSucc (h : m + 1 ≤ n) (e : Equiv.Perm (Fin m))
    (chart : NativeChamberChart e) (j : Fin (m + 1)) (u : NativeCube (Fin n)) :
    extendedChamberCutSequence h e chart j.castSucc u =
      chamberLower e j.rev chart (cubeRestriction (Nat.le_of_succ_le h) u) :=
  chamberCutSequence_castSucc e chart j _

theorem extendedChamberCutSequence_succ (h : m + 1 ≤ n) (e : Equiv.Perm (Fin m))
    (chart : NativeChamberChart e) (j : Fin (m + 1)) (u : NativeCube (Fin n)) :
    extendedChamberCutSequence h e chart j.succ u =
      chamberUpper e j.rev chart (cubeRestriction (Nat.le_of_succ_le h) u) :=
  chamberCutSequence_succ e chart j _

end Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision
