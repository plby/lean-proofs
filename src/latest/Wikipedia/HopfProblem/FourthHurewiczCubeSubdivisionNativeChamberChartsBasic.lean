import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeBasic
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativePermutationInsertion

/-!
# Coordinate insertion for native chamber parametrizations

A chamber chart remembers which affine face contains the image of each
boundary face of its source cube. These face conditions are preserved when
one coordinate is inserted between two consecutive ordered coordinates.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision

variable {n : ℕ}

/-- The boundary-face conditions of an ordered chamber parametrization. -/
structure NativeChamberChart (e : Equiv.Perm (Fin n)) where
  toContinuousMap : C(NativeCube (Fin n), NativeCube (Fin n))
  zero_last : ∀ u i, i.val + 1 = n → u (e i) = 0 → toContinuousMap u (e i) = 0
  zero_adjacent : ∀ u i j, i.val + 1 = j.val → u (e i) = 0 →
    toContinuousMap u (e i) = toContinuousMap u (e j)
  one_first : ∀ u i, i.val = 0 → u (e i) = 1 → toContinuousMap u (e i) = 1
  one_adjacent : ∀ u i j, j.val + 1 = i.val → u (e i) = 1 →
    toContinuousMap u (e i) = toContinuousMap u (e j)

/-- The lower endpoint for a new coordinate inserted at rank `r`. -/
def chamberLower (e : Equiv.Perm (Fin n)) (r : Fin (n + 1))
    (chart : NativeChamberChart e) : C(NativeCube (Fin n), I) :=
  if h : r.val < n then
    (ContinuousMap.eval (e ⟨r.val, h⟩)).comp chart.toContinuousMap
  else ContinuousMap.const _ 0

/-- The upper endpoint for a new coordinate inserted at rank `r`. -/
def chamberUpper (e : Equiv.Perm (Fin n)) (r : Fin (n + 1))
    (chart : NativeChamberChart e) : C(NativeCube (Fin n), I) :=
  if h : 0 < r.val then
    (ContinuousMap.eval (e ⟨r.val - 1, by omega⟩)).comp chart.toContinuousMap
  else ContinuousMap.const _ 1

theorem chamberLower_of_rank (e : Equiv.Perm (Fin n)) (r : Fin (n + 1))
    (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (k : Fin n)
    (h : r.val = k.val) : chamberLower e r chart u = chart.toContinuousMap u (e k) := by
  have hr : r.val < n := h ▸ k.isLt
  have hk : (⟨r.val, hr⟩ : Fin n) = k := Fin.ext h
  simp [chamberLower, hr, hk]

theorem chamberLower_last (e : Equiv.Perm (Fin n)) (r : Fin (n + 1))
    (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (h : r.val = n) :
    chamberLower e r chart u = 0 := by
  simp [chamberLower, h]

theorem chamberUpper_of_rank (e : Equiv.Perm (Fin n)) (r : Fin (n + 1))
    (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (k : Fin n)
    (h : r.val = k.val + 1) : chamberUpper e r chart u = chart.toContinuousMap u (e k) := by
  have hr : 0 < r.val := by omega
  have hk : (⟨r.val - 1, by omega⟩ : Fin n) = k := Fin.ext (by dsimp; omega)
  simp [chamberUpper, hr, hk]

theorem chamberUpper_first (e : Equiv.Perm (Fin n)) (r : Fin (n + 1))
    (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (h : r.val = 0) :
    chamberUpper e r chart u = 1 := by
  simp [chamberUpper, h]

/-- On the zero face immediately above the new coordinate, its lower endpoint
agrees with the old coordinate as well. -/
theorem chamberLower_zero_face (e : Equiv.Perm (Fin n)) (r : Fin (n + 1))
    (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (k : Fin n)
    (h : r.val = k.val + 1) (hu : u (e k) = 0) :
    chamberLower e r chart u = chart.toContinuousMap u (e k) := by
  by_cases hr : r.val < n
  · let j : Fin n := ⟨r.val, hr⟩
    rw [chamberLower_of_rank e r chart u j rfl]
    exact (chart.zero_adjacent u k j (by simpa [j] using h.symm) hu).symm
  · have hn : r.val = n := by omega
    rw [chamberLower_last e r chart u hn]
    exact (chart.zero_last u k (by omega) hu).symm

/-- On the one face immediately below the new coordinate, its upper endpoint
agrees with the old coordinate as well. -/
theorem chamberUpper_one_face (e : Equiv.Perm (Fin n)) (r : Fin (n + 1))
    (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (k : Fin n)
    (h : r.val = k.val) (hu : u (e k) = 1) :
    chamberUpper e r chart u = chart.toContinuousMap u (e k) := by
  by_cases hr : 0 < r.val
  · let j : Fin n := ⟨r.val - 1, by omega⟩
    rw [chamberUpper_of_rank e r chart u j (by dsimp [j]; omega)]
    exact (chart.one_adjacent u k j (by dsimp [j]; omega) hu).symm
  · have hz : r.val = 0 := by omega
    rw [chamberUpper_first e r chart u hz]
    exact (chart.one_first u k (by omega) hu).symm

/-- Restrict a cube point to its old coordinates. -/
def chamberOldCoordinates : C(NativeCube (Fin (n + 1)), NativeCube (Fin n)) where
  toFun u k := u k.castSucc
  continuous_toFun := continuous_pi fun _ => continuous_apply _

@[simp] theorem chamberOldCoordinates_apply (u : NativeCube (Fin (n + 1))) (k : Fin n) :
    chamberOldCoordinates u k = u k.castSucc := rfl

/-- Keep the old chart coordinates and interpolate the newly inserted one. -/
def insertChamberMap (e : Equiv.Perm (Fin n)) (r : Fin (n + 1))
    (chart : NativeChamberChart e) :
    C(NativeCube (Fin (n + 1)), NativeCube (Fin (n + 1))) where
  toFun u := Fin.lastCases
    (Set.Icc.convexComb (chamberLower e r chart (chamberOldCoordinates u))
      (chamberUpper e r chart (chamberOldCoordinates u)) (u (Fin.last n)))
    (chart.toContinuousMap (chamberOldCoordinates u))
  continuous_toFun := by
    apply continuous_pi
    intro k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simp only [Fin.lastCases_last]
      exact Set.Icc.continuous_convexComb_prod.comp
        (((chamberLower e r chart).continuous.comp chamberOldCoordinates.continuous).prodMk
          (((chamberUpper e r chart).continuous.comp chamberOldCoordinates.continuous).prodMk
            (continuous_apply (Fin.last n))))
    · simp only [Fin.lastCases_castSucc]
      exact (continuous_apply j).comp
        (chart.toContinuousMap.continuous.comp chamberOldCoordinates.continuous)

@[simp] theorem insertChamberMap_apply_castSucc (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin (n + 1))) (k : Fin n) :
    insertChamberMap e r chart u k.castSucc =
      chart.toContinuousMap (chamberOldCoordinates u) k := by
  simp [insertChamberMap]

@[simp] theorem insertChamberMap_apply_last (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin (n + 1))) :
    insertChamberMap e r chart u (Fin.last n) =
      Set.Icc.convexComb (chamberLower e r chart (chamberOldCoordinates u))
        (chamberUpper e r chart (chamberOldCoordinates u)) (u (Fin.last n)) := by
  simp [insertChamberMap]

@[simp] theorem insertChamberMap_apply_at (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin (n + 1))) :
    insertChamberMap e r chart u (insertPermutation e r r) =
      Set.Icc.convexComb (chamberLower e r chart (chamberOldCoordinates u))
        (chamberUpper e r chart (chamberOldCoordinates u)) (u (Fin.last n)) := by
  simp

@[simp] theorem insertChamberMap_apply_succAbove (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin (n + 1))) (k : Fin n) :
    insertChamberMap e r chart u (insertPermutation e r (r.succAbove k)) =
      chart.toContinuousMap (chamberOldCoordinates u) (e k) := by
  simp

/-- The two possible rank formulas after omitting the insertion rank. -/
theorem chamberSuccAbove_val_cases (r : Fin (n + 1)) (i : Fin n) :
    ((r.succAbove i).val = i.val ∧ i.val < r.val) ∨
      ((r.succAbove i).val = i.val + 1 ∧ r.val ≤ i.val) := by
  by_cases h : i.castSucc < r
  · exact Or.inl ⟨congrArg Fin.val (Fin.succAbove_of_castSucc_lt r i h), h⟩
  · exact Or.inr ⟨congrArg Fin.val (Fin.succAbove_of_le_castSucc r i (le_of_not_gt h)),
      le_of_not_gt h⟩

end Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision
